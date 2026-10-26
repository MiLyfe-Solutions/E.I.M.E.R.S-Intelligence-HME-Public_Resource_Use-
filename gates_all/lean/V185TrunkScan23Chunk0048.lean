import V185TrunkScan23Chunk0047

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_284035 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 1, 1, 4]
def baseStart_284035 : Nat := 118140960795 + 284035 * 2 ^ 59
def prefixEnd_284035 : Nat := 4983230072969 + 3 ^ 40 * 284035 * 2
def baseEnd_284035 : Nat := 145846477699901445456253

theorem tailTrace_284035 : CollatzResearch.WordTrace tailWord_284035 prefixEnd_284035 145846477699901445456253 := by
  unfold tailWord_284035
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359607525997179161085559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6906405017331452774057039 10359607525997179161085559)
  ·
    refine ⟨15539411288995768741628339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10359607525997179161085559 15539411288995768741628339)
    ·
      refine ⟨23309116933493653112442509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15539411288995768741628339 23309116933493653112442509)
      ·
        refine ⟨8740918850060119917165941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23309116933493653112442509 8740918850060119917165941)
        ·
          refine ⟨819461142193136242234307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8740918850060119917165941 819461142193136242234307)
          ·
            refine ⟨1229191713289704363351461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819461142193136242234307 1229191713289704363351461)
            ·
              refine ⟨230473446241819568128399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1229191713289704363351461 230473446241819568128399)
              ·
                refine ⟨345710169362729352192599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230473446241819568128399 345710169362729352192599)
                ·
                  refine ⟨518565254044094028288899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345710169362729352192599 518565254044094028288899)
                  ·
                    refine ⟨777847881066141042433349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 518565254044094028288899 777847881066141042433349)
                    ·
                      refine ⟨145846477699901445456253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 777847881066141042433349 145846477699901445456253)
                      ·
                        rfl

theorem cell23_284035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_284035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284035 prefixEnd_284035 := by exact prefixLift 284035
  have htrace : WordTrace (prefixWord ++ tailWord_284035) baseStart_284035 baseEnd_284035 := by
    simpa [prefixWord, tailWord_284035, baseEnd_284035] using wordTrace_append hprefix tailTrace_284035
  have hstable : (prefixWord ++ tailWord_284035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284035).length < 2 ^ (prefixWord ++ tailWord_284035).sum := by decide
  have hdescent : baseEnd_284035 < baseStart_284035 := by decide
  rcases family_descends (prefixWord ++ tailWord_284035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284041 : List Nat := [1, 2, 1, 1, 7, 1, 10]
def baseStart_284041 : Nat := 118140960795 + 284041 * 2 ^ 59
def prefixEnd_284041 : Nat := 4983230072969 + 3 ^ 40 * 284041 * 2
def baseEnd_284041 : Nat := 1800611834368252123225

theorem tailTrace_284041 : CollatzResearch.WordTrace tailWord_284041 prefixEnd_284041 1800611834368252123225 := by
  unfold tailWord_284041
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359826363975442185803977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6906550909316961457202651 10359826363975442185803977)
  ·
    refine ⟨7769869772981581639352983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10359826363975442185803977 7769869772981581639352983)
    ·
      refine ⟨11654804659472372459029475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7769869772981581639352983 11654804659472372459029475)
      ·
        refine ⟨17482206989208558688544213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11654804659472372459029475 17482206989208558688544213)
        ·
          refine ⟨409739226309575594262755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17482206989208558688544213 409739226309575594262755)
          ·
            refine ⟨614608839464363391394133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409739226309575594262755 614608839464363391394133)
            ·
              refine ⟨1800611834368252123225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 614608839464363391394133 1800611834368252123225)
              ·
                rfl

theorem cell23_284041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 10].length) (baseStart_284041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284041 prefixEnd_284041 := by exact prefixLift 284041
  have htrace : WordTrace (prefixWord ++ tailWord_284041) baseStart_284041 baseEnd_284041 := by
    simpa [prefixWord, tailWord_284041, baseEnd_284041] using wordTrace_append hprefix tailTrace_284041
  have hstable : (prefixWord ++ tailWord_284041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284041).length < 2 ^ (prefixWord ++ tailWord_284041).sum := by decide
  have hdescent : baseEnd_284041 < baseStart_284041 := by decide
  rcases family_descends (prefixWord ++ tailWord_284041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284052 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_284052 : Nat := 118140960795 + 284052 * 2 ^ 59
def prefixEnd_284052 : Nat := 4983230072969 + 3 ^ 40 * 284052 * 2
def baseEnd_284052 : Nat := 145855206871027878943675

theorem tailTrace_284052 : CollatzResearch.WordTrace tailWord_284052 prefixEnd_284052 145855206871027878943675 := by
  unfold tailWord_284052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180113783467795532227205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6906818377957060709636273 5180113783467795532227205)
  ·
    refine ⟨971271334400211662292601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5180113783467795532227205 971271334400211662292601)
    ·
      refine ⟨728453500800158746719451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 971271334400211662292601 728453500800158746719451)
      ·
        refine ⟨1092680251200238120079177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728453500800158746719451 1092680251200238120079177)
        ·
          refine ⟨819510188400178590059383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1092680251200238120079177 819510188400178590059383)
          ·
            refine ⟨1229265282600267885089075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819510188400178590059383 1229265282600267885089075)
            ·
              refine ⟨1843897923900401827633613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229265282600267885089075 1843897923900401827633613)
              ·
                refine ⟨691461721462650685362605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1843897923900401827633613 691461721462650685362605)
                ·
                  refine ⟨259298145548494007010977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691461721462650685362605 259298145548494007010977)
                  ·
                    refine ⟨194473609161370505258233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259298145548494007010977 194473609161370505258233)
                    ·
                      refine ⟨145855206871027878943675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194473609161370505258233 145855206871027878943675)
                      ·
                        rfl

theorem cell23_284052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_284052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284052 prefixEnd_284052 := by exact prefixLift 284052
  have htrace : WordTrace (prefixWord ++ tailWord_284052) baseStart_284052 baseEnd_284052 := by
    simpa [prefixWord, tailWord_284052, baseEnd_284052] using wordTrace_append hprefix tailTrace_284052
  have hstable : (prefixWord ++ tailWord_284052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284052).length < 2 ^ (prefixWord ++ tailWord_284052).sum := by decide
  have hdescent : baseEnd_284052 < baseStart_284052 := by decide
  rcases family_descends (prefixWord ++ tailWord_284052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284062 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_284062 : Nat := 118140960795 + 284062 * 2 ^ 59
def prefixEnd_284062 : Nat := 4983230072969 + 3 ^ 40 * 284062 * 2
def baseEnd_284062 : Nat := 48620113892524279939543

theorem tailTrace_284062 : CollatzResearch.WordTrace tailWord_284062 prefixEnd_284062 48620113892524279939543 := by
  unfold tailWord_284062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295074037112420346539805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6907061531266241848212293 1295074037112420346539805)
  ·
    refine ⟨485652763917157629952427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1295074037112420346539805 485652763917157629952427)
    ·
      refine ⟨728479145875736444928641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485652763917157629952427 728479145875736444928641)
      ·
        refine ⟨546359359406802333696481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728479145875736444928641 546359359406802333696481)
        ·
          refine ⟨409769519555101750272361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546359359406802333696481 409769519555101750272361)
          ·
            refine ⟨307327139666326312704271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409769519555101750272361 307327139666326312704271)
            ·
              refine ⟨460990709499489469056407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307327139666326312704271 460990709499489469056407)
              ·
                refine ⟨691486064249234203584611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460990709499489469056407 691486064249234203584611)
                ·
                  refine ⟨1037229096373851305376917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691486064249234203584611 1037229096373851305376917)
                  ·
                    refine ⟨48620113892524279939543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1037229096373851305376917 48620113892524279939543)
                    ·
                      rfl

theorem cell23_284062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_284062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284062 prefixEnd_284062 := by exact prefixLift 284062
  have htrace : WordTrace (prefixWord ++ tailWord_284062) baseStart_284062 baseEnd_284062 := by
    simpa [prefixWord, tailWord_284062, baseEnd_284062] using wordTrace_append hprefix tailTrace_284062
  have hstable : (prefixWord ++ tailWord_284062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284062).length < 2 ^ (prefixWord ++ tailWord_284062).sum := by decide
  have hdescent : baseEnd_284062 < baseStart_284062 := by decide
  rcases family_descends (prefixWord ++ tailWord_284062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284081 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_284081 : Nat := 118140960795 + 284081 * 2 ^ 59
def prefixEnd_284081 : Nat := 4983230072969 + 3 ^ 40 * 284081 * 2
def baseEnd_284081 : Nat := 145870097810008265481041

theorem tailTrace_284081 : CollatzResearch.WordTrace tailWord_284081 prefixEnd_284081 145870097810008265481041 := by
  unfold tailWord_284081
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361285283830529017260097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6907523522553686011506731 10361285283830529017260097)
  ·
    refine ⟨7770963962872896762945073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10361285283830529017260097 7770963962872896762945073)
    ·
      refine ⟨5828222972154672572208805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7770963962872896762945073 5828222972154672572208805)
      ·
        refine ⟨1092791807279001107289151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5828222972154672572208805 1092791807279001107289151)
        ·
          refine ⟨1639187710918501660933727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092791807279001107289151 1639187710918501660933727)
          ·
            refine ⟨2458781566377752491400591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639187710918501660933727 2458781566377752491400591)
            ·
              refine ⟨3688172349566628737100887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458781566377752491400591 3688172349566628737100887)
              ·
                refine ⟨5532258524349943105651331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688172349566628737100887 5532258524349943105651331)
                ·
                  refine ⟨8298387786524914658476997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532258524349943105651331 8298387786524914658476997)
                  ·
                    refine ⟨1555947709973421498464437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8298387786524914658476997 1555947709973421498464437)
                    ·
                      refine ⟨145870097810008265481041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1555947709973421498464437 145870097810008265481041)
                      ·
                        rfl

theorem cell23_284081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_284081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284081 prefixEnd_284081 := by exact prefixLift 284081
  have htrace : WordTrace (prefixWord ++ tailWord_284081) baseStart_284081 baseEnd_284081 := by
    simpa [prefixWord, tailWord_284081, baseEnd_284081] using wordTrace_append hprefix tailTrace_284081
  have hstable : (prefixWord ++ tailWord_284081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284081).length < 2 ^ (prefixWord ++ tailWord_284081).sum := by decide
  have hdescent : baseEnd_284081 < baseStart_284081 := by decide
  rcases family_descends (prefixWord ++ tailWord_284081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284085 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_284085 : Nat := 118140960795 + 284085 * 2 ^ 59
def prefixEnd_284085 : Nat := 4983230072969 + 3 ^ 40 * 284085 * 2
def baseEnd_284085 : Nat := 145872151732626249831023

theorem tailTrace_284085 : CollatzResearch.WordTrace tailWord_284085 prefixEnd_284085 145872151732626249831023 := by
  unfold tailWord_284085
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361431175816037700405709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6907620783877358466937139 10361431175816037700405709)
  ·
    refine ⟨3885536690931014137652141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10361431175816037700405709 3885536690931014137652141)
    ·
      refine ⟨1457076259099130301619553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3885536690931014137652141 1457076259099130301619553)
      ·
        refine ⟨1092807194324347726214665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1457076259099130301619553 1092807194324347726214665)
        ·
          refine ⟨819605395743260794660999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1092807194324347726214665 819605395743260794660999)
          ·
            refine ⟨1229408093614891191991499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819605395743260794660999 1229408093614891191991499)
            ·
              refine ⟨1844112140422336787987249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229408093614891191991499 1844112140422336787987249)
              ·
                refine ⟨1383084105316752590990437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844112140422336787987249 1383084105316752590990437)
                ·
                  refine ⟨259328269746891110810707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383084105316752590990437 259328269746891110810707)
                  ·
                    refine ⟨388992404620336666216061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259328269746891110810707 388992404620336666216061)
                    ·
                      refine ⟨145872151732626249831023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 388992404620336666216061 145872151732626249831023)
                      ·
                        rfl

theorem cell23_284085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_284085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284085 prefixEnd_284085 := by exact prefixLift 284085
  have htrace : WordTrace (prefixWord ++ tailWord_284085) baseStart_284085 baseEnd_284085 := by
    simpa [prefixWord, tailWord_284085, baseEnd_284085] using wordTrace_append hprefix tailTrace_284085
  have hstable : (prefixWord ++ tailWord_284085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284085).length < 2 ^ (prefixWord ++ tailWord_284085).sum := by decide
  have hdescent : baseEnd_284085 < baseStart_284085 := by decide
  rcases family_descends (prefixWord ++ tailWord_284085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284208 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 7, 4]
def baseStart_284208 : Nat := 118140960795 + 284208 * 2 ^ 59
def prefixEnd_284208 : Nat := 4983230072969 + 3 ^ 40 * 284208 * 2
def baseEnd_284208 : Nat := 48645103284376422864319

theorem tailTrace_284208 : CollatzResearch.WordTrace tailWord_284208 prefixEnd_284208 48645103284376422864319 := by
  unfold tailWord_284208
  simp only [CollatzResearch.WordTrace]
  refine ⟨5182958677185214853566639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6910611569580286471422185 5182958677185214853566639)
  ·
    refine ⟨7774438015777822280349959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5182958677185214853566639 7774438015777822280349959)
    ·
      refine ⟨11661657023666733420524939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774438015777822280349959 11661657023666733420524939)
      ·
        refine ⟨17492485535500100130787409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661657023666733420524939 17492485535500100130787409)
        ·
          refine ⟨13119364151625075098090557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17492485535500100130787409 13119364151625075098090557)
          ·
            refine ⟨4919761556859403161783959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13119364151625075098090557 4919761556859403161783959)
            ·
              refine ⟨7379642335289104742675939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919761556859403161783959 7379642335289104742675939)
              ·
                refine ⟨11069463502933657114013909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7379642335289104742675939 11069463502933657114013909)
                ·
                  refine ⟨259440550850007588609701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11069463502933657114013909 259440550850007588609701)
                  ·
                    refine ⟨48645103284376422864319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259440550850007588609701 48645103284376422864319)
                    ·
                      rfl

theorem cell23_284208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_284208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284208 prefixEnd_284208 := by exact prefixLift 284208
  have htrace : WordTrace (prefixWord ++ tailWord_284208) baseStart_284208 baseEnd_284208 := by
    simpa [prefixWord, tailWord_284208, baseEnd_284208] using wordTrace_append hprefix tailTrace_284208
  have hstable : (prefixWord ++ tailWord_284208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284208).length < 2 ^ (prefixWord ++ tailWord_284208).sum := by decide
  have hdescent : baseEnd_284208 < baseStart_284208 := by decide
  rcases family_descends (prefixWord ++ tailWord_284208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284215 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 2, 4, 2]
def baseStart_284215 : Nat := 118140960795 + 284215 * 2 ^ 59
def prefixEnd_284215 : Nat := 4983230072969 + 3 ^ 40 * 284215 * 2
def baseEnd_284215 : Nat := 145938904217710741205425

theorem tailTrace_284215 : CollatzResearch.WordTrace tailWord_284215 prefixEnd_284215 145938904217710741205425 := by
  unfold tailWord_284215
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366172665345069902638099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6910781776896713268425399 10366172665345069902638099)
  ·
    refine ⟨15549258998017604853957149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10366172665345069902638099 15549258998017604853957149)
    ·
      refine ⟨5830972124256601820233931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15549258998017604853957149 5830972124256601820233931)
      ·
        refine ⟨8746458186384902730350897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830972124256601820233931 8746458186384902730350897)
        ·
          refine ⟨6559843639788677047763173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8746458186384902730350897 6559843639788677047763173)
          ·
            refine ⟨1229970682460376946455595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6559843639788677047763173 1229970682460376946455595)
            ·
              refine ⟨1844956023690565419683393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229970682460376946455595 1844956023690565419683393)
              ·
                refine ⟨1383717017767924064762545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844956023690565419683393 1383717017767924064762545)
                ·
                  refine ⟨1037787763325943048571909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383717017767924064762545 1037787763325943048571909)
                  ·
                    refine ⟨194585205623614321607233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037787763325943048571909 194585205623614321607233)
                    ·
                      refine ⟨145938904217710741205425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194585205623614321607233 145938904217710741205425)
                      ·
                        rfl

theorem cell23_284215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_284215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284215 prefixEnd_284215 := by exact prefixLift 284215
  have htrace : WordTrace (prefixWord ++ tailWord_284215) baseStart_284215 baseEnd_284215 := by
    simpa [prefixWord, tailWord_284215, baseEnd_284215] using wordTrace_append hprefix tailTrace_284215
  have hstable : (prefixWord ++ tailWord_284215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284215).length < 2 ^ (prefixWord ++ tailWord_284215).sum := by decide
  have hdescent : baseEnd_284215 < baseStart_284215 := by decide
  rcases family_descends (prefixWord ++ tailWord_284215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284248 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_284248 : Nat := 118140960795 + 284248 * 2 ^ 59
def prefixEnd_284248 : Nat := 4983230072969 + 3 ^ 40 * 284248 * 2
def baseEnd_284248 : Nat := 145955849079309112092773

theorem tailTrace_284248 : CollatzResearch.WordTrace tailWord_284248 prefixEnd_284248 145955849079309112092773 := by
  unfold tailWord_284248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183688137112758269294699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6911584182817011025726265 5183688137112758269294699)
  ·
    refine ⟨7775532205669137403942049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5183688137112758269294699 7775532205669137403942049)
    ·
      refine ⟨5831649154251853052956537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7775532205669137403942049 5831649154251853052956537)
      ·
        refine ⟨4373736865688889789717403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5831649154251853052956537 4373736865688889789717403)
        ·
          refine ⟨6560605298533334684576105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373736865688889789717403 6560605298533334684576105)
          ·
            refine ⟨4920453973900001013432079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6560605298533334684576105 4920453973900001013432079)
            ·
              refine ⟨7380680960850001520148119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4920453973900001013432079 7380680960850001520148119)
              ·
                refine ⟨11071021441275002280222179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7380680960850001520148119 11071021441275002280222179)
                ·
                  refine ⟨16606532161912503420333269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11071021441275002280222179 16606532161912503420333269)
                  ·
                    refine ⟨389215597544824298914061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16606532161912503420333269 389215597544824298914061)
                    ·
                      refine ⟨145955849079309112092773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 389215597544824298914061 145955849079309112092773)
                      ·
                        rfl

theorem cell23_284248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_284248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284248 prefixEnd_284248 := by exact prefixLift 284248
  have htrace : WordTrace (prefixWord ++ tailWord_284248) baseStart_284248 baseEnd_284248 := by
    simpa [prefixWord, tailWord_284248, baseEnd_284248] using wordTrace_append hprefix tailTrace_284248
  have hstable : (prefixWord ++ tailWord_284248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284248).length < 2 ^ (prefixWord ++ tailWord_284248).sum := by decide
  have hdescent : baseEnd_284248 < baseStart_284248 := by decide
  rcases family_descends (prefixWord ++ tailWord_284248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284259 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 1, 4]
def baseStart_284259 : Nat := 118140960795 + 284259 * 2 ^ 59
def prefixEnd_284259 : Nat := 4983230072969 + 3 ^ 40 * 284259 * 2
def baseEnd_284259 : Nat := 48653832455502856351741

theorem tailTrace_284259 : CollatzResearch.WordTrace tailWord_284259 prefixEnd_284259 48653832455502856351741 := by
  unfold tailWord_284259
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367777477185665417239831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6911851651457110278159887 10367777477185665417239831)
  ·
    refine ⟨15551666215778498125859747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10367777477185665417239831 15551666215778498125859747)
    ·
      refine ⟨23327499323667747188789621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15551666215778498125859747 23327499323667747188789621)
      ·
        refine ⟨2186953061593851298949027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23327499323667747188789621 2186953061593851298949027)
        ·
          refine ⟨3280429592390776948423541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186953061593851298949027 3280429592390776948423541)
          ·
            refine ⟨307540274286635338914707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3280429592390776948423541 307540274286635338914707)
            ·
              refine ⟨461310411429953008372061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307540274286635338914707 461310411429953008372061)
              ·
                refine ⟨172991404286232378139523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461310411429953008372061 172991404286232378139523)
                ·
                  refine ⟨259487106429348567209285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172991404286232378139523 259487106429348567209285)
                  ·
                    refine ⟨48653832455502856351741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259487106429348567209285 48653832455502856351741)
                    ·
                      rfl

theorem cell23_284259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 4].length) (baseStart_284259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284259 prefixEnd_284259 := by exact prefixLift 284259
  have htrace : WordTrace (prefixWord ++ tailWord_284259) baseStart_284259 baseEnd_284259 := by
    simpa [prefixWord, tailWord_284259, baseEnd_284259] using wordTrace_append hprefix tailTrace_284259
  have hstable : (prefixWord ++ tailWord_284259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284259).length < 2 ^ (prefixWord ++ tailWord_284259).sum := by decide
  have hdescent : baseEnd_284259 < baseStart_284259 := by decide
  rcases family_descends (prefixWord ++ tailWord_284259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284265 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 3]
def baseStart_284265 : Nat := 118140960795 + 284265 * 2 ^ 59
def prefixEnd_284265 : Nat := 4983230072969 + 3 ^ 40 * 284265 * 2
def baseEnd_284265 : Nat := 145964578250435545580195

theorem tailTrace_284265 : CollatzResearch.WordTrace tailWord_284265 prefixEnd_284265 145964578250435545580195 := by
  unfold tailWord_284265
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367996315163928441958249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6911997543442618961305499 10367996315163928441958249)
  ·
    refine ⟨7775997236372946331468687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10367996315163928441958249 7775997236372946331468687)
    ·
      refine ⟨11663995854559419497203031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775997236372946331468687 11663995854559419497203031)
      ·
        refine ⟨17495993781839129245804547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11663995854559419497203031 17495993781839129245804547)
        ·
          refine ⟨26243990672758693868706821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17495993781839129245804547 26243990672758693868706821)
          ·
            refine ⟨4920748251142255100382529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26243990672758693868706821 4920748251142255100382529)
            ·
              refine ⟨3690561188356691325286897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4920748251142255100382529 3690561188356691325286897)
              ·
                refine ⟨2767920891267518493965173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690561188356691325286897 2767920891267518493965173)
                ·
                  refine ⟨259492583556329858809235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2767920891267518493965173 259492583556329858809235)
                  ·
                    refine ⟨389238875334494788213853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259492583556329858809235 389238875334494788213853)
                    ·
                      refine ⟨145964578250435545580195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 389238875334494788213853 145964578250435545580195)
                      ·
                        rfl

theorem cell23_284265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_284265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284265 prefixEnd_284265 := by exact prefixLift 284265
  have htrace : WordTrace (prefixWord ++ tailWord_284265) baseStart_284265 baseEnd_284265 := by
    simpa [prefixWord, tailWord_284265, baseEnd_284265] using wordTrace_append hprefix tailTrace_284265
  have hstable : (prefixWord ++ tailWord_284265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284265).length < 2 ^ (prefixWord ++ tailWord_284265).sum := by decide
  have hdescent : baseEnd_284265 < baseStart_284265 := by decide
  rcases family_descends (prefixWord ++ tailWord_284265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284268 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_284268 : Nat := 118140960795 + 284268 * 2 ^ 59
def prefixEnd_284268 : Nat := 4983230072969 + 3 ^ 40 * 284268 * 2
def baseEnd_284268 : Nat := 48655372897466344614227

theorem tailTrace_284268 : CollatzResearch.WordTrace tailWord_284268 prefixEnd_284268 48655372897466344614227 := by
  unfold tailWord_284268
  simp only [CollatzResearch.WordTrace]
  refine ⟨5184052867076529977158729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6912070489435373302878305 5184052867076529977158729)
  ·
    refine ⟨3888039650307397482869047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5184052867076529977158729 3888039650307397482869047)
    ·
      refine ⟨5832059475461096224303571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888039650307397482869047 5832059475461096224303571)
      ·
        refine ⟨8748089213191644336455357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5832059475461096224303571 8748089213191644336455357)
        ·
          refine ⟨3280533454946866626170759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8748089213191644336455357 3280533454946866626170759)
          ·
            refine ⟨4920800182420299939256139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280533454946866626170759 4920800182420299939256139)
            ·
              refine ⟨7381200273630449908884209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4920800182420299939256139 7381200273630449908884209)
              ·
                refine ⟨5535900205222837431663157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7381200273630449908884209 5535900205222837431663157)
                ·
                  refine ⟨518990644239641009218421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5535900205222837431663157 518990644239641009218421)
                  ·
                    refine ⟨48655372897466344614227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 518990644239641009218421 48655372897466344614227)
                    ·
                      rfl

theorem cell23_284268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_284268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284268 prefixEnd_284268 := by exact prefixLift 284268
  have htrace : WordTrace (prefixWord ++ tailWord_284268) baseStart_284268 baseEnd_284268 := by
    simpa [prefixWord, tailWord_284268, baseEnd_284268] using wordTrace_append hprefix tailTrace_284268
  have hstable : (prefixWord ++ tailWord_284268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284268).length < 2 ^ (prefixWord ++ tailWord_284268).sum := by decide
  have hdescent : baseEnd_284268 < baseStart_284268 := by decide
  rcases family_descends (prefixWord ++ tailWord_284268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284302 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_284302 : Nat := 118140960795 + 284302 * 2 ^ 59
def prefixEnd_284302 : Nat := 4983230072969 + 3 ^ 40 * 284302 * 2
def baseEnd_284302 : Nat := 48661192344883966939175

theorem tailTrace_284302 : CollatzResearch.WordTrace tailWord_284302 prefixEnd_284302 48661192344883966939175 := by
  unfold tailWord_284302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296168227003735470131895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6912897210686589174036773 1296168227003735470131895)
  ·
    refine ⟨1944252340505603205197843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1296168227003735470131895 1944252340505603205197843)
    ·
      refine ⟨2916378510758404807796765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944252340505603205197843 2916378510758404807796765)
      ·
        refine ⟨1093641941534401802923787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2916378510758404807796765 1093641941534401802923787)
        ·
          refine ⟨1640462912301602704385681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093641941534401802923787 1640462912301602704385681)
          ·
            refine ⟨1230347184226202028289261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1640462912301602704385681 1230347184226202028289261)
            ·
              refine ⟨461380194084825760608473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230347184226202028289261 461380194084825760608473)
              ·
                refine ⟨346035145563619320456355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461380194084825760608473 346035145563619320456355)
                ·
                  refine ⟨519052718345428980684533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346035145563619320456355 519052718345428980684533)
                  ·
                    refine ⟨48661192344883966939175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 519052718345428980684533 48661192344883966939175)
                    ·
                      rfl

theorem cell23_284302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_284302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284302 prefixEnd_284302 := by exact prefixLift 284302
  have htrace : WordTrace (prefixWord ++ tailWord_284302) baseStart_284302 baseEnd_284302 := by
    simpa [prefixWord, tailWord_284302, baseEnd_284302] using wordTrace_append hprefix tailTrace_284302
  have hstable : (prefixWord ++ tailWord_284302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284302).length < 2 ^ (prefixWord ++ tailWord_284302).sum := by decide
  have hdescent : baseEnd_284302 < baseStart_284302 := by decide
  rcases family_descends (prefixWord ++ tailWord_284302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284305 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_284305 : Nat := 118140960795 + 284305 * 2 ^ 59
def prefixEnd_284305 : Nat := 4983230072969 + 3 ^ 40 * 284305 * 2
def baseEnd_284305 : Nat := 145985117476615389080011

theorem tailTrace_284305 : CollatzResearch.WordTrace tailWord_284305 prefixEnd_284305 145985117476615389080011 := by
  unfold tailWord_284305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369455235019015273414369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6912970156679343515609579 10369455235019015273414369)
  ·
    refine ⟨7777091426264261455060777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10369455235019015273414369 7777091426264261455060777)
    ·
      refine ⟨5832818569698196091295583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7777091426264261455060777 5832818569698196091295583)
      ·
        refine ⟨8749227854547294136943375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5832818569698196091295583 8749227854547294136943375)
        ·
          refine ⟨13123841781820941205415063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8749227854547294136943375 13123841781820941205415063)
          ·
            refine ⟨19685762672731411808122595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13123841781820941205415063 19685762672731411808122595)
            ·
              refine ⟨29528644009097117712183893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19685762672731411808122595 29528644009097117712183893)
              ·
                refine ⟨346038796981606848189655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 29528644009097117712183893 346038796981606848189655)
                ·
                  refine ⟨519058195472410272284483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346038796981606848189655 519058195472410272284483)
                  ·
                    refine ⟨778587293208615408426725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 519058195472410272284483 778587293208615408426725)
                    ·
                      refine ⟨145985117476615389080011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 778587293208615408426725 145985117476615389080011)
                      ·
                        rfl

theorem cell23_284305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_284305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284305 prefixEnd_284305 := by exact prefixLift 284305
  have htrace : WordTrace (prefixWord ++ tailWord_284305) baseStart_284305 baseEnd_284305 := by
    simpa [prefixWord, tailWord_284305, baseEnd_284305] using wordTrace_append hprefix tailTrace_284305
  have hstable : (prefixWord ++ tailWord_284305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284305).length < 2 ^ (prefixWord ++ tailWord_284305).sum := by decide
  have hdescent : baseEnd_284305 < baseStart_284305 := by decide
  rcases family_descends (prefixWord ++ tailWord_284305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284325 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_284325 : Nat := 118140960795 + 284325 * 2 ^ 59
def prefixEnd_284325 : Nat := 4983230072969 + 3 ^ 40 * 284325 * 2
def baseEnd_284325 : Nat := 145995387089705310829919

theorem tailTrace_284325 : CollatzResearch.WordTrace tailWord_284325 prefixEnd_284325 145995387089705310829919 := by
  unfold tailWord_284325
  simp only [CollatzResearch.WordTrace]
  refine ⟨10370184694946558689142429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6913456463297705792761619 10370184694946558689142429)
  ·
    refine ⟨3888819260604959508428411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10370184694946558689142429 3888819260604959508428411)
    ·
      refine ⟨5833228890907439262642617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888819260604959508428411 5833228890907439262642617)
      ·
        refine ⟨4374921668180579446981963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5833228890907439262642617 4374921668180579446981963)
        ·
          refine ⟨6562382502270869170472945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374921668180579446981963 6562382502270869170472945)
          ·
            refine ⟨4921786876703151877854709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6562382502270869170472945 4921786876703151877854709)
            ·
              refine ⟨461417519690920488548879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4921786876703151877854709 461417519690920488548879)
              ·
                refine ⟨692126279536380732823319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461417519690920488548879 692126279536380732823319)
                ·
                  refine ⟨1038189419304571099234979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692126279536380732823319 1038189419304571099234979)
                  ·
                    refine ⟨1557284128956856648852469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1038189419304571099234979 1557284128956856648852469)
                    ·
                      refine ⟨145995387089705310829919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1557284128956856648852469 145995387089705310829919)
                      ·
                        rfl

theorem cell23_284325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_284325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284325 prefixEnd_284325 := by exact prefixLift 284325
  have htrace : WordTrace (prefixWord ++ tailWord_284325) baseStart_284325 baseEnd_284325 := by
    simpa [prefixWord, tailWord_284325, baseEnd_284325] using wordTrace_append hprefix tailTrace_284325
  have hstable : (prefixWord ++ tailWord_284325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284325).length < 2 ^ (prefixWord ++ tailWord_284325).sum := by decide
  have hdescent : baseEnd_284325 < baseStart_284325 := by decide
  rcases family_descends (prefixWord ++ tailWord_284325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284362 : List Nat := [3, 1, 2, 1, 5, 1, 3, 7]
def baseStart_284362 : Nat := 118140960795 + 284362 * 2 ^ 59
def prefixEnd_284362 : Nat := 4983230072969 + 3 ^ 40 * 284362 * 2
def baseEnd_284362 : Nat := 5407940217552654298787

theorem tailTrace_284362 : CollatzResearch.WordTrace tailWord_284362 prefixEnd_284362 5407940217552654298787 := by
  unfold tailWord_284362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592883548953128502059835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6914356130541676005492893 2592883548953128502059835)
  ·
    refine ⟨3889325323429692753089753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2592883548953128502059835 3889325323429692753089753)
    ·
      refine ⟨2916993992572269564817315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3889325323429692753089753 2916993992572269564817315)
      ·
        refine ⟨4375490988858404347225973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916993992572269564817315 4375490988858404347225973)
        ·
          refine ⟨410202280205475407552435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4375490988858404347225973 410202280205475407552435)
          ·
            refine ⟨615303420308213111328653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410202280205475407552435 615303420308213111328653)
            ·
              refine ⟨230738782615579916748245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 615303420308213111328653 230738782615579916748245)
              ·
                refine ⟨5407940217552654298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 230738782615579916748245 5407940217552654298787)
                ·
                  rfl

theorem cell23_284362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_284362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284362 prefixEnd_284362 := by exact prefixLift 284362
  have htrace : WordTrace (prefixWord ++ tailWord_284362) baseStart_284362 baseEnd_284362 := by
    simpa [prefixWord, tailWord_284362, baseEnd_284362] using wordTrace_append hprefix tailTrace_284362
  have hstable : (prefixWord ++ tailWord_284362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284362).length < 2 ^ (prefixWord ++ tailWord_284362).sum := by decide
  have hdescent : baseEnd_284362 < baseStart_284362 := by decide
  rcases family_descends (prefixWord ++ tailWord_284362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284415 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_284415 : Nat := 118140960795 + 284415 * 2 ^ 59
def prefixEnd_284415 : Nat := 4983230072969 + 3 ^ 40 * 284415 * 2
def baseEnd_284415 : Nat := 146041600348609958704505

theorem tailTrace_284415 : CollatzResearch.WordTrace tailWord_284415 prefixEnd_284415 146041600348609958704505 := by
  unfold tailWord_284415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10373467264620504059918699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6915644843080336039945799 10373467264620504059918699)
  ·
    refine ⟨15560200896930756089878049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10373467264620504059918699 15560200896930756089878049)
    ·
      refine ⟨11670150672698067067408537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15560200896930756089878049 11670150672698067067408537)
      ·
        refine ⟨8752613004523550300556403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11670150672698067067408537 8752613004523550300556403)
        ·
          refine ⟨13128919506785325450834605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8752613004523550300556403 13128919506785325450834605)
          ·
            refine ⟨4923344815044497044062977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13128919506785325450834605 4923344815044497044062977)
            ·
              refine ⟨3692508611283372783047233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4923344815044497044062977 3692508611283372783047233)
              ·
                refine ⟨2769381458462529587285425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3692508611283372783047233 2769381458462529587285425)
                ·
                  refine ⟨2077036093846897190464069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2769381458462529587285425 2077036093846897190464069)
                  ·
                    refine ⟨389444267596293223212013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2077036093846897190464069 389444267596293223212013)
                    ·
                      refine ⟨146041600348609958704505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 389444267596293223212013 146041600348609958704505)
                      ·
                        rfl

theorem cell23_284415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_284415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284415 prefixEnd_284415 := by exact prefixLift 284415
  have htrace : WordTrace (prefixWord ++ tailWord_284415) baseStart_284415 baseEnd_284415 := by
    simpa [prefixWord, tailWord_284415, baseEnd_284415] using wordTrace_append hprefix tailTrace_284415
  have hstable : (prefixWord ++ tailWord_284415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284415).length < 2 ^ (prefixWord ++ tailWord_284415).sum := by decide
  have hdescent : baseEnd_284415 < baseStart_284415 := by decide
  rcases family_descends (prefixWord ++ tailWord_284415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284452 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 7]
def baseStart_284452 : Nat := 118140960795 + 284452 * 2 ^ 59
def prefixEnd_284452 : Nat := 4983230072969 + 3 ^ 40 * 284452 * 2
def baseEnd_284452 : Nat := 16228955459202923771315

theorem tailTrace_284452 : CollatzResearch.WordTrace tailWord_284452 prefixEnd_284452 16228955459202923771315 := by
  unfold tailWord_284452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187408382743229689507805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6916544510324306252677073 5187408382743229689507805)
  ·
    refine ⟨1945278143528711133565427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5187408382743229689507805 1945278143528711133565427)
    ·
      refine ⟨2917917215293066700348141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1945278143528711133565427 2917917215293066700348141)
      ·
        refine ⟨1094218955734900012630553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2917917215293066700348141 1094218955734900012630553)
        ·
          refine ⟨820664216801175009472915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094218955734900012630553 820664216801175009472915)
          ·
            refine ⟨1230996325201762514209373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820664216801175009472915 1230996325201762514209373)
            ·
              refine ⟨461623621950660942828515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230996325201762514209373 461623621950660942828515)
              ·
                refine ⟨692435432925991414242773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461623621950660942828515 692435432925991414242773)
                ·
                  refine ⟨16228955459202923771315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 692435432925991414242773 16228955459202923771315)
                  ·
                    rfl

theorem cell23_284452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_284452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284452 prefixEnd_284452 := by exact prefixLift 284452
  have htrace : WordTrace (prefixWord ++ tailWord_284452) baseStart_284452 baseEnd_284452 := by
    simpa [prefixWord, tailWord_284452, baseEnd_284452] using wordTrace_append hprefix tailTrace_284452
  have hstable : (prefixWord ++ tailWord_284452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284452).length < 2 ^ (prefixWord ++ tailWord_284452).sum := by decide
  have hdescent : baseEnd_284452 < baseStart_284452 := by decide
  rcases family_descends (prefixWord ++ tailWord_284452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284503 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 5]
def baseStart_284503 : Nat := 118140960795 + 284503 * 2 ^ 59
def prefixEnd_284503 : Nat := 4983230072969 + 3 ^ 40 * 284503 * 2
def baseEnd_284503 : Nat := 16231865182911734933789

theorem tailTrace_284503 : CollatzResearch.WordTrace tailWord_284503 prefixEnd_284503 16231865182911734933789 := by
  unfold tailWord_284503
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376676888301695089122163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6917784592201130059414775 10376676888301695089122163)
  ·
    refine ⟨15565015332452542633683245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10376676888301695089122163 15565015332452542633683245)
    ·
      refine ⟨5836880749669703487631217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15565015332452542633683245 5836880749669703487631217)
      ·
        refine ⟨4377660562252277615723413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5836880749669703487631217 4377660562252277615723413)
        ·
          refine ⟨205202838855575513237035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4377660562252277615723413 205202838855575513237035)
          ·
            refine ⟨307804258283363269855553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205202838855575513237035 307804258283363269855553)
            ·
              refine ⟨230853193712522452391665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307804258283363269855553 230853193712522452391665)
              ·
                refine ⟨173139895284391839293749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230853193712522452391665 173139895284391839293749)
                ·
                  refine ⟨16231865182911734933789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173139895284391839293749 16231865182911734933789)
                  ·
                    rfl

theorem cell23_284503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 5].length) (baseStart_284503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284503 prefixEnd_284503 := by exact prefixLift 284503
  have htrace : WordTrace (prefixWord ++ tailWord_284503) baseStart_284503 baseEnd_284503 := by
    simpa [prefixWord, tailWord_284503, baseEnd_284503] using wordTrace_append hprefix tailTrace_284503
  have hstable : (prefixWord ++ tailWord_284503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284503).length < 2 ^ (prefixWord ++ tailWord_284503).sum := by decide
  have hdescent : baseEnd_284503 < baseStart_284503 := by decide
  rcases family_descends (prefixWord ++ tailWord_284503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284505 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_284505 : Nat := 118140960795 + 284505 * 2 ^ 59
def prefixEnd_284505 : Nat := 4983230072969 + 3 ^ 40 * 284505 * 2
def baseEnd_284505 : Nat := 146087813607514606579091

theorem tailTrace_284505 : CollatzResearch.WordTrace tailWord_284505 prefixEnd_284505 146087813607514606579091 := by
  unfold tailWord_284505
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376749834294449430694969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6917833222862966287129979 10376749834294449430694969)
  ·
    refine ⟨7782562375720837073021227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10376749834294449430694969 7782562375720837073021227)
    ·
      refine ⟨11673843563581255609531841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7782562375720837073021227 11673843563581255609531841)
      ·
        refine ⟨8755382672685941707148881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11673843563581255609531841 8755382672685941707148881)
        ·
          refine ⟨6566537004514456280361661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8755382672685941707148881 6566537004514456280361661)
          ·
            refine ⟨2462451376692921105135623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6566537004514456280361661 2462451376692921105135623)
            ·
              refine ⟨3693677065039381657703435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462451376692921105135623 3693677065039381657703435)
              ·
                refine ⟨5540515597559072486555153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693677065039381657703435 5540515597559072486555153)
                ·
                  refine ⟨4155386698169304364916365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540515597559072486555153 4155386698169304364916365)
                  ·
                    refine ⟨1558270011813489136843637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4155386698169304364916365 1558270011813489136843637)
                    ·
                      refine ⟨146087813607514606579091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1558270011813489136843637 146087813607514606579091)
                      ·
                        rfl

theorem cell23_284505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_284505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284505 prefixEnd_284505 := by exact prefixLift 284505
  have htrace : WordTrace (prefixWord ++ tailWord_284505) baseStart_284505 baseEnd_284505 := by
    simpa [prefixWord, tailWord_284505, baseEnd_284505] using wordTrace_append hprefix tailTrace_284505
  have hstable : (prefixWord ++ tailWord_284505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284505).length < 2 ^ (prefixWord ++ tailWord_284505).sum := by decide
  have hdescent : baseEnd_284505 < baseStart_284505 := by decide
  rcases family_descends (prefixWord ++ tailWord_284505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284519 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_284519 : Nat := 118140960795 + 284519 * 2 ^ 59
def prefixEnd_284519 : Nat := 4983230072969 + 3 ^ 40 * 284519 * 2
def baseEnd_284519 : Nat := 146095002336677551804027

theorem tailTrace_284519 : CollatzResearch.WordTrace tailWord_284519 prefixEnd_284519 146095002336677551804027 := by
  unfold tailWord_284519
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377260456243729821704611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6918173637495819881136407 10377260456243729821704611)
  ·
    refine ⟨15565890684365594732556917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10377260456243729821704611 15565890684365594732556917)
    ·
      refine ⟨1459302251659274506177211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15565890684365594732556917 1459302251659274506177211)
      ·
        refine ⟨2188953377488911759265817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459302251659274506177211 2188953377488911759265817)
        ·
          refine ⟨1641715033116683819449363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188953377488911759265817 1641715033116683819449363)
          ·
            refine ⟨2462572549675025729174045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641715033116683819449363 2462572549675025729174045)
            ·
              refine ⟨923464706128134648440267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2462572549675025729174045 923464706128134648440267)
              ·
                refine ⟨1385197059192201972660401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923464706128134648440267 1385197059192201972660401)
                ·
                  refine ⟨1038897794394151479495301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1385197059192201972660401 1038897794394151479495301)
                  ·
                    refine ⟨194793336448903402405369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038897794394151479495301 194793336448903402405369)
                    ·
                      refine ⟨146095002336677551804027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194793336448903402405369 146095002336677551804027)
                      ·
                        rfl

theorem cell23_284519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_284519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284519 prefixEnd_284519 := by exact prefixLift 284519
  have htrace : WordTrace (prefixWord ++ tailWord_284519) baseStart_284519 baseEnd_284519 := by
    simpa [prefixWord, tailWord_284519, baseEnd_284519] using wordTrace_append hprefix tailTrace_284519
  have hstable : (prefixWord ++ tailWord_284519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284519).length < 2 ^ (prefixWord ++ tailWord_284519).sum := by decide
  have hdescent : baseEnd_284519 < baseStart_284519 := by decide
  rcases family_descends (prefixWord ++ tailWord_284519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284569 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 3]
def baseStart_284569 : Nat := 118140960795 + 284569 * 2 ^ 59
def prefixEnd_284569 : Nat := 4983230072969 + 3 ^ 40 * 284569 * 2
def baseEnd_284569 : Nat := 146120676369402356178797

theorem tailTrace_284569 : CollatzResearch.WordTrace tailWord_284569 prefixEnd_284569 146120676369402356178797 := by
  unfold tailWord_284569
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379084106062588361024761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6919389404041725574016507 10379084106062588361024761)
  ·
    refine ⟨7784313079546941270768571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10379084106062588361024761 7784313079546941270768571)
    ·
      refine ⟨11676469619320411906152857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7784313079546941270768571 11676469619320411906152857)
      ·
        refine ⟨8757352214490308929614643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11676469619320411906152857 8757352214490308929614643)
        ·
          refine ⟨13136028321735463394421965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8757352214490308929614643 13136028321735463394421965)
          ·
            refine ⟨4926010620650798772908237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13136028321735463394421965 4926010620650798772908237)
            ·
              refine ⟨1847253982744049539840589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4926010620650798772908237 1847253982744049539840589)
              ·
                refine ⟨692720243529018577440221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1847253982744049539840589 692720243529018577440221)
                ·
                  refine ⟨259770091323381966540083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692720243529018577440221 259770091323381966540083)
                  ·
                    refine ⟨389655136985072949810125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259770091323381966540083 389655136985072949810125)
                    ·
                      refine ⟨146120676369402356178797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 389655136985072949810125 146120676369402356178797)
                      ·
                        rfl

theorem cell23_284569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_284569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284569 prefixEnd_284569 := by exact prefixLift 284569
  have htrace : WordTrace (prefixWord ++ tailWord_284569) baseStart_284569 baseEnd_284569 := by
    simpa [prefixWord, tailWord_284569, baseEnd_284569] using wordTrace_append hprefix tailTrace_284569
  have hstable : (prefixWord ++ tailWord_284569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284569).length < 2 ^ (prefixWord ++ tailWord_284569).sum := by decide
  have hdescent : baseEnd_284569 < baseStart_284569 := by decide
  rcases family_descends (prefixWord ++ tailWord_284569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284619 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 2, 4]
def baseStart_284619 : Nat := 118140960795 + 284619 * 2 ^ 59
def prefixEnd_284619 : Nat := 4983230072969 + 3 ^ 40 * 284619 * 2
def baseEnd_284619 : Nat := 48715450134042386851189

theorem tailTrace_284619 : CollatzResearch.WordTrace tailWord_284619 prefixEnd_284619 48715450134042386851189 := by
  unfold tailWord_284619
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380907755881446900344911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6920605170587631266896607 10380907755881446900344911)
  ·
    refine ⟨15571361633822170350517367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10380907755881446900344911 15571361633822170350517367)
    ·
      refine ⟨23357042450733255525776051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15571361633822170350517367 23357042450733255525776051)
      ·
        refine ⟨35035563676099883288664077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23357042450733255525776051 35035563676099883288664077)
        ·
          refine ⟨13138336378537456233249029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35035563676099883288664077 13138336378537456233249029)
          ·
            refine ⟨2463438070975773043734193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13138336378537456233249029 2463438070975773043734193)
            ·
              refine ⟨1847578553231829782800645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2463438070975773043734193 1847578553231829782800645)
              ·
                refine ⟨346420978730968084275121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1847578553231829782800645 346420978730968084275121)
                ·
                  refine ⟨259815734048226063206341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346420978730968084275121 259815734048226063206341)
                  ·
                    refine ⟨48715450134042386851189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259815734048226063206341 48715450134042386851189)
                    ·
                      rfl

theorem cell23_284619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 4].length) (baseStart_284619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284619 prefixEnd_284619 := by exact prefixLift 284619
  have htrace : WordTrace (prefixWord ++ tailWord_284619) baseStart_284619 baseEnd_284619 := by
    simpa [prefixWord, tailWord_284619, baseEnd_284619] using wordTrace_append hprefix tailTrace_284619
  have hstable : (prefixWord ++ tailWord_284619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284619).length < 2 ^ (prefixWord ++ tailWord_284619).sum := by decide
  have hdescent : baseEnd_284619 < baseStart_284619 := by decide
  rcases family_descends (prefixWord ++ tailWord_284619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284620 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 1, 1, 3]
def baseStart_284620 : Nat := 118140960795 + 284620 * 2 ^ 59
def prefixEnd_284620 : Nat := 4983230072969 + 3 ^ 40 * 284620 * 2
def baseEnd_284620 : Nat := 146146863882781656641063

theorem tailTrace_284620 : CollatzResearch.WordTrace tailWord_284620 prefixEnd_284620 146146863882781656641063 := by
  unfold tailWord_284620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190472114438912035565657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6920629485918549380754209 5190472114438912035565657)
  ·
    refine ⟨3892854085829184026674243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5190472114438912035565657 3892854085829184026674243)
    ·
      refine ⟨5839281128743776040011365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3892854085829184026674243 5839281128743776040011365)
      ·
        refine ⟨1094865211639458007502131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5839281128743776040011365 1094865211639458007502131)
        ·
          refine ⟨1642297817459187011253197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094865211639458007502131 1642297817459187011253197)
          ·
            refine ⟨615861681547195129219949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1642297817459187011253197 615861681547195129219949)
            ·
              refine ⟨230948130580198173457481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 615861681547195129219949 230948130580198173457481)
              ·
                refine ⟨173211097935148630093111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230948130580198173457481 173211097935148630093111)
                ·
                  refine ⟨259816646902722945139667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173211097935148630093111 259816646902722945139667)
                  ·
                    refine ⟨389724970354084417709501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259816646902722945139667 389724970354084417709501)
                    ·
                      refine ⟨146146863882781656641063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 389724970354084417709501 146146863882781656641063)
                      ·
                        rfl

theorem cell23_284620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_284620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284620 prefixEnd_284620 := by exact prefixLift 284620
  have htrace : WordTrace (prefixWord ++ tailWord_284620) baseStart_284620 baseEnd_284620 := by
    simpa [prefixWord, tailWord_284620, baseEnd_284620] using wordTrace_append hprefix tailTrace_284620
  have hstable : (prefixWord ++ tailWord_284620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284620).length < 2 ^ (prefixWord ++ tailWord_284620).sum := by decide
  have hdescent : baseEnd_284620 < baseStart_284620 := by decide
  rcases family_descends (prefixWord ++ tailWord_284620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284622 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_284622 : Nat := 118140960795 + 284622 * 2 ^ 59
def prefixEnd_284622 : Nat := 4983230072969 + 3 ^ 40 * 284622 * 2
def baseEnd_284622 : Nat := 146147890844090648816053

theorem tailTrace_284622 : CollatzResearch.WordTrace tailWord_284622 prefixEnd_284622 146147890844090648816053 := by
  unfold tailWord_284622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297627146858822301588015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6920678116580385608469413 1297627146858822301588015)
  ·
    refine ⟨1946440720288233452382023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297627146858822301588015 1946440720288233452382023)
    ·
      refine ⟨2919661080432350178573035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946440720288233452382023 2919661080432350178573035)
      ·
        refine ⟨4379491620648525267859553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2919661080432350178573035 4379491620648525267859553)
        ·
          refine ⟨3284618715486393950894665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4379491620648525267859553 3284618715486393950894665)
          ·
            refine ⟨2463464036614795463170999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284618715486393950894665 2463464036614795463170999)
            ·
              refine ⟨3695196054922193194756499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463464036614795463170999 3695196054922193194756499)
              ·
                refine ⟨5542794082383289792134749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695196054922193194756499 5542794082383289792134749)
                ·
                  refine ⟨2078547780893733672050531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5542794082383289792134749 2078547780893733672050531)
                  ·
                    refine ⟨3117821671340600508075797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2078547780893733672050531 3117821671340600508075797)
                    ·
                      refine ⟨146147890844090648816053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3117821671340600508075797 146147890844090648816053)
                      ·
                        rfl

theorem cell23_284622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_284622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284622 prefixEnd_284622 := by exact prefixLift 284622
  have htrace : WordTrace (prefixWord ++ tailWord_284622) baseStart_284622 baseEnd_284622 := by
    simpa [prefixWord, tailWord_284622, baseEnd_284622] using wordTrace_append hprefix tailTrace_284622
  have hstable : (prefixWord ++ tailWord_284622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284622).length < 2 ^ (prefixWord ++ tailWord_284622).sum := by decide
  have hdescent : baseEnd_284622 < baseStart_284622 := by decide
  rcases family_descends (prefixWord ++ tailWord_284622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284629 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_284629 : Nat := 118140960795 + 284629 * 2 ^ 59
def prefixEnd_284629 : Nat := 4983230072969 + 3 ^ 40 * 284629 * 2
def baseEnd_284629 : Nat := 146151485208672121428521

theorem tailTrace_284629 : CollatzResearch.WordTrace tailWord_284629 prefixEnd_284629 146151485208672121428521 := by
  unfold tailWord_284629
  simp only [CollatzResearch.WordTrace]
  refine ⟨10381272485845218608208941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6920848323896812405472627 10381272485845218608208941)
  ·
    refine ⟨3892977182191956978078353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10381272485845218608208941 3892977182191956978078353)
    ·
      refine ⟨2919732886643967733558765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3892977182191956978078353 2919732886643967733558765)
      ·
        refine ⟨1094899832491487900084537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2919732886643967733558765 1094899832491487900084537)
        ·
          refine ⟨821174874368615925063403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094899832491487900084537 821174874368615925063403)
          ·
            refine ⟨1231762311552923887595105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821174874368615925063403 1231762311552923887595105)
            ·
              refine ⟨923821733664692915696329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231762311552923887595105 923821733664692915696329)
              ·
                refine ⟨692866300248519686772247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923821733664692915696329 692866300248519686772247)
                ·
                  refine ⟨1039299450372779530158371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692866300248519686772247 1039299450372779530158371)
                  ·
                    refine ⟨1558949175559169295237557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1039299450372779530158371 1558949175559169295237557)
                    ·
                      refine ⟨146151485208672121428521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1558949175559169295237557 146151485208672121428521)
                      ·
                        rfl

theorem cell23_284629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_284629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284629 prefixEnd_284629 := by exact prefixLift 284629
  have htrace : WordTrace (prefixWord ++ tailWord_284629) baseStart_284629 baseEnd_284629 := by
    simpa [prefixWord, tailWord_284629, baseEnd_284629] using wordTrace_append hprefix tailTrace_284629
  have hstable : (prefixWord ++ tailWord_284629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284629).length < 2 ^ (prefixWord ++ tailWord_284629).sum := by decide
  have hdescent : baseEnd_284629 < baseStart_284629 := by decide
  rcases family_descends (prefixWord ++ tailWord_284629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284632 : List Nat := [2, 1, 2, 2, 2, 2, 4, 8]
def baseStart_284632 : Nat := 118140960795 + 284632 * 2 ^ 59
def prefixEnd_284632 : Nat := 4983230072969 + 3 ^ 40 * 284632 * 2
def baseEnd_284632 : Nat := 5413075024097615173741

theorem tailTrace_284632 : CollatzResearch.WordTrace tailWord_284632 prefixEnd_284632 5413075024097615173741 := by
  unfold tailWord_284632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190690952417175060284075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6920921269889566747045433 5190690952417175060284075)
  ·
    refine ⟨7786036428625762590426113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5190690952417175060284075 7786036428625762590426113)
    ·
      refine ⟨5839527321469321942819585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7786036428625762590426113 5839527321469321942819585)
      ·
        refine ⟨4379645491101991457114689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5839527321469321942819585 4379645491101991457114689)
        ·
          refine ⟨3284734118326493592836017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4379645491101991457114689 3284734118326493592836017)
          ·
            refine ⟨2463550588744870194627013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284734118326493592836017 2463550588744870194627013)
            ·
              refine ⟨461915735389663161492565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2463550588744870194627013 461915735389663161492565)
              ·
                refine ⟨5413075024097615173741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 461915735389663161492565 5413075024097615173741)
                ·
                  rfl

theorem cell23_284632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 8].length) (baseStart_284632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284632 prefixEnd_284632 := by exact prefixLift 284632
  have htrace : WordTrace (prefixWord ++ tailWord_284632) baseStart_284632 baseEnd_284632 := by
    simpa [prefixWord, tailWord_284632, baseEnd_284632] using wordTrace_append hprefix tailTrace_284632
  have hstable : (prefixWord ++ tailWord_284632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284632).length < 2 ^ (prefixWord ++ tailWord_284632).sum := by decide
  have hdescent : baseEnd_284632 < baseStart_284632 := by decide
  rcases family_descends (prefixWord ++ tailWord_284632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284659 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 3]
def baseStart_284659 : Nat := 118140960795 + 284659 * 2 ^ 59
def prefixEnd_284659 : Nat := 4983230072969 + 3 ^ 40 * 284659 * 2
def baseEnd_284659 : Nat := 146166889628307004053383

theorem tailTrace_284659 : CollatzResearch.WordTrace tailWord_284659 prefixEnd_284659 146166889628307004053383 := by
  unfold tailWord_284659
  simp only [CollatzResearch.WordTrace]
  refine ⟨10382366675736533731801031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6921577783824355821200687 10382366675736533731801031)
  ·
    refine ⟨15573550013604800597701547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10382366675736533731801031 15573550013604800597701547)
    ·
      refine ⟨23360325020407200896552321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15573550013604800597701547 23360325020407200896552321)
      ·
        refine ⟨17520243765305400672414241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23360325020407200896552321 17520243765305400672414241)
        ·
          refine ⟨13140182823979050504310681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17520243765305400672414241 13140182823979050504310681)
          ·
            refine ⟨9855137117984287878233011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13140182823979050504310681 9855137117984287878233011)
            ·
              refine ⟨14782705676976431817349517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9855137117984287878233011 14782705676976431817349517)
              ·
                refine ⟨5543514628866161931506069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14782705676976431817349517 5543514628866161931506069)
                ·
                  refine ⟨259852248228101340539347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5543514628866161931506069 259852248228101340539347)
                  ·
                    refine ⟨389778372342152010809021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259852248228101340539347 389778372342152010809021)
                    ·
                      refine ⟨146166889628307004053383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 389778372342152010809021 146166889628307004053383)
                      ·
                        rfl

theorem cell23_284659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_284659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284659 prefixEnd_284659 := by exact prefixLift 284659
  have htrace : WordTrace (prefixWord ++ tailWord_284659) baseStart_284659 baseEnd_284659 := by
    simpa [prefixWord, tailWord_284659, baseEnd_284659] using wordTrace_append hprefix tailTrace_284659
  have hstable : (prefixWord ++ tailWord_284659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284659).length < 2 ^ (prefixWord ++ tailWord_284659).sum := by decide
  have hdescent : baseEnd_284659 < baseStart_284659 := by decide
  rcases family_descends (prefixWord ++ tailWord_284659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284677 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 1, 2, 2]
def baseStart_284677 : Nat := 118140960795 + 284677 * 2 ^ 59
def prefixEnd_284677 : Nat := 4983230072969 + 3 ^ 40 * 284677 * 2
def baseEnd_284677 : Nat := 146176132280087933628301

theorem tailTrace_284677 : CollatzResearch.WordTrace tailWord_284677 prefixEnd_284677 146176132280087933628301 := by
  unfold tailWord_284677
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383023189671322805956285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6922015459780881870637523 10383023189671322805956285)
  ·
    refine ⟨3893633696126746052233607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10383023189671322805956285 3893633696126746052233607)
    ·
      refine ⟨5840450544190119078350411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3893633696126746052233607 5840450544190119078350411)
      ·
        refine ⟨8760675816285178617525617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840450544190119078350411 8760675816285178617525617)
        ·
          refine ⟨6570506862213883963144213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8760675816285178617525617 6570506862213883963144213)
          ·
            refine ⟨307992509166275810772385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6570506862213883963144213 307992509166275810772385)
            ·
              refine ⟨230994381874706858079289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307992509166275810772385 230994381874706858079289)
              ·
                refine ⟨173245786406030143559467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230994381874706858079289 173245786406030143559467)
                ·
                  refine ⟨259868679609045215339201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173245786406030143559467 259868679609045215339201)
                  ·
                    refine ⟨194901509706783911504401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259868679609045215339201 194901509706783911504401)
                    ·
                      refine ⟨146176132280087933628301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194901509706783911504401 146176132280087933628301)
                      ·
                        rfl

theorem cell23_284677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_284677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284677 prefixEnd_284677 := by exact prefixLift 284677
  have htrace : WordTrace (prefixWord ++ tailWord_284677) baseStart_284677 baseEnd_284677 := by
    simpa [prefixWord, tailWord_284677, baseEnd_284677] using wordTrace_append hprefix tailTrace_284677
  have hstable : (prefixWord ++ tailWord_284677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284677).length < 2 ^ (prefixWord ++ tailWord_284677).sum := by decide
  have hdescent : baseEnd_284677 < baseStart_284677 := by decide
  rcases family_descends (prefixWord ++ tailWord_284677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284686 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_284686 : Nat := 118140960795 + 284686 * 2 ^ 59
def prefixEnd_284686 : Nat := 4983230072969 + 3 ^ 40 * 284686 * 2
def baseEnd_284686 : Nat := 146180753605978398415759

theorem tailTrace_284686 : CollatzResearch.WordTrace tailWord_284686 prefixEnd_284686 146180753605978398415759 := by
  unfold tailWord_284686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297918930829839667879239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6922234297759144895355941 1297918930829839667879239)
  ·
    refine ⟨1946878396244759501818859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297918930829839667879239 1946878396244759501818859)
    ·
      refine ⟨2920317594367139252728289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946878396244759501818859 2920317594367139252728289)
      ·
        refine ⟨2190238195775354439546217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920317594367139252728289 2190238195775354439546217)
        ·
          refine ⟨1642678646831515829659663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190238195775354439546217 1642678646831515829659663)
          ·
            refine ⟨2464017970247273744489495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642678646831515829659663 2464017970247273744489495)
            ·
              refine ⟨3696026955370910616734243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464017970247273744489495 3696026955370910616734243)
              ·
                refine ⟨5544040433056365925101365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696026955370910616734243 5544040433056365925101365)
                ·
                  refine ⟨519753790599034305478253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5544040433056365925101365 519753790599034305478253)
                  ·
                    refine ⟨194907671474637864554345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519753790599034305478253 194907671474637864554345)
                    ·
                      refine ⟨146180753605978398415759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194907671474637864554345 146180753605978398415759)
                      ·
                        rfl

theorem cell23_284686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_284686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284686 prefixEnd_284686 := by exact prefixLift 284686
  have htrace : WordTrace (prefixWord ++ tailWord_284686) baseStart_284686 baseEnd_284686 := by
    simpa [prefixWord, tailWord_284686, baseEnd_284686] using wordTrace_append hprefix tailTrace_284686
  have hstable : (prefixWord ++ tailWord_284686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284686).length < 2 ^ (prefixWord ++ tailWord_284686).sum := by decide
  have hdescent : baseEnd_284686 < baseStart_284686 := by decide
  rcases family_descends (prefixWord ++ tailWord_284686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284720 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 1, 3, 2]
def baseStart_284720 : Nat := 118140960795 + 284720 * 2 ^ 59
def prefixEnd_284720 : Nat := 4983230072969 + 3 ^ 40 * 284720 * 2
def baseEnd_284720 : Nat := 146198211948231265390603

theorem tailTrace_284720 : CollatzResearch.WordTrace tailWord_284720 prefixEnd_284720 146198211948231265390603 := by
  unfold tailWord_284720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5192295764257770574885807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6923061019010360766514409 5192295764257770574885807)
  ·
    refine ⟨7788443646386655862328711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5192295764257770574885807 7788443646386655862328711)
    ·
      refine ⟨11682665469579983793493067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7788443646386655862328711 11682665469579983793493067)
      ·
        refine ⟨17523998204369975690239601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11682665469579983793493067 17523998204369975690239601)
        ·
          refine ⟨13142998653277481767679701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17523998204369975690239601 13142998653277481767679701)
          ·
            refine ⟨308039030936190978929993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13142998653277481767679701 308039030936190978929993)
            ·
              refine ⟨231029273202143234197495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308039030936190978929993 231029273202143234197495)
              ·
                refine ⟨346543909803214851296243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231029273202143234197495 346543909803214851296243)
                ·
                  refine ⟨519815864704822276944365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346543909803214851296243 519815864704822276944365)
                  ·
                    refine ⟨194930949264308353854137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519815864704822276944365 194930949264308353854137)
                    ·
                      refine ⟨146198211948231265390603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194930949264308353854137 146198211948231265390603)
                      ·
                        rfl

theorem cell23_284720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 3, 2].length) (baseStart_284720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284720 prefixEnd_284720 := by exact prefixLift 284720
  have htrace : WordTrace (prefixWord ++ tailWord_284720) baseStart_284720 baseEnd_284720 := by
    simpa [prefixWord, tailWord_284720, baseEnd_284720] using wordTrace_append hprefix tailTrace_284720
  have hstable : (prefixWord ++ tailWord_284720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284720).length < 2 ^ (prefixWord ++ tailWord_284720).sum := by decide
  have hdescent : baseEnd_284720 < baseStart_284720 := by decide
  rcases family_descends (prefixWord ++ tailWord_284720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284733 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_284733 : Nat := 118140960795 + 284733 * 2 ^ 59
def prefixEnd_284733 : Nat := 4983230072969 + 3 ^ 40 * 284733 * 2
def baseEnd_284733 : Nat := 146204887196739714528043

theorem tailTrace_284733 : CollatzResearch.WordTrace tailWord_284733 prefixEnd_284733 146204887196739714528043 := by
  unfold tailWord_284733
  simp only [CollatzResearch.WordTrace]
  refine ⟨10385065677468444369994853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6923377118312296246663235 10385065677468444369994853)
  ·
    refine ⟨1947199814525333319374035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10385065677468444369994853 1947199814525333319374035)
    ·
      refine ⟨2920799721787999979061053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947199814525333319374035 2920799721787999979061053)
      ·
        refine ⟨1095299895670499992147895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2920799721787999979061053 1095299895670499992147895)
        ·
          refine ⟨1642949843505749988221843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095299895670499992147895 1642949843505749988221843)
          ·
            refine ⟨2464424765258624982332765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642949843505749988221843 2464424765258624982332765)
            ·
              refine ⟨924159286971984368374787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2464424765258624982332765 924159286971984368374787)
              ·
                refine ⟨1386238930457976552562181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924159286971984368374787 1386238930457976552562181)
                ·
                  refine ⟨259919799460870603605409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386238930457976552562181 259919799460870603605409)
                  ·
                    refine ⟨194939849595652952704057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259919799460870603605409 194939849595652952704057)
                    ·
                      refine ⟨146204887196739714528043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194939849595652952704057 146204887196739714528043)
                      ·
                        rfl

theorem cell23_284733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_284733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284733 prefixEnd_284733 := by exact prefixLift 284733
  have htrace : WordTrace (prefixWord ++ tailWord_284733) baseStart_284733 baseEnd_284733 := by
    simpa [prefixWord, tailWord_284733, baseEnd_284733] using wordTrace_append hprefix tailTrace_284733
  have hstable : (prefixWord ++ tailWord_284733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284733).length < 2 ^ (prefixWord ++ tailWord_284733).sum := by decide
  have hdescent : baseEnd_284733 < baseStart_284733 := by decide
  rcases family_descends (prefixWord ++ tailWord_284733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284769 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_284769 : Nat := 118140960795 + 284769 * 2 ^ 59
def prefixEnd_284769 : Nat := 4983230072969 + 3 ^ 40 * 284769 * 2
def baseEnd_284769 : Nat := 48741124166767191225959

theorem tailTrace_284769 : CollatzResearch.WordTrace tailWord_284769 prefixEnd_284769 48741124166767191225959 := by
  unfold tailWord_284769
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386378705338022518305361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6924252470225348345536907 10386378705338022518305361)
  ·
    refine ⟨7789784029003516888729021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10386378705338022518305361 7789784029003516888729021)
    ·
      refine ⟨2921169010876318833273383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7789784029003516888729021 2921169010876318833273383)
      ·
        refine ⟨4381753516314478249910075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921169010876318833273383 4381753516314478249910075)
        ·
          refine ⟨6572630274471717374865113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4381753516314478249910075 6572630274471717374865113)
          ·
            refine ⟨4929472705853788031148835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6572630274471717374865113 4929472705853788031148835)
            ·
              refine ⟨7394209058780682046723253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929472705853788031148835 7394209058780682046723253)
              ·
                refine ⟨693207099260688941880305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7394209058780682046723253 693207099260688941880305)
                ·
                  refine ⟨519905324445516706410229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 693207099260688941880305 519905324445516706410229)
                  ·
                    refine ⟨48741124166767191225959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 519905324445516706410229 48741124166767191225959)
                    ·
                      rfl

theorem cell23_284769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_284769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284769 prefixEnd_284769 := by exact prefixLift 284769
  have htrace : WordTrace (prefixWord ++ tailWord_284769) baseStart_284769 baseEnd_284769 := by
    simpa [prefixWord, tailWord_284769, baseEnd_284769] using wordTrace_append hprefix tailTrace_284769
  have hstable : (prefixWord ++ tailWord_284769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284769).length < 2 ^ (prefixWord ++ tailWord_284769).sum := by decide
  have hdescent : baseEnd_284769 < baseStart_284769 := by decide
  rcases family_descends (prefixWord ++ tailWord_284769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284773 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 5]
def baseStart_284773 : Nat := 118140960795 + 284773 * 2 ^ 59
def prefixEnd_284773 : Nat := 4983230072969 + 3 ^ 40 * 284773 * 2
def baseEnd_284773 : Nat := 16247269602546617558651

theorem tailTrace_284773 : CollatzResearch.WordTrace tailWord_284773 prefixEnd_284773 16247269602546617558651 := by
  unfold tailWord_284773
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386524597323531201450973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6924349731549020800967315 10386524597323531201450973)
  ·
    refine ⟨3894946723996324200544115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10386524597323531201450973 3894946723996324200544115)
    ·
      refine ⟨5842420085994486300816173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3894946723996324200544115 5842420085994486300816173)
      ·
        refine ⟨2190907532247932362806065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5842420085994486300816173 2190907532247932362806065)
        ·
          refine ⟨1643180649185949272104549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190907532247932362806065 1643180649185949272104549)
          ·
            refine ⟨308096371722365488519603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1643180649185949272104549 308096371722365488519603)
            ·
              refine ⟨462144557583548232779405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308096371722365488519603 462144557583548232779405)
              ·
                refine ⟨173304209093830587292277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462144557583548232779405 173304209093830587292277)
                ·
                  refine ⟨16247269602546617558651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173304209093830587292277 16247269602546617558651)
                  ·
                    rfl

theorem cell23_284773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_284773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284773 prefixEnd_284773 := by exact prefixLift 284773
  have htrace : WordTrace (prefixWord ++ tailWord_284773) baseStart_284773 baseEnd_284773 := by
    simpa [prefixWord, tailWord_284773, baseEnd_284773] using wordTrace_append hprefix tailTrace_284773
  have hstable : (prefixWord ++ tailWord_284773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284773).length < 2 ^ (prefixWord ++ tailWord_284773).sum := by decide
  have hdescent : baseEnd_284773 < baseStart_284773 := by decide
  rcases family_descends (prefixWord ++ tailWord_284773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284786 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_284786 : Nat := 118140960795 + 284786 * 2 ^ 59
def prefixEnd_284786 : Nat := 4983230072969 + 3 ^ 40 * 284786 * 2
def baseEnd_284786 : Nat := 48744033890476002388433

theorem tailTrace_284786 : CollatzResearch.WordTrace tailWord_284786 prefixEnd_284786 48744033890476002388433 := by
  unfold tailWord_284786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596749686569108605418553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6924665830850956281116141 2596749686569108605418553)
  ·
    refine ⟨1947562264926831454063915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2596749686569108605418553 1947562264926831454063915)
    ·
      refine ⟨2921343397390247181095873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947562264926831454063915 2921343397390247181095873)
      ·
        refine ⟨2191007548042685385821905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921343397390247181095873 2191007548042685385821905)
        ·
          refine ⟨1643255661032014039366429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2191007548042685385821905 1643255661032014039366429)
          ·
            refine ⟨616220872887005264762411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1643255661032014039366429 616220872887005264762411)
            ·
              refine ⟨924331309330507897143617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616220872887005264762411 924331309330507897143617)
              ·
                refine ⟨693248481997880922857713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 924331309330507897143617 693248481997880922857713)
                ·
                  refine ⟨519936361498410692143285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 693248481997880922857713 519936361498410692143285)
                  ·
                    refine ⟨48744033890476002388433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 519936361498410692143285 48744033890476002388433)
                    ·
                      rfl

theorem cell23_284786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_284786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284786 prefixEnd_284786 := by exact prefixLift 284786
  have htrace : WordTrace (prefixWord ++ tailWord_284786) baseStart_284786 baseEnd_284786 := by
    simpa [prefixWord, tailWord_284786, baseEnd_284786] using wordTrace_append hprefix tailTrace_284786
  have hstable : (prefixWord ++ tailWord_284786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284786).length < 2 ^ (prefixWord ++ tailWord_284786).sum := by decide
  have hdescent : baseEnd_284786 < baseStart_284786 := by decide
  rcases family_descends (prefixWord ++ tailWord_284786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284790 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_284790 : Nat := 118140960795 + 284790 * 2 ^ 59
def prefixEnd_284790 : Nat := 4983230072969 + 3 ^ 40 * 284790 * 2
def baseEnd_284790 : Nat := 16248239510449554612809

theorem tailTrace_284790 : CollatzResearch.WordTrace tailWord_284790 prefixEnd_284790 16248239510449554612809 := by
  unfold tailWord_284790
  simp only [CollatzResearch.WordTrace]
  refine ⟨649196539891371444051239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6924763092174628736546549 649196539891371444051239)
  ·
    refine ⟨973794809837057166076859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649196539891371444051239 973794809837057166076859)
    ·
      refine ⟨1460692214755585749115289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973794809837057166076859 1460692214755585749115289)
      ·
        refine ⟨1095519161066689311836467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460692214755585749115289 1095519161066689311836467)
        ·
          refine ⟨1643278741600033967754701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095519161066689311836467 1643278741600033967754701)
          ·
            refine ⟨616229528100012737908013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1643278741600033967754701 616229528100012737908013)
            ·
              refine ⟨231086073037504776715505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 616229528100012737908013 231086073037504776715505)
              ·
                refine ⟨173314554778128582536629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231086073037504776715505 173314554778128582536629)
                ·
                  refine ⟨16248239510449554612809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173314554778128582536629 16248239510449554612809)
                  ·
                    rfl

theorem cell23_284790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_284790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284790 prefixEnd_284790 := by exact prefixLift 284790
  have htrace : WordTrace (prefixWord ++ tailWord_284790) baseStart_284790 baseEnd_284790 := by
    simpa [prefixWord, tailWord_284790, baseEnd_284790] using wordTrace_append hprefix tailTrace_284790
  have hstable : (prefixWord ++ tailWord_284790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284790).length < 2 ^ (prefixWord ++ tailWord_284790).sum := by decide
  have hdescent : baseEnd_284790 < baseStart_284790 := by decide
  rcases family_descends (prefixWord ++ tailWord_284790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284820 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_284820 : Nat := 118140960795 + 284820 * 2 ^ 59
def prefixEnd_284820 : Nat := 4983230072969 + 3 ^ 40 * 284820 * 2
def baseEnd_284820 : Nat := 48749853337893624713381

theorem tailTrace_284820 : CollatzResearch.WordTrace tailWord_284820 prefixEnd_284820 48749853337893624713381 := by
  unfold tailWord_284820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5194119414076629114205957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6925492552102172152274609 5194119414076629114205957)
  ·
    refine ⟨973897390139367958913617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5194119414076629114205957 973897390139367958913617)
    ·
      refine ⟨730423042604525969185213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 973897390139367958913617 730423042604525969185213)
      ·
        refine ⟨273908640976697238444455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 730423042604525969185213 273908640976697238444455)
        ·
          refine ⟨410862961465045857666683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273908640976697238444455 410862961465045857666683)
          ·
            refine ⟨616294442197568786500025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410862961465045857666683 616294442197568786500025)
            ·
              refine ⟨462220831648176589875019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616294442197568786500025 462220831648176589875019)
              ·
                refine ⟨693331247472264884812529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462220831648176589875019 693331247472264884812529)
                ·
                  refine ⟨519998435604198663609397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 693331247472264884812529 519998435604198663609397)
                  ·
                    refine ⟨48749853337893624713381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 519998435604198663609397 48749853337893624713381)
                    ·
                      rfl

theorem cell23_284820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_284820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284820 prefixEnd_284820 := by exact prefixLift 284820
  have htrace : WordTrace (prefixWord ++ tailWord_284820) baseStart_284820 baseEnd_284820 := by
    simpa [prefixWord, tailWord_284820, baseEnd_284820] using wordTrace_append hprefix tailTrace_284820
  have hstable : (prefixWord ++ tailWord_284820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284820).length < 2 ^ (prefixWord ++ tailWord_284820).sum := by decide
  have hdescent : baseEnd_284820 < baseStart_284820 := by decide
  rcases family_descends (prefixWord ++ tailWord_284820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284823 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_284823 : Nat := 118140960795 + 284823 * 2 ^ 59
def prefixEnd_284823 : Nat := 4983230072969 + 3 ^ 40 * 284823 * 2
def baseEnd_284823 : Nat := 146251100455644362402629

theorem tailTrace_284823 : CollatzResearch.WordTrace tailWord_284823 prefixEnd_284823 146251100455644362402629 := by
  unfold tailWord_284823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388348247142389740771123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6925565498094926493847415 10388348247142389740771123)
  ·
    refine ⟨15582522370713584611156685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10388348247142389740771123 15582522370713584611156685)
    ·
      refine ⟨5843445889017594229183757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15582522370713584611156685 5843445889017594229183757)
      ·
        refine ⟨2191292208381597835943909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5843445889017594229183757 2191292208381597835943909)
        ·
          refine ⟨410867289071549594239483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2191292208381597835943909 410867289071549594239483)
          ·
            refine ⟨616300933607324391359225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410867289071549594239483 616300933607324391359225)
            ·
              refine ⟨462225700205493293519419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616300933607324391359225 462225700205493293519419)
              ·
                refine ⟨693338550308239940279129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462225700205493293519419 693338550308239940279129)
                ·
                  refine ⟨520003912731179955209347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 693338550308239940279129 520003912731179955209347)
                  ·
                    refine ⟨780005869096769932814021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 520003912731179955209347 780005869096769932814021)
                    ·
                      refine ⟨146251100455644362402629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 780005869096769932814021 146251100455644362402629)
                      ·
                        rfl

theorem cell23_284823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_284823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284823 prefixEnd_284823 := by exact prefixLift 284823
  have htrace : WordTrace (prefixWord ++ tailWord_284823) baseStart_284823 baseEnd_284823 := by
    simpa [prefixWord, tailWord_284823, baseEnd_284823] using wordTrace_append hprefix tailTrace_284823
  have hstable : (prefixWord ++ tailWord_284823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284823).length < 2 ^ (prefixWord ++ tailWord_284823).sum := by decide
  have hdescent : baseEnd_284823 < baseStart_284823 := by decide
  rcases family_descends (prefixWord ++ tailWord_284823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284859 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 5, 5]
def baseStart_284859 : Nat := 118140960795 + 284859 * 2 ^ 59
def prefixEnd_284859 : Nat := 4983230072969 + 3 ^ 40 * 284859 * 2
def baseEnd_284859 : Nat := 48756528586402073850821

theorem tailTrace_284859 : CollatzResearch.WordTrace tailWord_284859 prefixEnd_284859 48756528586402073850821 := by
  unfold tailWord_284859
  simp only [CollatzResearch.WordTrace]
  refine ⟨10389661275011967889081631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6926440850007978592721087 10389661275011967889081631)
  ·
    refine ⟨15584491912517951833622447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10389661275011967889081631 15584491912517951833622447)
    ·
      refine ⟨23376737868776927750433671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15584491912517951833622447 23376737868776927750433671)
      ·
        refine ⟨35065106803165391625650507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23376737868776927750433671 35065106803165391625650507)
        ·
          refine ⟨52597660204748087438475761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35065106803165391625650507 52597660204748087438475761)
          ·
            refine ⟨39448245153561065578856821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52597660204748087438475761 39448245153561065578856821)
            ·
              refine ⟨3698272983146349898017827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39448245153561065578856821 3698272983146349898017827)
              ·
                refine ⟨5547409474719524847026741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698272983146349898017827 5547409474719524847026741)
                ·
                  refine ⟨520069638254955454408757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5547409474719524847026741 520069638254955454408757)
                  ·
                    refine ⟨48756528586402073850821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 520069638254955454408757 48756528586402073850821)
                    ·
                      rfl

theorem cell23_284859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 5].length) (baseStart_284859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284859 prefixEnd_284859 := by exact prefixLift 284859
  have htrace : WordTrace (prefixWord ++ tailWord_284859) baseStart_284859 baseEnd_284859 := by
    simpa [prefixWord, tailWord_284859, baseEnd_284859] using wordTrace_append hprefix tailTrace_284859
  have hstable : (prefixWord ++ tailWord_284859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284859).length < 2 ^ (prefixWord ++ tailWord_284859).sum := by decide
  have hdescent : baseEnd_284859 < baseStart_284859 := by decide
  rcases family_descends (prefixWord ++ tailWord_284859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284890 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3]
def baseStart_284890 : Nat := 118140960795 + 284890 * 2 ^ 59
def prefixEnd_284890 : Nat := 4983230072969 + 3 ^ 40 * 284890 * 2
def baseEnd_284890 : Nat := 146285503659495600264821

theorem tailTrace_284890 : CollatzResearch.WordTrace tailWord_284890 prefixEnd_284890 146285503659495600264821 := by
  unfold tailWord_284890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597697984474915045865031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6927194625266440122306749 2597697984474915045865031)
  ·
    refine ⟨3896546976712372568797547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597697984474915045865031 3896546976712372568797547)
    ·
      refine ⟨5844820465068558853196321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3896546976712372568797547 5844820465068558853196321)
      ·
        refine ⟨4383615348801419139897241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5844820465068558853196321 4383615348801419139897241)
        ·
          refine ⟨3287711511601064354922931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4383615348801419139897241 3287711511601064354922931)
          ·
            refine ⟨4931567267401596532384397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287711511601064354922931 4931567267401596532384397)
            ·
              refine ⟨1849337725275598699644149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931567267401596532384397 1849337725275598699644149)
              ·
                refine ⟨173375411744587378091639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1849337725275598699644149 173375411744587378091639)
                ·
                  refine ⟨260063117616881067137459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173375411744587378091639 260063117616881067137459)
                  ·
                    refine ⟨390094676425321600706189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260063117616881067137459 390094676425321600706189)
                    ·
                      refine ⟨146285503659495600264821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390094676425321600706189 146285503659495600264821)
                      ·
                        rfl

theorem cell23_284890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_284890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284890 prefixEnd_284890 := by exact prefixLift 284890
  have htrace : WordTrace (prefixWord ++ tailWord_284890) baseStart_284890 baseEnd_284890 := by
    simpa [prefixWord, tailWord_284890, baseEnd_284890] using wordTrace_append hprefix tailTrace_284890
  have hstable : (prefixWord ++ tailWord_284890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284890).length < 2 ^ (prefixWord ++ tailWord_284890).sum := by decide
  have hdescent : baseEnd_284890 < baseStart_284890 := by decide
  rcases family_descends (prefixWord ++ tailWord_284890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284930 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_284930 : Nat := 118140960795 + 284930 * 2 ^ 59
def prefixEnd_284930 : Nat := 4983230072969 + 3 ^ 40 * 284930 * 2
def baseEnd_284930 : Nat := 146306042885675443764637

theorem tailTrace_284930 : CollatzResearch.WordTrace tailWord_284930 prefixEnd_284930 146306042885675443764637 := by
  unfold tailWord_284930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598062714438686753729061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6928167238503164676610829 2598062714438686753729061)
  ·
    refine ⟨487136758957253766324199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2598062714438686753729061 487136758957253766324199)
    ·
      refine ⟨730705138435880649486299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487136758957253766324199 730705138435880649486299)
      ·
        refine ⟨1096057707653820974229449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730705138435880649486299 1096057707653820974229449)
        ·
          refine ⟨822043280740365730672087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1096057707653820974229449 822043280740365730672087)
          ·
            refine ⟨1233064921110548596008131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822043280740365730672087 1233064921110548596008131)
            ·
              refine ⟨1849597381665822894012197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233064921110548596008131 1849597381665822894012197)
              ·
                refine ⟨346799509062341792627287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1849597381665822894012197 346799509062341792627287)
                ·
                  refine ⟨520199263593512688940931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346799509062341792627287 520199263593512688940931)
                  ·
                    refine ⟨780298895390269033411397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 520199263593512688940931 780298895390269033411397)
                    ·
                      refine ⟨146306042885675443764637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 780298895390269033411397 146306042885675443764637)
                      ·
                        rfl

theorem cell23_284930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_284930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284930 prefixEnd_284930 := by exact prefixLift 284930
  have htrace : WordTrace (prefixWord ++ tailWord_284930) baseStart_284930 baseEnd_284930 := by
    simpa [prefixWord, tailWord_284930, baseEnd_284930] using wordTrace_append hprefix tailTrace_284930
  have hstable : (prefixWord ++ tailWord_284930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284930).length < 2 ^ (prefixWord ++ tailWord_284930).sum := by decide
  have hdescent : baseEnd_284930 < baseStart_284930 := by decide
  rcases family_descends (prefixWord ++ tailWord_284930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284936 : List Nat := [2, 1, 3, 2, 3, 2, 1, 9]
def baseStart_284936 : Nat := 118140960795 + 284936 * 2 ^ 59
def prefixEnd_284936 : Nat := 4983230072969 + 3 ^ 40 * 284936 * 2
def baseEnd_284936 : Nat := 5418856435911200751467

theorem tailTrace_284936 : CollatzResearch.WordTrace tailWord_284936 prefixEnd_284936 5418856435911200751467 := by
  unfold tailWord_284936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196234847866505019817331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6928313130488673359756441 5196234847866505019817331)
  ·
    refine ⟨7794352271799757529725997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5196234847866505019817331 7794352271799757529725997)
    ·
      refine ⟨2922882101924909073647249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7794352271799757529725997 2922882101924909073647249)
      ·
        refine ⟨2192161576443681805235437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2922882101924909073647249 2192161576443681805235437)
        ·
          refine ⟨822060591166380676963289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2192161576443681805235437 822060591166380676963289)
          ·
            refine ⟨616545443374785507722467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 822060591166380676963289 616545443374785507722467)
            ·
              refine ⟨924818165062178261583701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616545443374785507722467 924818165062178261583701)
              ·
                refine ⟨5418856435911200751467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 924818165062178261583701 5418856435911200751467)
                ·
                  rfl

theorem cell23_284936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 9].length) (baseStart_284936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284936 prefixEnd_284936 := by exact prefixLift 284936
  have htrace : WordTrace (prefixWord ++ tailWord_284936) baseStart_284936 baseEnd_284936 := by
    simpa [prefixWord, tailWord_284936, baseEnd_284936] using wordTrace_append hprefix tailTrace_284936
  have hstable : (prefixWord ++ tailWord_284936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284936).length < 2 ^ (prefixWord ++ tailWord_284936).sum := by decide
  have hdescent : baseEnd_284936 < baseStart_284936 := by decide
  rcases family_descends (prefixWord ++ tailWord_284936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284963 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 3]
def baseStart_284963 : Nat := 118140960795 + 284963 * 2 ^ 59
def prefixEnd_284963 : Nat := 4983230072969 + 3 ^ 40 * 284963 * 2
def baseEnd_284963 : Nat := 146322987747273814651985

theorem tailTrace_284963 : CollatzResearch.WordTrace tailWord_284963 prefixEnd_284963 146322987747273814651985 := by
  unfold tailWord_284963
  simp only [CollatzResearch.WordTrace]
  refine ⟨10393454466635193650867543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6928969644423462433911695 10393454466635193650867543)
  ·
    refine ⟨15590181699952790476301315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10393454466635193650867543 15590181699952790476301315)
    ·
      refine ⟨23385272549929185714451973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15590181699952790476301315 23385272549929185714451973)
      ·
        refine ⟨4384738603111722321459745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23385272549929185714451973 4384738603111722321459745)
        ·
          refine ⟨3288553952333791741094809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4384738603111722321459745 3288553952333791741094809)
          ·
            refine ⟨2466415464250343805821107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288553952333791741094809 2466415464250343805821107)
            ·
              refine ⟨3699623196375515708731661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466415464250343805821107 3699623196375515708731661)
              ·
                refine ⟨1387358698640818390774373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3699623196375515708731661 1387358698640818390774373)
                ·
                  refine ⟨260129755995153448270195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387358698640818390774373 260129755995153448270195)
                  ·
                    refine ⟨390194633992730172405293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260129755995153448270195 390194633992730172405293)
                    ·
                      refine ⟨146322987747273814651985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390194633992730172405293 146322987747273814651985)
                      ·
                        rfl

theorem cell23_284963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_284963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284963 prefixEnd_284963 := by exact prefixLift 284963
  have htrace : WordTrace (prefixWord ++ tailWord_284963) baseStart_284963 baseEnd_284963 := by
    simpa [prefixWord, tailWord_284963, baseEnd_284963] using wordTrace_append hprefix tailTrace_284963
  have hstable : (prefixWord ++ tailWord_284963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284963).length < 2 ^ (prefixWord ++ tailWord_284963).sum := by decide
  have hdescent : baseEnd_284963 < baseStart_284963 := by decide
  rcases family_descends (prefixWord ++ tailWord_284963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285006 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_285006 : Nat := 118140960795 + 285006 * 2 ^ 59
def prefixEnd_285006 : Nat := 4983230072969 + 3 ^ 40 * 285006 * 2
def baseEnd_285006 : Nat := 146345067415417146414287

theorem tailTrace_285006 : CollatzResearch.WordTrace tailWord_285006 prefixEnd_285006 146345067415417146414287 := by
  unfold tailWord_285006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299377850684926499335359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6930015203652941329788581 1299377850684926499335359)
  ·
    refine ⟨1949066776027389749003039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1299377850684926499335359 1949066776027389749003039)
    ·
      refine ⟨2923600164041084623504559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1949066776027389749003039 2923600164041084623504559)
      ·
        refine ⟨4385400246061626935256839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2923600164041084623504559 4385400246061626935256839)
        ·
          refine ⟨6578100369092440402885259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385400246061626935256839 6578100369092440402885259)
          ·
            refine ⟨9867150553638660604327889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578100369092440402885259 9867150553638660604327889)
            ·
              refine ⟨7400362915228995453245917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9867150553638660604327889 7400362915228995453245917)
              ·
                refine ⟨2775136093210873294967219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7400362915228995453245917 2775136093210873294967219)
                ·
                  refine ⟨4162704139816309942450829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775136093210873294967219 4162704139816309942450829)
                  ·
                    refine ⟨1561014052431116228419061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4162704139816309942450829 1561014052431116228419061)
                    ·
                      refine ⟨146345067415417146414287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1561014052431116228419061 146345067415417146414287)
                      ·
                        rfl

theorem cell23_285006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_285006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285006 prefixEnd_285006 := by exact prefixLift 285006
  have htrace : WordTrace (prefixWord ++ tailWord_285006) baseStart_285006 baseEnd_285006 := by
    simpa [prefixWord, tailWord_285006, baseEnd_285006] using wordTrace_append hprefix tailTrace_285006
  have hstable : (prefixWord ++ tailWord_285006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285006).length < 2 ^ (prefixWord ++ tailWord_285006).sum := by decide
  have hdescent : baseEnd_285006 < baseStart_285006 := by decide
  rcases family_descends (prefixWord ++ tailWord_285006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285037 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_285037 : Nat := 118140960795 + 285037 * 2 ^ 59
def prefixEnd_285037 : Nat := 4983230072969 + 3 ^ 40 * 285037 * 2
def baseEnd_285037 : Nat := 146360985315706525126645

theorem tailTrace_285037 : CollatzResearch.WordTrace tailWord_285037 prefixEnd_285037 146360985315706525126645 := by
  unfold tailWord_285037
  simp only [CollatzResearch.WordTrace]
  refine ⟨10396153468367104289061365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6930768978911402859374243 10396153468367104289061365)
  ·
    refine ⟨974639387659416027099503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10396153468367104289061365 974639387659416027099503)
    ·
      refine ⟨1461959081489124040649255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 974639387659416027099503 1461959081489124040649255)
      ·
        refine ⟨2192938622233686060973883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461959081489124040649255 2192938622233686060973883)
        ·
          refine ⟨3289407933350529091460825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192938622233686060973883 3289407933350529091460825)
          ·
            refine ⟨2467055950012896818595619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3289407933350529091460825 2467055950012896818595619)
            ·
              refine ⟨3700583925019345227893429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467055950012896818595619 3700583925019345227893429)
              ·
                refine ⟨346929742970563615115009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3700583925019345227893429 346929742970563615115009)
                ·
                  refine ⟨260197307227922711336257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346929742970563615115009 260197307227922711336257)
                  ·
                    refine ⟨195147980420942033502193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260197307227922711336257 195147980420942033502193)
                    ·
                      refine ⟨146360985315706525126645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195147980420942033502193 146360985315706525126645)
                      ·
                        rfl

theorem cell23_285037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_285037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285037 prefixEnd_285037 := by exact prefixLift 285037
  have htrace : WordTrace (prefixWord ++ tailWord_285037) baseStart_285037 baseEnd_285037 := by
    simpa [prefixWord, tailWord_285037, baseEnd_285037] using wordTrace_append hprefix tailTrace_285037
  have hstable : (prefixWord ++ tailWord_285037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285037).length < 2 ^ (prefixWord ++ tailWord_285037).sum := by decide
  have hdescent : baseEnd_285037 < baseStart_285037 := by decide
  rcases family_descends (prefixWord ++ tailWord_285037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285058 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_285058 : Nat := 118140960795 + 285058 * 2 ^ 59
def prefixEnd_285058 : Nat := 4983230072969 + 3 ^ 40 * 285058 * 2
def baseEnd_285058 : Nat := 146371768409450942964049

theorem tailTrace_285058 : CollatzResearch.WordTrace tailWord_285058 prefixEnd_285058 146371768409450942964049 := by
  unfold tailWord_285058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599229850322756218893957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6931279600860683250383885 2599229850322756218893957)
  ·
    refine ⟨487355596935516791042617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2599229850322756218893957 487355596935516791042617)
    ·
      refine ⟨365516697701637593281963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 487355596935516791042617 365516697701637593281963)
      ·
        refine ⟨548275046552456389922945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365516697701637593281963 548275046552456389922945)
        ·
          refine ⟨411206284914342292442209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548275046552456389922945 411206284914342292442209)
          ·
            refine ⟨308404713685756719331657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411206284914342292442209 308404713685756719331657)
            ·
              refine ⟨231303535264317539498743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308404713685756719331657 231303535264317539498743)
              ·
                refine ⟨346955302896476309248115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231303535264317539498743 346955302896476309248115)
                ·
                  refine ⟨520432954344714463872173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346955302896476309248115 520432954344714463872173)
                  ·
                    refine ⟨195162357879267923952065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520432954344714463872173 195162357879267923952065)
                    ·
                      refine ⟨146371768409450942964049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195162357879267923952065 146371768409450942964049)
                      ·
                        rfl

theorem cell23_285058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_285058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285058 prefixEnd_285058 := by exact prefixLift 285058
  have htrace : WordTrace (prefixWord ++ tailWord_285058) baseStart_285058 baseEnd_285058 := by
    simpa [prefixWord, tailWord_285058, baseEnd_285058] using wordTrace_append hprefix tailTrace_285058
  have hstable : (prefixWord ++ tailWord_285058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285058).length < 2 ^ (prefixWord ++ tailWord_285058).sum := by decide
  have hdescent : baseEnd_285058 < baseStart_285058 := by decide
  rcases family_descends (prefixWord ++ tailWord_285058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285060 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 5]
def baseStart_285060 : Nat := 118140960795 + 285060 * 2 ^ 59
def prefixEnd_285060 : Nat := 4983230072969 + 3 ^ 40 * 285060 * 2
def baseEnd_285060 : Nat := 16263643930084437237671

theorem tailTrace_285060 : CollatzResearch.WordTrace tailWord_285060 prefixEnd_285060 16263643930084437237671 := by
  unfold tailWord_285060
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198496173641889608574317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6931328231522519478099089 5198496173641889608574317)
  ·
    refine ⟨1949436065115708603215369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5198496173641889608574317 1949436065115708603215369)
    ·
      refine ⟨1462077048836781452411527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1949436065115708603215369 1462077048836781452411527)
      ·
        refine ⟨2193115573255172178617291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462077048836781452411527 2193115573255172178617291)
        ·
          refine ⟨3289673359882758267925937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2193115573255172178617291 3289673359882758267925937)
          ·
            refine ⟨2467255019912068700944453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3289673359882758267925937 2467255019912068700944453)
            ·
              refine ⟨462610316233512881427085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2467255019912068700944453 462610316233512881427085)
              ·
                refine ⟨173478868587567330535157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462610316233512881427085 173478868587567330535157)
                ·
                  refine ⟨16263643930084437237671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173478868587567330535157 16263643930084437237671)
                  ·
                    rfl

theorem cell23_285060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_285060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285060 prefixEnd_285060 := by exact prefixLift 285060
  have htrace : WordTrace (prefixWord ++ tailWord_285060) baseStart_285060 baseEnd_285060 := by
    simpa [prefixWord, tailWord_285060, baseEnd_285060] using wordTrace_append hprefix tailTrace_285060
  have hstable : (prefixWord ++ tailWord_285060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285060).length < 2 ^ (prefixWord ++ tailWord_285060).sum := by decide
  have hdescent : baseEnd_285060 < baseStart_285060 := by decide
  rcases family_descends (prefixWord ++ tailWord_285060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285070 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_285070 : Nat := 118140960795 + 285070 * 2 ^ 59
def prefixEnd_285070 : Nat := 4983230072969 + 3 ^ 40 * 285070 * 2
def baseEnd_285070 : Nat := 146377930177304896013993

theorem tailTrace_285070 : CollatzResearch.WordTrace tailWord_285070 prefixEnd_285070 146377930177304896013993 := by
  unfold tailWord_285070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299669634655943865626583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6931571384831700616675109 1299669634655943865626583)
  ·
    refine ⟨1949504451983915798439875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1299669634655943865626583 1949504451983915798439875)
    ·
      refine ⟨2924256677975873697659813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1949504451983915798439875 2924256677975873697659813)
      ·
        refine ⟨548298127120476318311215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2924256677975873697659813 548298127120476318311215)
        ·
          refine ⟨822447190680714477466823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548298127120476318311215 822447190680714477466823)
          ·
            refine ⟨1233670786021071716200235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822447190680714477466823 1233670786021071716200235)
            ·
              refine ⟨1850506179031607574300353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233670786021071716200235 1850506179031607574300353)
              ·
                refine ⟨1387879634273705680725265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850506179031607574300353 1387879634273705680725265)
                ·
                  refine ⟨1040909725705279260543949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1387879634273705680725265 1040909725705279260543949)
                  ·
                    refine ⟨390341147139479722703981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040909725705279260543949 390341147139479722703981)
                    ·
                      refine ⟨146377930177304896013993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390341147139479722703981 146377930177304896013993)
                      ·
                        rfl

theorem cell23_285070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_285070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285070 prefixEnd_285070 := by exact prefixLift 285070
  have htrace : WordTrace (prefixWord ++ tailWord_285070) baseStart_285070 baseEnd_285070 := by
    simpa [prefixWord, tailWord_285070, baseEnd_285070] using wordTrace_append hprefix tailTrace_285070
  have hstable : (prefixWord ++ tailWord_285070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285070).length < 2 ^ (prefixWord ++ tailWord_285070).sum := by decide
  have hdescent : baseEnd_285070 < baseStart_285070 := by decide
  rcases family_descends (prefixWord ++ tailWord_285070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285130 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_285130 : Nat := 118140960795 + 285130 * 2 ^ 59
def prefixEnd_285130 : Nat := 4983230072969 + 3 ^ 40 * 285130 * 2
def baseEnd_285130 : Nat := 146408739016574661263717

theorem tailTrace_285130 : CollatzResearch.WordTrace tailWord_285130 prefixEnd_285130 146408739016574661263717 := by
  unfold tailWord_285130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599886364257545293049211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6933030304686787448131229 2599886364257545293049211)
  ·
    refine ⟨3899829546386317939573817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2599886364257545293049211 3899829546386317939573817)
    ·
      refine ⟨2924872159789738454680363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3899829546386317939573817 2924872159789738454680363)
      ·
        refine ⟨4387308239684607682020545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924872159789738454680363 4387308239684607682020545)
        ·
          refine ⟨3290481179763455761515409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4387308239684607682020545 3290481179763455761515409)
          ·
            refine ⟨2467860884822591821136557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3290481179763455761515409 2467860884822591821136557)
            ·
              refine ⟨925447831808471932926209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2467860884822591821136557 925447831808471932926209)
              ·
                refine ⟨694085873856353949694657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925447831808471932926209 694085873856353949694657)
                ·
                  refine ⟨520564405392265462270993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694085873856353949694657 520564405392265462270993)
                  ·
                    refine ⟨390423304044199096703245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 520564405392265462270993 390423304044199096703245)
                    ·
                      refine ⟨146408739016574661263717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390423304044199096703245 146408739016574661263717)
                      ·
                        rfl

theorem cell23_285130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_285130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285130 prefixEnd_285130 := by exact prefixLift 285130
  have htrace : WordTrace (prefixWord ++ tailWord_285130) baseStart_285130 baseEnd_285130 := by
    simpa [prefixWord, tailWord_285130, baseEnd_285130] using wordTrace_append hprefix tailTrace_285130
  have hstable : (prefixWord ++ tailWord_285130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285130).length < 2 ^ (prefixWord ++ tailWord_285130).sum := by decide
  have hdescent : baseEnd_285130 < baseStart_285130 := by decide
  rcases family_descends (prefixWord ++ tailWord_285130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285163 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 3, 5]
def baseStart_285163 : Nat := 118140960795 + 285163 * 2 ^ 59
def prefixEnd_285163 : Nat := 4983230072969 + 3 ^ 40 * 285163 * 2
def baseEnd_285163 : Nat := 48808561292724344050355

theorem tailTrace_285163 : CollatzResearch.WordTrace tailWord_285163 prefixEnd_285163 48808561292724344050355 := by
  unfold tailWord_285163
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400749065910627808148143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6933832710607085205432095 10400749065910627808148143)
  ·
    refine ⟨15601123598865941712222215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400749065910627808148143 15601123598865941712222215)
    ·
      refine ⟨23401685398298912568333323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15601123598865941712222215 23401685398298912568333323)
      ·
        refine ⟨35102528097448368852499985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23401685398298912568333323 35102528097448368852499985)
        ·
          refine ⟨26326896073086276639374989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35102528097448368852499985 26326896073086276639374989)
          ·
            refine ⟨9872586027407353739765621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26326896073086276639374989 9872586027407353739765621)
            ·
              refine ⟨925554940069439413103027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9872586027407353739765621 925554940069439413103027)
              ·
                refine ⟨1388332410104159119654541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925554940069439413103027 1388332410104159119654541)
                ·
                  refine ⟨520624653789059669870453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1388332410104159119654541 520624653789059669870453)
                  ·
                    refine ⟨48808561292724344050355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 520624653789059669870453 48808561292724344050355)
                    ·
                      rfl

theorem cell23_285163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 5].length) (baseStart_285163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285163 prefixEnd_285163 := by exact prefixLift 285163
  have htrace : WordTrace (prefixWord ++ tailWord_285163) baseStart_285163 baseEnd_285163 := by
    simpa [prefixWord, tailWord_285163, baseEnd_285163] using wordTrace_append hprefix tailTrace_285163
  have hstable : (prefixWord ++ tailWord_285163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285163).length < 2 ^ (prefixWord ++ tailWord_285163).sum := by decide
  have hdescent : baseEnd_285163 < baseStart_285163 := by decide
  rcases family_descends (prefixWord ++ tailWord_285163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285194 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_285194 : Nat := 118140960795 + 285194 * 2 ^ 59
def prefixEnd_285194 : Nat := 4983230072969 + 3 ^ 40 * 285194 * 2
def baseEnd_285194 : Nat := 146441601778462410863423

theorem tailTrace_285194 : CollatzResearch.WordTrace tailWord_285194 prefixEnd_285194 146441601778462410863423 := by
  unfold tailWord_285194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600469932199580025631659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6934586485865546735017757 2600469932199580025631659)
  ·
    refine ⟨3900704898299370038447489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600469932199580025631659 3900704898299370038447489)
    ·
      refine ⟨2925528673724527528835617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3900704898299370038447489 2925528673724527528835617)
      ·
        refine ⟨2194146505293395646626713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2925528673724527528835617 2194146505293395646626713)
        ·
          refine ⟨1645609878970046734970035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2194146505293395646626713 1645609878970046734970035)
          ·
            refine ⟨2468414818455070102455053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645609878970046734970035 2468414818455070102455053)
            ·
              refine ⟨925655556920651288420645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468414818455070102455053 925655556920651288420645)
              ·
                refine ⟨173560416922622116578871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 925655556920651288420645 173560416922622116578871)
                ·
                  refine ⟨260340625383933174868307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173560416922622116578871 260340625383933174868307)
                  ·
                    refine ⟨390510938075899762302461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260340625383933174868307 390510938075899762302461)
                    ·
                      refine ⟨146441601778462410863423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390510938075899762302461 146441601778462410863423)
                      ·
                        rfl

theorem cell23_285194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_285194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285194 prefixEnd_285194 := by exact prefixLift 285194
  have htrace : WordTrace (prefixWord ++ tailWord_285194) baseStart_285194 baseEnd_285194 := by
    simpa [prefixWord, tailWord_285194, baseEnd_285194] using wordTrace_append hprefix tailTrace_285194
  have hstable : (prefixWord ++ tailWord_285194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285194).length < 2 ^ (prefixWord ++ tailWord_285194).sum := by decide
  have hdescent : baseEnd_285194 < baseStart_285194 := by decide
  rcases family_descends (prefixWord ++ tailWord_285194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285203 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5]
def baseStart_285203 : Nat := 118140960795 + 285203 * 2 ^ 59
def prefixEnd_285203 : Nat := 4983230072969 + 3 ^ 40 * 285203 * 2
def baseEnd_285203 : Nat := 146446223104352875650881

theorem tailTrace_285203 : CollatzResearch.WordTrace tailWord_285203 prefixEnd_285203 146446223104352875650881 := by
  unfold tailWord_285203
  simp only [CollatzResearch.WordTrace]
  refine ⟨10402207985765714639604263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6934805323843809759736175 10402207985765714639604263)
  ·
    refine ⟨15603311978648571959406395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10402207985765714639604263 15603311978648571959406395)
    ·
      refine ⟨23404967967972857939109593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15603311978648571959406395 23404967967972857939109593)
      ·
        refine ⟨17553725975979643454332195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23404967967972857939109593 17553725975979643454332195)
        ·
          refine ⟨26330588963969465181498293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17553725975979643454332195 26330588963969465181498293)
          ·
            refine ⟨2468492715372137360765465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26330588963969465181498293 2468492715372137360765465)
            ·
              refine ⟨1851369536529103020574099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468492715372137360765465 1851369536529103020574099)
              ·
                refine ⟨2777054304793654530861149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851369536529103020574099 2777054304793654530861149)
                ·
                  refine ⟨1041395364297620449072931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2777054304793654530861149 1041395364297620449072931)
                  ·
                    refine ⟨1562093046446430673609397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1041395364297620449072931 1562093046446430673609397)
                    ·
                      refine ⟨146446223104352875650881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1562093046446430673609397 146446223104352875650881)
                      ·
                        rfl

theorem cell23_285203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_285203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285203 prefixEnd_285203 := by exact prefixLift 285203
  have htrace : WordTrace (prefixWord ++ tailWord_285203) baseStart_285203 baseEnd_285203 := by
    simpa [prefixWord, tailWord_285203, baseEnd_285203] using wordTrace_append hprefix tailTrace_285203
  have hstable : (prefixWord ++ tailWord_285203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285203).length < 2 ^ (prefixWord ++ tailWord_285203).sum := by decide
  have hdescent : baseEnd_285203 < baseStart_285203 := by decide
  rcases family_descends (prefixWord ++ tailWord_285203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285237 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_285237 : Nat := 118140960795 + 285237 * 2 ^ 59
def prefixEnd_285237 : Nat := 4983230072969 + 3 ^ 40 * 285237 * 2
def baseEnd_285237 : Nat := 146463681446605742625725

theorem tailTrace_285237 : CollatzResearch.WordTrace tailWord_285237 prefixEnd_285237 146463681446605742625725 := by
  unfold tailWord_285237
  simp only [CollatzResearch.WordTrace]
  refine ⟨10403448067642538446341965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6935632045095025630894643 10403448067642538446341965)
  ·
    refine ⟨3901293025365951917378237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10403448067642538446341965 3901293025365951917378237)
    ·
      refine ⟨1462984884512231969016839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3901293025365951917378237 1462984884512231969016839)
      ·
        refine ⟨2194477326768347953525259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462984884512231969016839 2194477326768347953525259)
        ·
          refine ⟨3291715990152521930287889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194477326768347953525259 3291715990152521930287889)
          ·
            refine ⟨2468786992614391447715917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291715990152521930287889 2468786992614391447715917)
            ·
              refine ⟨925795122230396792893469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468786992614391447715917 925795122230396792893469)
              ·
                refine ⟨347173170836398797335051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 925795122230396792893469 347173170836398797335051)
                ·
                  refine ⟨520759756254598196002577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347173170836398797335051 520759756254598196002577)
                  ·
                    refine ⟨390569817190948647001933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 520759756254598196002577 390569817190948647001933)
                    ·
                      refine ⟨146463681446605742625725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390569817190948647001933 146463681446605742625725)
                      ·
                        rfl

theorem cell23_285237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_285237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285237 prefixEnd_285237 := by exact prefixLift 285237
  have htrace : WordTrace (prefixWord ++ tailWord_285237) baseStart_285237 baseEnd_285237 := by
    simpa [prefixWord, tailWord_285237, baseEnd_285237] using wordTrace_append hprefix tailTrace_285237
  have hstable : (prefixWord ++ tailWord_285237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285237).length < 2 ^ (prefixWord ++ tailWord_285237).sum := by decide
  have hdescent : baseEnd_285237 < baseStart_285237 := by decide
  rcases family_descends (prefixWord ++ tailWord_285237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285244 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_285244 : Nat := 118140960795 + 285244 * 2 ^ 59
def prefixEnd_285244 : Nat := 4983230072969 + 3 ^ 40 * 285244 * 2
def baseEnd_285244 : Nat := 48822425270395738412731

theorem tailTrace_285244 : CollatzResearch.WordTrace tailWord_285244 prefixEnd_285244 48822425270395738412731 := by
  unfold tailWord_285244
  simp only [CollatzResearch.WordTrace]
  refine ⟨5201851689308589320923393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6935802252411452427897857 5201851689308589320923393)
  ·
    refine ⟨3901388766981441990692545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5201851689308589320923393 3901388766981441990692545)
    ·
      refine ⟨2926041575236081493019409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3901388766981441990692545 2926041575236081493019409)
      ·
        refine ⟨2194531181427061119764557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2926041575236081493019409 2194531181427061119764557)
        ·
          refine ⟨822949193035147919911709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2194531181427061119764557 822949193035147919911709)
          ·
            refine ⟨308605947388180469966891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 822949193035147919911709 308605947388180469966891)
            ·
              refine ⟨462908921082270704950337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308605947388180469966891 462908921082270704950337)
              ·
                refine ⟨347181690811703028712753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462908921082270704950337 347181690811703028712753)
                ·
                  refine ⟨260386268108777271534565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347181690811703028712753 260386268108777271534565)
                  ·
                    refine ⟨48822425270395738412731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 260386268108777271534565 48822425270395738412731)
                    ·
                      rfl

theorem cell23_285244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_285244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285244 prefixEnd_285244 := by exact prefixLift 285244
  have htrace : WordTrace (prefixWord ++ tailWord_285244) baseStart_285244 baseEnd_285244 := by
    simpa [prefixWord, tailWord_285244, baseEnd_285244] using wordTrace_append hprefix tailTrace_285244
  have hstable : (prefixWord ++ tailWord_285244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285244).length < 2 ^ (prefixWord ++ tailWord_285244).sum := by decide
  have hdescent : baseEnd_285244 < baseStart_285244 := by decide
  rcases family_descends (prefixWord ++ tailWord_285244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285254 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_285254 : Nat := 118140960795 + 285254 * 2 ^ 59
def prefixEnd_285254 : Nat := 4983230072969 + 3 ^ 40 * 285254 * 2
def baseEnd_285254 : Nat := 146472410617732176113147

theorem tailTrace_285254 : CollatzResearch.WordTrace tailWord_285254 prefixEnd_285254 146472410617732176113147 := by
  unfold tailWord_285254
  simp only [CollatzResearch.WordTrace]
  refine ⟨325127128393154698428463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6936045405720633566473877 325127128393154698428463)
  ·
    refine ⟨487690692589732047642695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 325127128393154698428463 487690692589732047642695)
    ·
      refine ⟨731536038884598071464043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487690692589732047642695 731536038884598071464043)
      ·
        refine ⟨1097304058326897107196065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731536038884598071464043 1097304058326897107196065)
        ·
          refine ⟨822978043745172830397049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1097304058326897107196065 822978043745172830397049)
          ·
            refine ⟨617233532808879622797787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 822978043745172830397049 617233532808879622797787)
            ·
              refine ⟨925850299213319434196681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617233532808879622797787 925850299213319434196681)
              ·
                refine ⟨694387724409989575647511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925850299213319434196681 694387724409989575647511)
                ·
                  refine ⟨1041581586614984363471267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694387724409989575647511 1041581586614984363471267)
                  ·
                    refine ⟨1562372379922476545206901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1041581586614984363471267 1562372379922476545206901)
                    ·
                      refine ⟨146472410617732176113147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1562372379922476545206901 146472410617732176113147)
                      ·
                        rfl

theorem cell23_285254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_285254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285254 prefixEnd_285254 := by exact prefixLift 285254
  have htrace : WordTrace (prefixWord ++ tailWord_285254) baseStart_285254 baseEnd_285254 := by
    simpa [prefixWord, tailWord_285254, baseEnd_285254] using wordTrace_append hprefix tailTrace_285254
  have hstable : (prefixWord ++ tailWord_285254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285254).length < 2 ^ (prefixWord ++ tailWord_285254).sum := by decide
  have hdescent : baseEnd_285254 < baseStart_285254 := by decide
  rcases family_descends (prefixWord ++ tailWord_285254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285261 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_285261 : Nat := 118140960795 + 285261 * 2 ^ 59
def prefixEnd_285261 : Nat := 4983230072969 + 3 ^ 40 * 285261 * 2
def baseEnd_285261 : Nat := 48825334994104549575205

theorem tailTrace_285261 : CollatzResearch.WordTrace tailWord_285261 prefixEnd_285261 48825334994104549575205 := by
  unfold tailWord_285261
  simp only [CollatzResearch.WordTrace]
  refine ⟨10404323419555590545215637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6936215613037060363477091 10404323419555590545215637)
  ·
    refine ⟨487702660291668306806983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10404323419555590545215637 487702660291668306806983)
    ·
      refine ⟨731553990437502460210475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487702660291668306806983 731553990437502460210475)
      ·
        refine ⟨1097330985656253690315713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731553990437502460210475 1097330985656253690315713)
        ·
          refine ⟨822998239242190267736785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1097330985656253690315713 822998239242190267736785)
          ·
            refine ⟨617248679431642700802589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 822998239242190267736785 617248679431642700802589)
            ·
              refine ⟨231468254786866012800971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 617248679431642700802589 231468254786866012800971)
              ·
                refine ⟨347202382180299019201457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231468254786866012800971 347202382180299019201457)
                ·
                  refine ⟨260401786635224264401093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347202382180299019201457 260401786635224264401093)
                  ·
                    refine ⟨48825334994104549575205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 260401786635224264401093 48825334994104549575205)
                    ·
                      rfl

theorem cell23_285261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_285261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285261 prefixEnd_285261 := by exact prefixLift 285261
  have htrace : WordTrace (prefixWord ++ tailWord_285261) baseStart_285261 baseEnd_285261 := by
    simpa [prefixWord, tailWord_285261, baseEnd_285261] using wordTrace_append hprefix tailTrace_285261
  have hstable : (prefixWord ++ tailWord_285261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285261).length < 2 ^ (prefixWord ++ tailWord_285261).sum := by decide
  have hdescent : baseEnd_285261 < baseStart_285261 := by decide
  rcases family_descends (prefixWord ++ tailWord_285261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285285 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 1, 2, 2]
def baseStart_285285 : Nat := 118140960795 + 285285 * 2 ^ 59
def prefixEnd_285285 : Nat := 4983230072969 + 3 ^ 40 * 285285 * 2
def baseEnd_285285 : Nat := 146488328518021554825505

theorem tailTrace_285285 : CollatzResearch.WordTrace tailWord_285285 prefixEnd_285285 146488328518021554825505 := by
  unfold tailWord_285285
  simp only [CollatzResearch.WordTrace]
  refine ⟨10405198771468642644089309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6936799180979095096059539 10405198771468642644089309)
  ·
    refine ⟨3901949539300740991533491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10405198771468642644089309 3901949539300740991533491)
    ·
      refine ⟨5852924308951111487300237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901949539300740991533491 5852924308951111487300237)
      ·
        refine ⟨2194846615856666807737589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5852924308951111487300237 2194846615856666807737589)
        ·
          refine ⟨205766870236562513225399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2194846615856666807737589 205766870236562513225399)
          ·
            refine ⟨308650305354843769838099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205766870236562513225399 308650305354843769838099)
            ·
              refine ⟨462975458032265654757149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308650305354843769838099 462975458032265654757149)
              ·
                refine ⟨173615796762099620533931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462975458032265654757149 173615796762099620533931)
                ·
                  refine ⟨260423695143149430800897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173615796762099620533931 260423695143149430800897)
                  ·
                    refine ⟨195317771357362073100673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260423695143149430800897 195317771357362073100673)
                    ·
                      refine ⟨146488328518021554825505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195317771357362073100673 146488328518021554825505)
                      ·
                        rfl

theorem cell23_285285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_285285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285285 prefixEnd_285285 := by exact prefixLift 285285
  have htrace : WordTrace (prefixWord ++ tailWord_285285) baseStart_285285 baseEnd_285285 := by
    simpa [prefixWord, tailWord_285285, baseEnd_285285] using wordTrace_append hprefix tailTrace_285285
  have hstable : (prefixWord ++ tailWord_285285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285285).length < 2 ^ (prefixWord ++ tailWord_285285).sum := by decide
  have hdescent : baseEnd_285285 < baseStart_285285 := by decide
  rcases family_descends (prefixWord ++ tailWord_285285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285358 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_285358 : Nat := 118140960795 + 285358 * 2 ^ 59
def prefixEnd_285358 : Nat := 4983230072969 + 3 ^ 40 * 285358 * 2
def baseEnd_285358 : Nat := 146525812605799769212669

theorem tailTrace_285358 : CollatzResearch.WordTrace tailWord_285358 prefixEnd_285358 146525812605799769212669 := by
  unfold tailWord_285358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300982662525522013937091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6938574200136117407664485 1300982662525522013937091)
  ·
    refine ⟨1951473993788283020905637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1300982662525522013937091 1951473993788283020905637)
    ·
      refine ⟨365901373835303066419807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1951473993788283020905637 365901373835303066419807)
      ·
        refine ⟨548852060752954599629711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365901373835303066419807 548852060752954599629711)
        ·
          refine ⟨823278091129431899444567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548852060752954599629711 823278091129431899444567)
          ·
            refine ⟨1234917136694147849166851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823278091129431899444567 1234917136694147849166851)
            ·
              refine ⟨1852375705041221773750277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234917136694147849166851 1852375705041221773750277)
              ·
                refine ⟨347320444695229082578177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1852375705041221773750277 347320444695229082578177)
                ·
                  refine ⟨260490333521421811933633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347320444695229082578177 260490333521421811933633)
                  ·
                    refine ⟨195367750141066358950225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260490333521421811933633 195367750141066358950225)
                    ·
                      refine ⟨146525812605799769212669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195367750141066358950225 146525812605799769212669)
                      ·
                        rfl

theorem cell23_285358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_285358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285358 prefixEnd_285358 := by exact prefixLift 285358
  have htrace : WordTrace (prefixWord ++ tailWord_285358) baseStart_285358 baseEnd_285358 := by
    simpa [prefixWord, tailWord_285358, baseEnd_285358] using wordTrace_append hprefix tailTrace_285358
  have hstable : (prefixWord ++ tailWord_285358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285358).length < 2 ^ (prefixWord ++ tailWord_285358).sum := by decide
  have hdescent : baseEnd_285358 < baseStart_285358 := by decide
  rcases family_descends (prefixWord ++ tailWord_285358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285370 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_285370 : Nat := 118140960795 + 285370 * 2 ^ 59
def prefixEnd_285370 : Nat := 4983230072969 + 3 ^ 40 * 285370 * 2
def baseEnd_285370 : Nat := 146531974373653722262613

theorem tailTrace_285370 : CollatzResearch.WordTrace tailWord_285370 prefixEnd_285370 146531974373653722262613 := by
  unfold tailWord_285370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602074744040175540233391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6938865984107134773955709 2602074744040175540233391)
  ·
    refine ⟨3903112116060263310350087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602074744040175540233391 3903112116060263310350087)
    ·
      refine ⟨5854668174090394965525131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3903112116060263310350087 5854668174090394965525131)
      ·
        refine ⟨8782002261135592448287697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854668174090394965525131 8782002261135592448287697)
        ·
          refine ⟨6586501695851694336215773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8782002261135592448287697 6586501695851694336215773)
          ·
            refine ⟨2469938135944385376080915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6586501695851694336215773 2469938135944385376080915)
            ·
              refine ⟨3704907203916578064121373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469938135944385376080915 3704907203916578064121373)
              ·
                refine ⟨1389340201468716774045515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3704907203916578064121373 1389340201468716774045515)
                ·
                  refine ⟨2084010302203075161068273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389340201468716774045515 2084010302203075161068273)
                  ·
                    refine ⟨1563007726652306370801205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2084010302203075161068273 1563007726652306370801205)
                    ·
                      refine ⟨146531974373653722262613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1563007726652306370801205 146531974373653722262613)
                      ·
                        rfl

theorem cell23_285370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_285370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285370 prefixEnd_285370 := by exact prefixLift 285370
  have htrace : WordTrace (prefixWord ++ tailWord_285370) baseStart_285370 baseEnd_285370 := by
    simpa [prefixWord, tailWord_285370, baseEnd_285370] using wordTrace_append hprefix tailTrace_285370
  have hstable : (prefixWord ++ tailWord_285370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285370).length < 2 ^ (prefixWord ++ tailWord_285370).sum := by decide
  have hdescent : baseEnd_285370 < baseStart_285370 := by decide
  rcases family_descends (prefixWord ++ tailWord_285370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285417 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_285417 : Nat := 118140960795 + 285417 * 2 ^ 59
def prefixEnd_285417 : Nat := 4983230072969 + 3 ^ 40 * 285417 * 2
def baseEnd_285417 : Nat := 146556107964415038374897

theorem tailTrace_285417 : CollatzResearch.WordTrace tailWord_285417 prefixEnd_285417 146556107964415038374897 := by
  unfold tailWord_285417
  simp only [CollatzResearch.WordTrace]
  refine ⟨10410013206990429187894505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6940008804660286125263003 10410013206990429187894505)
  ·
    refine ⟨7807509905242821890920879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10410013206990429187894505 7807509905242821890920879)
    ·
      refine ⟨11711264857864232836381319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807509905242821890920879 11711264857864232836381319)
      ·
        refine ⟨17566897286796349254571979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11711264857864232836381319 17566897286796349254571979)
        ·
          refine ⟨26350345930194523881857969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17566897286796349254571979 26350345930194523881857969)
          ·
            refine ⟨19762759447645892911393477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26350345930194523881857969 19762759447645892911393477)
            ·
              refine ⟨3705517396433604920886277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19762759447645892911393477 3705517396433604920886277)
              ·
                refine ⟨694784511831300922666177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3705517396433604920886277 694784511831300922666177)
                ·
                  refine ⟨521088383873475691999633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694784511831300922666177 521088383873475691999633)
                  ·
                    refine ⟨390816287905106768999725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 521088383873475691999633 390816287905106768999725)
                    ·
                      refine ⟨146556107964415038374897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390816287905106768999725 146556107964415038374897)
                      ·
                        rfl

theorem cell23_285417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_285417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285417 prefixEnd_285417 := by exact prefixLift 285417
  have htrace : WordTrace (prefixWord ++ tailWord_285417) baseStart_285417 baseEnd_285417 := by
    simpa [prefixWord, tailWord_285417, baseEnd_285417] using wordTrace_append hprefix tailTrace_285417
  have hstable : (prefixWord ++ tailWord_285417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285417).length < 2 ^ (prefixWord ++ tailWord_285417).sum := by decide
  have hdescent : baseEnd_285417 < baseStart_285417 := by decide
  rcases family_descends (prefixWord ++ tailWord_285417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285424 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 1, 4]
def baseStart_285424 : Nat := 118140960795 + 285424 * 2 ^ 59
def prefixEnd_285424 : Nat := 4983230072969 + 3 ^ 40 * 285424 * 2
def baseEnd_285424 : Nat := 48853234109665503662455

theorem tailTrace_285424 : CollatzResearch.WordTrace tailWord_285424 prefixEnd_285424 48853234109665503662455 := by
  unfold tailWord_285424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205134258982534691699663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6940179011976712922266217 5205134258982534691699663)
  ·
    refine ⟨7807701388473802037549495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5205134258982534691699663 7807701388473802037549495)
    ·
      refine ⟨11711552082710703056324243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807701388473802037549495 11711552082710703056324243)
      ·
        refine ⟨17567328124066054584486365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11711552082710703056324243 17567328124066054584486365)
        ·
          refine ⟨6587748046524770469182387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17567328124066054584486365 6587748046524770469182387)
          ·
            refine ⟨9881622069787155703773581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6587748046524770469182387 9881622069787155703773581)
            ·
              refine ⟨3705608276170183388915093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9881622069787155703773581 3705608276170183388915093)
              ·
                refine ⟨173700387945477346355395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3705608276170183388915093 173700387945477346355395)
                ·
                  refine ⟨260550581918216019533093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173700387945477346355395 260550581918216019533093)
                  ·
                    refine ⟨48853234109665503662455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 260550581918216019533093 48853234109665503662455)
                    ·
                      rfl

theorem cell23_285424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 4].length) (baseStart_285424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285424 prefixEnd_285424 := by exact prefixLift 285424
  have htrace : WordTrace (prefixWord ++ tailWord_285424) baseStart_285424 baseEnd_285424 := by
    simpa [prefixWord, tailWord_285424, baseEnd_285424] using wordTrace_append hprefix tailTrace_285424
  have hstable : (prefixWord ++ tailWord_285424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285424).length < 2 ^ (prefixWord ++ tailWord_285424).sum := by decide
  have hdescent : baseEnd_285424 < baseStart_285424 := by decide
  rcases family_descends (prefixWord ++ tailWord_285424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285532 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_285532 : Nat := 118140960795 + 285532 * 2 ^ 59
def prefixEnd_285532 : Nat := 4983230072969 + 3 ^ 40 * 285532 * 2
def baseEnd_285532 : Nat := 146615158239682088436869

theorem tailTrace_285532 : CollatzResearch.WordTrace tailWord_285532 prefixEnd_285532 146615158239682088436869 := by
  unfold tailWord_285532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207103800786901914165425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6942805067715869218887233 5207103800786901914165425)
  ·
    refine ⟨3905327850590176435624069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5207103800786901914165425 3905327850590176435624069)
    ·
      refine ⟨732248971985658081679513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3905327850590176435624069 732248971985658081679513)
      ·
        refine ⟨549186728989243561259635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732248971985658081679513 549186728989243561259635)
        ·
          refine ⟨823780093483865341889453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549186728989243561259635 823780093483865341889453)
          ·
            refine ⟨308917535056449503208545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 823780093483865341889453 308917535056449503208545)
            ·
              refine ⟨231688151292337127406409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308917535056449503208545 231688151292337127406409)
              ·
                refine ⟨173766113469252845554807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231688151292337127406409 173766113469252845554807)
                ·
                  refine ⟨260649170203879268332211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173766113469252845554807 260649170203879268332211)
                  ·
                    refine ⟨390973755305818902498317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260649170203879268332211 390973755305818902498317)
                    ·
                      refine ⟨146615158239682088436869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 390973755305818902498317 146615158239682088436869)
                      ·
                        rfl

theorem cell23_285532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_285532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285532 prefixEnd_285532 := by exact prefixLift 285532
  have htrace : WordTrace (prefixWord ++ tailWord_285532) baseStart_285532 baseEnd_285532 := by
    simpa [prefixWord, tailWord_285532, baseEnd_285532] using wordTrace_append hprefix tailTrace_285532
  have hstable : (prefixWord ++ tailWord_285532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285532).length < 2 ^ (prefixWord ++ tailWord_285532).sum := by decide
  have hdescent : baseEnd_285532 < baseStart_285532 := by decide
  rcases family_descends (prefixWord ++ tailWord_285532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285544 : List Nat := [2, 1, 4, 2, 1, 4, 1, 8]
def baseStart_285544 : Nat := 118140960795 + 285544 * 2 ^ 59
def prefixEnd_285544 : Nat := 4983230072969 + 3 ^ 40 * 285544 * 2
def baseEnd_285544 : Nat := 5430419259538371906919

theorem tailTrace_285544 : CollatzResearch.WordTrace tailWord_285544 prefixEnd_285544 5430419259538371906919 := by
  unfold tailWord_285544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207322638765164938883843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6943096851686886585178457 5207322638765164938883843)
  ·
    refine ⟨7810983958147747408325765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5207322638765164938883843 7810983958147747408325765)
    ·
      refine ⟨1464559492152702639061081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7810983958147747408325765 1464559492152702639061081)
      ·
        refine ⟨1098419619114526979295811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1464559492152702639061081 1098419619114526979295811)
        ·
          refine ⟨1647629428671790468943717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098419619114526979295811 1647629428671790468943717)
          ·
            refine ⟨308930517875960712926947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1647629428671790468943717 308930517875960712926947)
            ·
              refine ⟨463395776813941069390421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308930517875960712926947 463395776813941069390421)
              ·
                refine ⟨5430419259538371906919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 463395776813941069390421 5430419259538371906919)
                ·
                  rfl

theorem cell23_285544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 8].length) (baseStart_285544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285544 prefixEnd_285544 := by exact prefixLift 285544
  have htrace : WordTrace (prefixWord ++ tailWord_285544) baseStart_285544 baseEnd_285544 := by
    simpa [prefixWord, tailWord_285544, baseEnd_285544] using wordTrace_append hprefix tailTrace_285544
  have hstable : (prefixWord ++ tailWord_285544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285544).length < 2 ^ (prefixWord ++ tailWord_285544).sum := by decide
  have hdescent : baseEnd_285544 < baseStart_285544 := by decide
  rcases family_descends (prefixWord ++ tailWord_285544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285554 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_285554 : Nat := 118140960795 + 285554 * 2 ^ 59
def prefixEnd_285554 : Nat := 4983230072969 + 3 ^ 40 * 285554 * 2
def baseEnd_285554 : Nat := 146626454814081002361767

theorem tailTrace_285554 : CollatzResearch.WordTrace tailWord_285554 prefixEnd_285554 146626454814081002361767 := by
  unfold tailWord_285554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603752501873525396407929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6943340004996067723754477 2603752501873525396407929)
  ·
    refine ⟨1952814376405144047305947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2603752501873525396407929 1952814376405144047305947)
    ·
      refine ⟨2929221564607716070958921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952814376405144047305947 2929221564607716070958921)
      ·
        refine ⟨2196916173455787053219191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929221564607716070958921 2196916173455787053219191)
        ·
          refine ⟨3295374260183680579828787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196916173455787053219191 3295374260183680579828787)
          ·
            refine ⟨4943061390275520869743181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295374260183680579828787 4943061390275520869743181)
            ·
              refine ⟨1853648021353320326153693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4943061390275520869743181 1853648021353320326153693)
              ·
                refine ⟨695118008007495122307635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1853648021353320326153693 695118008007495122307635)
                ·
                  refine ⟨1042677012011242683461453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695118008007495122307635 1042677012011242683461453)
                  ·
                    refine ⟨391003879504216006298045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042677012011242683461453 391003879504216006298045)
                    ·
                      refine ⟨146626454814081002361767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 391003879504216006298045 146626454814081002361767)
                      ·
                        rfl

theorem cell23_285554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_285554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285554 prefixEnd_285554 := by exact prefixLift 285554
  have htrace : WordTrace (prefixWord ++ tailWord_285554) baseStart_285554 baseEnd_285554 := by
    simpa [prefixWord, tailWord_285554, baseEnd_285554] using wordTrace_append hprefix tailTrace_285554
  have hstable : (prefixWord ++ tailWord_285554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285554).length < 2 ^ (prefixWord ++ tailWord_285554).sum := by decide
  have hdescent : baseEnd_285554 < baseStart_285554 := by decide
  rcases family_descends (prefixWord ++ tailWord_285554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285681 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 2, 5]
def baseStart_285681 : Nat := 118140960795 + 285681 * 2 ^ 59
def prefixEnd_285681 : Nat := 4983230072969 + 3 ^ 40 * 285681 * 2
def baseEnd_285681 : Nat := 48897222285734001824561

theorem tailTrace_285681 : CollatzResearch.WordTrace tailWord_285681 prefixEnd_285681 48897222285734001824561 := by
  unfold tailWord_285681
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419642078034002275504897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6946428052022668183669931 10419642078034002275504897)
  ·
    refine ⟨7814731558525501706628673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10419642078034002275504897 7814731558525501706628673)
    ·
      refine ⟨5861048668894126279971505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7814731558525501706628673 5861048668894126279971505)
      ·
        refine ⟨4395786501670594709978629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5861048668894126279971505 4395786501670594709978629)
        ·
          refine ⟨824209969063236508120993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4395786501670594709978629 824209969063236508120993)
          ·
            refine ⟨618157476797427381090745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 824209969063236508120993 618157476797427381090745)
            ·
              refine ⟨463618107598070535818059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618157476797427381090745 463618107598070535818059)
              ·
                refine ⟨695427161397105803727089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463618107598070535818059 695427161397105803727089)
                ·
                  refine ⟨521570371047829352795317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695427161397105803727089 521570371047829352795317)
                  ·
                    refine ⟨48897222285734001824561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 521570371047829352795317 48897222285734001824561)
                    ·
                      rfl

theorem cell23_285681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_285681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285681 prefixEnd_285681 := by exact prefixLift 285681
  have htrace : WordTrace (prefixWord ++ tailWord_285681) baseStart_285681 baseEnd_285681 := by
    simpa [prefixWord, tailWord_285681, baseEnd_285681] using wordTrace_append hprefix tailTrace_285681
  have hstable : (prefixWord ++ tailWord_285681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285681).length < 2 ^ (prefixWord ++ tailWord_285681).sum := by decide
  have hdescent : baseEnd_285681 < baseStart_285681 := by decide
  rcases family_descends (prefixWord ++ tailWord_285681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285687 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_285687 : Nat := 118140960795 + 285687 * 2 ^ 59
def prefixEnd_285687 : Nat := 4983230072969 + 3 ^ 40 * 285687 * 2
def baseEnd_285687 : Nat := 146694747741128981998655

theorem tailTrace_285687 : CollatzResearch.WordTrace tailWord_285687 prefixEnd_285687 146694747741128981998655 := by
  unfold tailWord_285687
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419860916012265300223315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6946573944008176866815543 10419860916012265300223315)
  ·
    refine ⟨15629791374018397950334973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10419860916012265300223315 15629791374018397950334973)
    ·
      refine ⟨5861171765256899231375615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15629791374018397950334973 5861171765256899231375615)
      ·
        refine ⟨8791757647885348847063423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861171765256899231375615 8791757647885348847063423)
        ·
          refine ⟨13187636471828023270595135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8791757647885348847063423 13187636471828023270595135)
          ·
            refine ⟨19781454707742034905892703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13187636471828023270595135 19781454707742034905892703)
            ·
              refine ⟨29672182061613052358839055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19781454707742034905892703 29672182061613052358839055)
              ·
                refine ⟨44508273092419578538258583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29672182061613052358839055 44508273092419578538258583)
                ·
                  refine ⟨66762409638629367807387875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44508273092419578538258583 66762409638629367807387875)
                  ·
                    refine ⟨100143614457944051711081813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66762409638629367807387875 100143614457944051711081813)
                    ·
                      refine ⟨146694747741128981998655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 100143614457944051711081813 146694747741128981998655)
                      ·
                        rfl

theorem cell23_285687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_285687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285687 prefixEnd_285687 := by exact prefixLift 285687
  have htrace : WordTrace (prefixWord ++ tailWord_285687) baseStart_285687 baseEnd_285687 := by
    simpa [prefixWord, tailWord_285687, baseEnd_285687] using wordTrace_append hprefix tailTrace_285687
  have hstable : (prefixWord ++ tailWord_285687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285687).length < 2 ^ (prefixWord ++ tailWord_285687).sum := by decide
  have hdescent : baseEnd_285687 < baseStart_285687 := by decide
  rcases family_descends (prefixWord ++ tailWord_285687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285701 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 2, 4, 2]
def baseStart_285701 : Nat := 118140960795 + 285701 * 2 ^ 59
def prefixEnd_285701 : Nat := 4983230072969 + 3 ^ 40 * 285701 * 2
def baseEnd_285701 : Nat := 146701936470291927223591

theorem tailTrace_285701 : CollatzResearch.WordTrace tailWord_285701 prefixEnd_285701 146701936470291927223591 := by
  unfold tailWord_285701
  simp only [CollatzResearch.WordTrace]
  refine ⟨10420371537961545691232957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6946914358641030460821971 10420371537961545691232957)
  ·
    refine ⟨3907639326735579634212359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10420371537961545691232957 3907639326735579634212359)
    ·
      refine ⟨5861458990103369451318539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3907639326735579634212359 5861458990103369451318539)
      ·
        refine ⟨8792188485155054176977809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861458990103369451318539 8792188485155054176977809)
        ·
          refine ⟨6594141363866290632733357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8792188485155054176977809 6594141363866290632733357)
          ·
            refine ⟨2472803011449858987275009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6594141363866290632733357 2472803011449858987275009)
            ·
              refine ⟨1854602258587394240456257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472803011449858987275009 1854602258587394240456257)
              ·
                refine ⟨1390951693940545680342193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854602258587394240456257 1390951693940545680342193)
                ·
                  refine ⟨1043213770455409260256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1390951693940545680342193 1043213770455409260256645)
                  ·
                    refine ⟨195602581960389236298121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1043213770455409260256645 195602581960389236298121)
                    ·
                      refine ⟨146701936470291927223591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195602581960389236298121 146701936470291927223591)
                      ·
                        rfl

theorem cell23_285701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_285701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285701 prefixEnd_285701 := by exact prefixLift 285701
  have htrace : WordTrace (prefixWord ++ tailWord_285701) baseStart_285701 baseEnd_285701 := by
    simpa [prefixWord, tailWord_285701, baseEnd_285701] using wordTrace_append hprefix tailTrace_285701
  have hstable : (prefixWord ++ tailWord_285701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285701).length < 2 ^ (prefixWord ++ tailWord_285701).sum := by decide
  have hdescent : baseEnd_285701 < baseStart_285701 := by decide
  rcases family_descends (prefixWord ++ tailWord_285701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285735 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_285735 : Nat := 118140960795 + 285735 * 2 ^ 59
def prefixEnd_285735 : Nat := 4983230072969 + 3 ^ 40 * 285735 * 2
def baseEnd_285735 : Nat := 146719394812544794198435

theorem tailTrace_285735 : CollatzResearch.WordTrace tailWord_285735 prefixEnd_285735 146719394812544794198435 := by
  unfold tailWord_285735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421611619838369497970659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6947741079892246331980439 10421611619838369497970659)
  ·
    refine ⟨15632417429757554246955989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10421611619838369497970659 15632417429757554246955989)
    ·
      refine ⟨366384783509942677663031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15632417429757554246955989 366384783509942677663031)
      ·
        refine ⟨549577175264914016494547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366384783509942677663031 549577175264914016494547)
        ·
          refine ⟨824365762897371024741821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549577175264914016494547 824365762897371024741821)
          ·
            refine ⟨309137161086514134278183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 824365762897371024741821 309137161086514134278183)
            ·
              refine ⟨463705741629771201417275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309137161086514134278183 463705741629771201417275)
              ·
                refine ⟨695558612444656802125913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463705741629771201417275 695558612444656802125913)
                ·
                  refine ⟨521668959333492601594435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695558612444656802125913 521668959333492601594435)
                  ·
                    refine ⟨782503439000238902391653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 521668959333492601594435 782503439000238902391653)
                    ·
                      refine ⟨146719394812544794198435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 782503439000238902391653 146719394812544794198435)
                      ·
                        rfl

theorem cell23_285735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_285735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285735 prefixEnd_285735 := by exact prefixLift 285735
  have htrace : WordTrace (prefixWord ++ tailWord_285735) baseStart_285735 baseEnd_285735 := by
    simpa [prefixWord, tailWord_285735, baseEnd_285735] using wordTrace_append hprefix tailTrace_285735
  have hstable : (prefixWord ++ tailWord_285735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285735).length < 2 ^ (prefixWord ++ tailWord_285735).sum := by decide
  have hdescent : baseEnd_285735 < baseStart_285735 := by decide
  rcases family_descends (prefixWord ++ tailWord_285735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285738 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_285738 : Nat := 118140960795 + 285738 * 2 ^ 59
def prefixEnd_285738 : Nat := 4983230072969 + 3 ^ 40 * 285738 * 2
def baseEnd_285738 : Nat := 146720935254508282460921

theorem tailTrace_285738 : CollatzResearch.WordTrace tailWord_285738 prefixEnd_285738 146720935254508282460921 := by
  unfold tailWord_285738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605430259706875252582467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6947814025885000673553245 2605430259706875252582467)
  ·
    refine ⟨3908145389560312878873701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2605430259706875252582467 3908145389560312878873701)
    ·
      refine ⟨732777260542558664788819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3908145389560312878873701 732777260542558664788819)
      ·
        refine ⟨1099165890813837997183229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732777260542558664788819 1099165890813837997183229)
        ·
          refine ⟨412187209055189248943711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1099165890813837997183229 412187209055189248943711)
          ·
            refine ⟨618280813582783873415567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412187209055189248943711 618280813582783873415567)
            ·
              refine ⟨927421220374175810123351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618280813582783873415567 927421220374175810123351)
              ·
                refine ⟨1391131830561263715185027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927421220374175810123351 1391131830561263715185027)
                ·
                  refine ⟨2086697745841895572777541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391131830561263715185027 2086697745841895572777541)
                  ·
                    refine ⟨391255827345355419895789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086697745841895572777541 391255827345355419895789)
                    ·
                      refine ⟨146720935254508282460921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 391255827345355419895789 146720935254508282460921)
                      ·
                        rfl

theorem cell23_285738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_285738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285738 prefixEnd_285738 := by exact prefixLift 285738
  have htrace : WordTrace (prefixWord ++ tailWord_285738) baseStart_285738 baseEnd_285738 := by
    simpa [prefixWord, tailWord_285738, baseEnd_285738] using wordTrace_append hprefix tailTrace_285738
  have hstable : (prefixWord ++ tailWord_285738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285738).length < 2 ^ (prefixWord ++ tailWord_285738).sum := by decide
  have hdescent : baseEnd_285738 < baseStart_285738 := by decide
  rcases family_descends (prefixWord ++ tailWord_285738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285751 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_285751 : Nat := 118140960795 + 285751 * 2 ^ 59
def prefixEnd_285751 : Nat := 4983230072969 + 3 ^ 40 * 285751 * 2
def baseEnd_285751 : Nat := 146727610503016731598361

theorem tailTrace_285751 : CollatzResearch.WordTrace tailWord_285751 prefixEnd_285751 146727610503016731598361 := by
  unfold tailWord_285751
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422195187780404230553107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6948130125186936153702071 10422195187780404230553107)
  ·
    refine ⟨15633292781670606345829661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10422195187780404230553107 15633292781670606345829661)
    ·
      refine ⟨5862484793126477379686123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15633292781670606345829661 5862484793126477379686123)
      ·
        refine ⟨8793727189689716069529185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5862484793126477379686123 8793727189689716069529185)
        ·
          refine ⟨6595295392267287052146889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8793727189689716069529185 6595295392267287052146889)
          ·
            refine ⟨4946471544200465289110167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6595295392267287052146889 4946471544200465289110167)
            ·
              refine ⟨7419707316300697933665251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946471544200465289110167 7419707316300697933665251)
              ·
                refine ⟨11129560974451046900497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419707316300697933665251 11129560974451046900497877)
                ·
                  refine ⟨260849085338696411730419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11129560974451046900497877 260849085338696411730419)
                  ·
                    refine ⟨391273628008044617595629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260849085338696411730419 391273628008044617595629)
                    ·
                      refine ⟨146727610503016731598361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 391273628008044617595629 146727610503016731598361)
                      ·
                        rfl

theorem cell23_285751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_285751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285751 prefixEnd_285751 := by exact prefixLift 285751
  have htrace : WordTrace (prefixWord ++ tailWord_285751) baseStart_285751 baseEnd_285751 := by
    simpa [prefixWord, tailWord_285751, baseEnd_285751] using wordTrace_append hprefix tailTrace_285751
  have hstable : (prefixWord ++ tailWord_285751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285751).length < 2 ^ (prefixWord ++ tailWord_285751).sum := by decide
  have hdescent : baseEnd_285751 < baseStart_285751 := by decide
  rcases family_descends (prefixWord ++ tailWord_285751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285758 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_285758 : Nat := 118140960795 + 285758 * 2 ^ 59
def prefixEnd_285758 : Nat := 4983230072969 + 3 ^ 40 * 285758 * 2
def baseEnd_285758 : Nat := 16303467207510911578981

theorem tailTrace_285758 : CollatzResearch.WordTrace tailWord_285758 prefixEnd_285758 16303467207510911578981 := by
  unfold tailWord_285758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302806312344380553257241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6948300332503362950705285 1302806312344380553257241)
  ·
    refine ⟨977104734258285414942931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1302806312344380553257241 977104734258285414942931)
    ·
      refine ⟨1465657101387428122414397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977104734258285414942931 1465657101387428122414397)
      ·
        refine ⟨549621413020285545905399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1465657101387428122414397 549621413020285545905399)
        ·
          refine ⟨824432119530428318858099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549621413020285545905399 824432119530428318858099)
          ·
            refine ⟨1236648179295642478287149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824432119530428318858099 1236648179295642478287149)
            ·
              refine ⟨463743067235865929357681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236648179295642478287149 463743067235865929357681)
              ·
                refine ⟨347807300426899447018261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463743067235865929357681 347807300426899447018261)
                ·
                  refine ⟨16303467207510911578981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 347807300426899447018261 16303467207510911578981)
                  ·
                    rfl

theorem cell23_285758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_285758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285758 prefixEnd_285758 := by exact prefixLift 285758
  have htrace : WordTrace (prefixWord ++ tailWord_285758) baseStart_285758 baseEnd_285758 := by
    simpa [prefixWord, tailWord_285758, baseEnd_285758] using wordTrace_append hprefix tailTrace_285758
  have hstable : (prefixWord ++ tailWord_285758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285758).length < 2 ^ (prefixWord ++ tailWord_285758).sum := by decide
  have hdescent : baseEnd_285758 < baseStart_285758 := by decide
  rcases family_descends (prefixWord ++ tailWord_285758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285768 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_285768 : Nat := 118140960795 + 285768 * 2 ^ 59
def prefixEnd_285768 : Nat := 4983230072969 + 3 ^ 40 * 285768 * 2
def baseEnd_285768 : Nat := 146736339674143165085783

theorem tailTrace_285768 : CollatzResearch.WordTrace tailWord_285768 prefixEnd_285768 146736339674143165085783 := by
  unfold tailWord_285768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211407614359408066960979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6948543485812544089281305 5211407614359408066960979)
  ·
    refine ⟨7817111421539112100441469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211407614359408066960979 7817111421539112100441469)
    ·
      refine ⟨2931416783077167037665551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7817111421539112100441469 2931416783077167037665551)
      ·
        refine ⟨4397125174615750556498327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931416783077167037665551 4397125174615750556498327)
        ·
          refine ⟨6595687761923625834747491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397125174615750556498327 6595687761923625834747491)
          ·
            refine ⟨9893531642885438752121237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595687761923625834747491 9893531642885438752121237)
            ·
              refine ⟨463759295760254941505683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9893531642885438752121237 463759295760254941505683)
              ·
                refine ⟨695638943640382412258525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463759295760254941505683 695638943640382412258525)
                ·
                  refine ⟨260864603865143404596947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695638943640382412258525 260864603865143404596947)
                  ·
                    refine ⟨391296905797715106895421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260864603865143404596947 391296905797715106895421)
                    ·
                      refine ⟨146736339674143165085783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 391296905797715106895421 146736339674143165085783)
                      ·
                        rfl

theorem cell23_285768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_285768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285768 prefixEnd_285768 := by exact prefixLift 285768
  have htrace : WordTrace (prefixWord ++ tailWord_285768) baseStart_285768 baseEnd_285768 := by
    simpa [prefixWord, tailWord_285768, baseEnd_285768] using wordTrace_append hprefix tailTrace_285768
  have hstable : (prefixWord ++ tailWord_285768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285768).length < 2 ^ (prefixWord ++ tailWord_285768).sum := by decide
  have hdescent : baseEnd_285768 < baseStart_285768 := by decide
  rcases family_descends (prefixWord ++ tailWord_285768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285778 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_285778 : Nat := 118140960795 + 285778 * 2 ^ 59
def prefixEnd_285778 : Nat := 4983230072969 + 3 ^ 40 * 285778 * 2
def baseEnd_285778 : Nat := 146741474480688125960737

theorem tailTrace_285778 : CollatzResearch.WordTrace tailWord_285778 prefixEnd_285778 146741474480688125960737 := by
  unfold tailWord_285778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605794989670646960446497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6948786639121725227857325 2605794989670646960446497)
  ·
    refine ⟨1954346242252985220334873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2605794989670646960446497 1954346242252985220334873)
    ·
      refine ⟨1465759681689738915251155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1954346242252985220334873 1465759681689738915251155)
      ·
        refine ⟨2198639522534608372876733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465759681689738915251155 2198639522534608372876733)
        ·
          refine ⟨824489820950478139828775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2198639522534608372876733 824489820950478139828775)
          ·
            refine ⟨1236734731425717209743163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824489820950478139828775 1236734731425717209743163)
            ·
              refine ⟨1855102097138575814614745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236734731425717209743163 1855102097138575814614745)
              ·
                refine ⟨1391326572853931860961059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855102097138575814614745 1391326572853931860961059)
                ·
                  refine ⟨2086989859280897791441589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391326572853931860961059 2086989859280897791441589)
                  ·
                    refine ⟨195655299307584167947649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2086989859280897791441589 195655299307584167947649)
                    ·
                      refine ⟨146741474480688125960737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195655299307584167947649 146741474480688125960737)
                      ·
                        rfl

theorem cell23_285778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_285778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285778 prefixEnd_285778 := by exact prefixLift 285778
  have htrace : WordTrace (prefixWord ++ tailWord_285778) baseStart_285778 baseEnd_285778 := by
    simpa [prefixWord, tailWord_285778, baseEnd_285778] using wordTrace_append hprefix tailTrace_285778
  have hstable : (prefixWord ++ tailWord_285778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285778).length < 2 ^ (prefixWord ++ tailWord_285778).sum := by decide
  have hdescent : baseEnd_285778 < baseStart_285778 := by decide
  rcases family_descends (prefixWord ++ tailWord_285778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285788 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_285788 : Nat := 118140960795 + 285788 * 2 ^ 59
def prefixEnd_285788 : Nat := 4983230072969 + 3 ^ 40 * 285788 * 2
def baseEnd_285788 : Nat := 48915536429077695611897

theorem tailTrace_285788 : CollatzResearch.WordTrace tailWord_285788 prefixEnd_285788 48915536429077695611897 := by
  unfold tailWord_285788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211772344323179774825009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6949029792430906366433345 5211772344323179774825009)
  ·
    refine ⟨3908829258242384831118757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5211772344323179774825009 3908829258242384831118757)
    ·
      refine ⟨732905485920447155834767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3908829258242384831118757 732905485920447155834767)
      ·
        refine ⟨1099358228880670733752151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732905485920447155834767 1099358228880670733752151)
        ·
          refine ⟨1649037343321006100628227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099358228880670733752151 1649037343321006100628227)
          ·
            refine ⟨2473556014981509150942341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649037343321006100628227 2473556014981509150942341)
            ·
              refine ⟨463791752809032965801689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2473556014981509150942341 463791752809032965801689)
              ·
                refine ⟨347843814606774724351267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463791752809032965801689 347843814606774724351267)
                ·
                  refine ⟨521765721910162086526901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347843814606774724351267 521765721910162086526901)
                  ·
                    refine ⟨48915536429077695611897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 521765721910162086526901 48915536429077695611897)
                    ·
                      rfl

theorem cell23_285788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_285788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285788 prefixEnd_285788 := by exact prefixLift 285788
  have htrace : WordTrace (prefixWord ++ tailWord_285788) baseStart_285788 baseEnd_285788 := by
    simpa [prefixWord, tailWord_285788, baseEnd_285788] using wordTrace_append hprefix tailTrace_285788
  have hstable : (prefixWord ++ tailWord_285788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285788).length < 2 ^ (prefixWord ++ tailWord_285788).sum := by decide
  have hdescent : baseEnd_285788 < baseStart_285788 := by decide
  rcases family_descends (prefixWord ++ tailWord_285788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285791 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 6, 2]
def baseStart_285791 : Nat := 118140960795 + 285791 * 2 ^ 59
def prefixEnd_285791 : Nat := 4983230072969 + 3 ^ 40 * 285791 * 2
def baseEnd_285791 : Nat := 146748149729196575098177

theorem tailTrace_285791 : CollatzResearch.WordTrace tailWord_285791 prefixEnd_285791 146748149729196575098177 := by
  unfold tailWord_285791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10423654107635491062009227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6949102738423660708006151 10423654107635491062009227)
  ·
    refine ⟨15635481161453236593013841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10423654107635491062009227 15635481161453236593013841)
    ·
      refine ⟨11726610871089927444760381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15635481161453236593013841 11726610871089927444760381)
      ·
        refine ⟨4397479076658722791785143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11726610871089927444760381 4397479076658722791785143)
        ·
          refine ⟨6596218614988084187677715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397479076658722791785143 6596218614988084187677715)
          ·
            refine ⟨9894327922482126281516573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6596218614988084187677715 9894327922482126281516573)
            ·
              refine ⟨3710372970930797355568715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9894327922482126281516573 3710372970930797355568715)
              ·
                refine ⟨5565559456396196033353073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710372970930797355568715 5565559456396196033353073)
                ·
                  refine ⟨4174169592297147025014805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565559456396196033353073 4174169592297147025014805)
                  ·
                    refine ⟨195664199638928766797569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4174169592297147025014805 195664199638928766797569)
                    ·
                      refine ⟨146748149729196575098177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195664199638928766797569 146748149729196575098177)
                      ·
                        rfl

theorem cell23_285791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_285791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285791 prefixEnd_285791 := by exact prefixLift 285791
  have htrace : WordTrace (prefixWord ++ tailWord_285791) baseStart_285791 baseEnd_285791 := by
    simpa [prefixWord, tailWord_285791, baseEnd_285791] using wordTrace_append hprefix tailTrace_285791
  have hstable : (prefixWord ++ tailWord_285791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285791).length < 2 ^ (prefixWord ++ tailWord_285791).sum := by decide
  have hdescent : baseEnd_285791 < baseStart_285791 := by decide
  rcases family_descends (prefixWord ++ tailWord_285791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285801 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 4, 4]
def baseStart_285801 : Nat := 118140960795 + 285801 * 2 ^ 59
def prefixEnd_285801 : Nat := 4983230072969 + 3 ^ 40 * 285801 * 2
def baseEnd_285801 : Nat := 48917761511913845324377

theorem tailTrace_285801 : CollatzResearch.WordTrace tailWord_285801 prefixEnd_285801 48917761511913845324377 := by
  unfold tailWord_285801
  simp only [CollatzResearch.WordTrace]
  refine ⟨10424018837599262769873257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6949345891732841846582171 10424018837599262769873257)
  ·
    refine ⟨7818014128199447077404943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10424018837599262769873257 7818014128199447077404943)
    ·
      refine ⟨11727021192299170616107415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818014128199447077404943 11727021192299170616107415)
      ·
        refine ⟨17590531788448755924161123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727021192299170616107415 17590531788448755924161123)
        ·
          refine ⟨26385797682673133886241685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17590531788448755924161123 26385797682673133886241685)
          ·
            refine ⟨1236834266375303150917579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26385797682673133886241685 1236834266375303150917579)
            ·
              refine ⟨1855251399562954726376369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236834266375303150917579 1855251399562954726376369)
              ·
                refine ⟨1391438549672216044782277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855251399562954726376369 1391438549672216044782277)
                ·
                  refine ⟨260894728063540508396677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391438549672216044782277 260894728063540508396677)
                  ·
                    refine ⟨48917761511913845324377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 260894728063540508396677 48917761511913845324377)
                    ·
                      rfl

theorem cell23_285801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_285801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285801 prefixEnd_285801 := by exact prefixLift 285801
  have htrace : WordTrace (prefixWord ++ tailWord_285801) baseStart_285801 baseEnd_285801 := by
    simpa [prefixWord, tailWord_285801, baseEnd_285801] using wordTrace_append hprefix tailTrace_285801
  have hstable : (prefixWord ++ tailWord_285801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285801).length < 2 ^ (prefixWord ++ tailWord_285801).sum := by decide
  have hdescent : baseEnd_285801 < baseStart_285801 := by decide
  rcases family_descends (prefixWord ++ tailWord_285801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285802 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_285802 : Nat := 118140960795 + 285802 * 2 ^ 59
def prefixEnd_285802 : Nat := 4983230072969 + 3 ^ 40 * 285802 * 2
def baseEnd_285802 : Nat := 146753798016396032060627

theorem tailTrace_285802 : CollatzResearch.WordTrace tailWord_285802 prefixEnd_285802 146753798016396032060627 := by
  unfold tailWord_285802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606013827648909985164915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6949370207063759960439773 2606013827648909985164915)
  ·
    refine ⟨3909020741473364977747373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2606013827648909985164915 3909020741473364977747373)
    ·
      refine ⟨1465882778052511866655265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3909020741473364977747373 1465882778052511866655265)
      ·
        refine ⟨1099412083539383899991449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1465882778052511866655265 1099412083539383899991449)
        ·
          refine ⟨824559062654537924993587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099412083539383899991449 824559062654537924993587)
          ·
            refine ⟨1236838593981806887490381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824559062654537924993587 1236838593981806887490381)
            ·
              refine ⟨463814472743177582808893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236838593981806887490381 463814472743177582808893)
              ·
                refine ⟨173930427278691593553335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463814472743177582808893 173930427278691593553335)
                ·
                  refine ⟨260895640918037390330003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173930427278691593553335 260895640918037390330003)
                  ·
                    refine ⟨391343461377056085495005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260895640918037390330003 391343461377056085495005)
                    ·
                      refine ⟨146753798016396032060627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 391343461377056085495005 146753798016396032060627)
                      ·
                        rfl

theorem cell23_285802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_285802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285802 prefixEnd_285802 := by exact prefixLift 285802
  have htrace : WordTrace (prefixWord ++ tailWord_285802) baseStart_285802 baseEnd_285802 := by
    simpa [prefixWord, tailWord_285802, baseEnd_285802] using wordTrace_append hprefix tailTrace_285802
  have hstable : (prefixWord ++ tailWord_285802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285802).length < 2 ^ (prefixWord ++ tailWord_285802).sum := by decide
  have hdescent : baseEnd_285802 < baseStart_285802 := by decide
  rcases family_descends (prefixWord ++ tailWord_285802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285881 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_285881 : Nat := 118140960795 + 285881 * 2 ^ 59
def prefixEnd_285881 : Nat := 4983230072969 + 3 ^ 40 * 285881 * 2
def baseEnd_285881 : Nat := 146794362988101222972763

theorem tailTrace_285881 : CollatzResearch.WordTrace tailWord_285881 prefixEnd_285881 146794362988101222972763 := by
  unfold tailWord_285881
  simp only [CollatzResearch.WordTrace]
  refine ⟨10426936677309436432785497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6951291118206290955190331 10426936677309436432785497)
  ·
    refine ⟨7820202507982077324589123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10426936677309436432785497 7820202507982077324589123)
    ·
      refine ⟨11730303761973115986883685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7820202507982077324589123 11730303761973115986883685)
      ·
        refine ⟨2199431955369959247540691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11730303761973115986883685 2199431955369959247540691)
        ·
          refine ⟨3299147933054938871311037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199431955369959247540691 3299147933054938871311037)
          ·
            refine ⟨1237180474895602076741639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3299147933054938871311037 1237180474895602076741639)
            ·
              refine ⟨1855770712343403115112459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237180474895602076741639 1855770712343403115112459)
              ·
                refine ⟨2783656068515104672668689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855770712343403115112459 2783656068515104672668689)
                ·
                  refine ⟨2087742051386328504501517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783656068515104672668689 2087742051386328504501517)
                  ·
                    refine ⟨782903269269873189188069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087742051386328504501517 782903269269873189188069)
                    ·
                      refine ⟨146794362988101222972763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 782903269269873189188069 146794362988101222972763)
                      ·
                        rfl

theorem cell23_285881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_285881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285881 prefixEnd_285881 := by exact prefixLift 285881
  have htrace : WordTrace (prefixWord ++ tailWord_285881) baseStart_285881 baseEnd_285881 := by
    simpa [prefixWord, tailWord_285881, baseEnd_285881] using wordTrace_append hprefix tailTrace_285881
  have hstable : (prefixWord ++ tailWord_285881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285881).length < 2 ^ (prefixWord ++ tailWord_285881).sum := by decide
  have hdescent : baseEnd_285881 < baseStart_285881 := by decide
  rcases family_descends (prefixWord ++ tailWord_285881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285932 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 2, 2, 2]
def baseStart_285932 : Nat := 118140960795 + 285932 * 2 ^ 59
def prefixEnd_285932 : Nat := 4983230072969 + 3 ^ 40 * 285932 * 2
def baseEnd_285932 : Nat := 146820550501480523435029

theorem tailTrace_285932 : CollatzResearch.WordTrace tailWord_285932 prefixEnd_285932 146820550501480523435029 := by
  unfold tailWord_285932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214398400062336071446025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6952531200083114761928033 5214398400062336071446025)
  ·
    refine ⟨3910798800046752053584519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5214398400062336071446025 3910798800046752053584519)
    ·
      refine ⟨5866198200070128080376779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3910798800046752053584519 5866198200070128080376779)
      ·
        refine ⟨8799297300105192120565169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866198200070128080376779 8799297300105192120565169)
        ·
          refine ⟨6599472975078894090423877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8799297300105192120565169 6599472975078894090423877)
          ·
            refine ⟨1237401182827292641954477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6599472975078894090423877 1237401182827292641954477)
            ·
              refine ⟨464025443560234740732929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1237401182827292641954477 464025443560234740732929)
              ·
                refine ⟨348019082670176055549697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464025443560234740732929 348019082670176055549697)
                ·
                  refine ⟨261014312002632041662273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348019082670176055549697 261014312002632041662273)
                  ·
                    refine ⟨195760734001974031246705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 261014312002632041662273 195760734001974031246705)
                    ·
                      refine ⟨146820550501480523435029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195760734001974031246705 146820550501480523435029)
                      ·
                        rfl

theorem cell23_285932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_285932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285932 prefixEnd_285932 := by exact prefixLift 285932
  have htrace : WordTrace (prefixWord ++ tailWord_285932) baseStart_285932 baseEnd_285932 := by
    simpa [prefixWord, tailWord_285932, baseEnd_285932] using wordTrace_append hprefix tailTrace_285932
  have hstable : (prefixWord ++ tailWord_285932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285932).length < 2 ^ (prefixWord ++ tailWord_285932).sum := by decide
  have hdescent : baseEnd_285932 < baseStart_285932 := by decide
  rcases family_descends (prefixWord ++ tailWord_285932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285951 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 1, 7]
def baseStart_285951 : Nat := 118140960795 + 285951 * 2 ^ 59
def prefixEnd_285951 : Nat := 4983230072969 + 3 ^ 40 * 285951 * 2
def baseEnd_285951 : Nat := 48943435544638649699147

theorem tailTrace_285951 : CollatzResearch.WordTrace tailWord_285951 prefixEnd_285951 48943435544638649699147 := by
  unfold tailWord_285951
  simp only [CollatzResearch.WordTrace]
  refine ⟨10429489787055838387833707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6952993191370558925222471 10429489787055838387833707)
  ·
    refine ⟨15644234680583757581750561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10429489787055838387833707 15644234680583757581750561)
    ·
      refine ⟨11733176010437818186312921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15644234680583757581750561 11733176010437818186312921)
      ·
        refine ⟨8799882007828363639734691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11733176010437818186312921 8799882007828363639734691)
        ·
          refine ⟨13199823011742545459602037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799882007828363639734691 13199823011742545459602037)
          ·
            refine ⟨1237483407350863636837691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13199823011742545459602037 1237483407350863636837691)
            ·
              refine ⟨1856225111026295455256537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237483407350863636837691 1856225111026295455256537)
              ·
                refine ⟨1392168833269721591442403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856225111026295455256537 1392168833269721591442403)
                ·
                  refine ⟨2088253249904582387163605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392168833269721591442403 2088253249904582387163605)
                  ·
                    refine ⟨48943435544638649699147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2088253249904582387163605 48943435544638649699147)
                    ·
                      rfl

theorem cell23_285951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_285951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_285951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_285951 prefixEnd_285951 := by exact prefixLift 285951
  have htrace : WordTrace (prefixWord ++ tailWord_285951) baseStart_285951 baseEnd_285951 := by
    simpa [prefixWord, tailWord_285951, baseEnd_285951] using wordTrace_append hprefix tailTrace_285951
  have hstable : (prefixWord ++ tailWord_285951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285951).length < 2 ^ (prefixWord ++ tailWord_285951).sum := by decide
  have hdescent : baseEnd_285951 < baseStart_285951 := by decide
  rcases family_descends (prefixWord ++ tailWord_285951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286008 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_286008 : Nat := 118140960795 + 286008 * 2 ^ 59
def prefixEnd_286008 : Nat := 4983230072969 + 3 ^ 40 * 286008 * 2
def baseEnd_286008 : Nat := 146859575031222226084679

theorem tailTrace_286008 : CollatzResearch.WordTrace tailWord_286008 prefixEnd_286008 146859575031222226084679 := by
  unfold tailWord_286008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215784373924668561329339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6954379165232891415105785 5215784373924668561329339)
  ·
    refine ⟨7823676560887002841994009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5215784373924668561329339 7823676560887002841994009)
    ·
      refine ⟨5867757420665252131495507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7823676560887002841994009 5867757420665252131495507)
      ·
        refine ⟨8801636130997878197243261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867757420665252131495507 8801636130997878197243261)
        ·
          refine ⟨3300613549124204323966223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8801636130997878197243261 3300613549124204323966223)
          ·
            refine ⟨4950920323686306485949335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300613549124204323966223 4950920323686306485949335)
            ·
              refine ⟨7426380485529459728924003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950920323686306485949335 7426380485529459728924003)
              ·
                refine ⟨11139570728294189593386005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426380485529459728924003 11139570728294189593386005)
                ·
                  refine ⟨522167377888790137189969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11139570728294189593386005 522167377888790137189969)
                  ·
                    refine ⟨391625533416592602892477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 522167377888790137189969 391625533416592602892477)
                    ·
                      refine ⟨146859575031222226084679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 391625533416592602892477 146859575031222226084679)
                      ·
                        rfl

theorem cell23_286008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_286008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286008 prefixEnd_286008 := by exact prefixLift 286008
  have htrace : WordTrace (prefixWord ++ tailWord_286008) baseStart_286008 baseEnd_286008 := by
    simpa [prefixWord, tailWord_286008, baseEnd_286008] using wordTrace_append hprefix tailTrace_286008
  have hstable : (prefixWord ++ tailWord_286008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286008).length < 2 ^ (prefixWord ++ tailWord_286008).sum := by decide
  have hdescent : baseEnd_286008 < baseStart_286008 := by decide
  rcases family_descends (prefixWord ++ tailWord_286008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286065 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 4, 3, 2]
def baseStart_286065 : Nat := 118140960795 + 286065 * 2 ^ 59
def prefixEnd_286065 : Nat := 4983230072969 + 3 ^ 40 * 286065 * 2
def baseEnd_286065 : Nat := 146888843428528503071917

theorem tailTrace_286065 : CollatzResearch.WordTrace tailWord_286065 prefixEnd_286065 146888843428528503071917 := by
  unfold tailWord_286065
  simp only [CollatzResearch.WordTrace]
  refine ⟨10433647708642835857483649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6955765139095223904989099 10433647708642835857483649)
  ·
    refine ⟨7825235781482126893112737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10433647708642835857483649 7825235781482126893112737)
    ·
      refine ⟨5868926836111595169834553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7825235781482126893112737 5868926836111595169834553)
      ·
        refine ⟨4401695127083696377375915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5868926836111595169834553 4401695127083696377375915)
        ·
          refine ⟨6602542690625544566063873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401695127083696377375915 6602542690625544566063873)
          ·
            refine ⟨4951907017969158424547905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6602542690625544566063873 4951907017969158424547905)
            ·
              refine ⟨3713930263476868818410929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4951907017969158424547905 3713930263476868818410929)
              ·
                refine ⟨2785447697607651613808197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3713930263476868818410929 2785447697607651613808197)
                ·
                  refine ⟨522271443301434677589037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2785447697607651613808197 522271443301434677589037)
                  ·
                    refine ⟨195851791238038004095889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522271443301434677589037 195851791238038004095889)
                    ·
                      refine ⟨146888843428528503071917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195851791238038004095889 146888843428528503071917)
                      ·
                        rfl

theorem cell23_286065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_286065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286065 prefixEnd_286065 := by exact prefixLift 286065
  have htrace : WordTrace (prefixWord ++ tailWord_286065) baseStart_286065 baseEnd_286065 := by
    simpa [prefixWord, tailWord_286065, baseEnd_286065] using wordTrace_append hprefix tailTrace_286065
  have hstable : (prefixWord ++ tailWord_286065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286065).length < 2 ^ (prefixWord ++ tailWord_286065).sum := by decide
  have hdescent : baseEnd_286065 < baseStart_286065 := by decide
  rcases family_descends (prefixWord ++ tailWord_286065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286105 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 4, 4]
def baseStart_286105 : Nat := 118140960795 + 286105 * 2 ^ 59
def prefixEnd_286105 : Nat := 4983230072969 + 3 ^ 40 * 286105 * 2
def baseEnd_286105 : Nat := 48969794218236115523911

theorem tailTrace_286105 : CollatzResearch.WordTrace tailWord_286105 prefixEnd_286105 48969794218236115523911 := by
  unfold tailWord_286105
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435106628497922688939769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6956737752331948459293179 10435106628497922688939769)
  ·
    refine ⟨7826329971373442016704827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10435106628497922688939769 7826329971373442016704827)
    ·
      refine ⟨11739494957060163025057241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7826329971373442016704827 11739494957060163025057241)
      ·
        refine ⟨8804621217795122268792931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11739494957060163025057241 8804621217795122268792931)
        ·
          refine ⟨13206931826692683403189397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8804621217795122268792931 13206931826692683403189397)
          ·
            refine ⟨619074929376219534524503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13206931826692683403189397 619074929376219534524503)
            ·
              refine ⟨928612394064329301786755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619074929376219534524503 928612394064329301786755)
              ·
                refine ⟨1392918591096493952680133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928612394064329301786755 1392918591096493952680133)
                ·
                  refine ⟨261172235830592616127525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392918591096493952680133 261172235830592616127525)
                  ·
                    refine ⟨48969794218236115523911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261172235830592616127525 48969794218236115523911)
                    ·
                      rfl

theorem cell23_286105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_286105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286105 prefixEnd_286105 := by exact prefixLift 286105
  have htrace : WordTrace (prefixWord ++ tailWord_286105) baseStart_286105 baseEnd_286105 := by
    simpa [prefixWord, tailWord_286105, baseEnd_286105] using wordTrace_append hprefix tailTrace_286105
  have hstable : (prefixWord ++ tailWord_286105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286105).length < 2 ^ (prefixWord ++ tailWord_286105).sum := by decide
  have hdescent : baseEnd_286105 < baseStart_286105 := by decide
  rcases family_descends (prefixWord ++ tailWord_286105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286179 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 3]
def baseStart_286179 : Nat := 118140960795 + 286179 * 2 ^ 59
def prefixEnd_286179 : Nat := 4983230072969 + 3 ^ 40 * 286179 * 2
def baseEnd_286179 : Nat := 146947380223141057046393

theorem tailTrace_286179 : CollatzResearch.WordTrace tailWord_286179 prefixEnd_286179 146947380223141057046393 := by
  unfold tailWord_286179
  simp only [CollatzResearch.WordTrace]
  refine ⟨10437805630229833327133591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6958537086819888884755727 10437805630229833327133591)
  ·
    refine ⟨15656708445344749990700387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10437805630229833327133591 15656708445344749990700387)
    ·
      refine ⟨23485062668017124986050581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15656708445344749990700387 23485062668017124986050581)
      ·
        refine ⟨1100862312563302733721121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23485062668017124986050581 1100862312563302733721121)
        ·
          refine ⟨825646734422477050290841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100862312563302733721121 825646734422477050290841)
          ·
            refine ⟨619235050816857787718131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825646734422477050290841 619235050816857787718131)
            ·
              refine ⟨928852576225286681577197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619235050816857787718131 928852576225286681577197)
              ·
                refine ⟨348319716084482505591449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928852576225286681577197 348319716084482505591449)
                ·
                  refine ⟨261239787063361879193587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348319716084482505591449 261239787063361879193587)
                  ·
                    refine ⟨391859680595042818790381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 261239787063361879193587 391859680595042818790381)
                    ·
                      refine ⟨146947380223141057046393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 391859680595042818790381 146947380223141057046393)
                      ·
                        rfl

theorem cell23_286179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_286179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286179 prefixEnd_286179 := by exact prefixLift 286179
  have htrace : WordTrace (prefixWord ++ tailWord_286179) baseStart_286179 baseEnd_286179 := by
    simpa [prefixWord, tailWord_286179, baseEnd_286179] using wordTrace_append hprefix tailTrace_286179
  have hstable : (prefixWord ++ tailWord_286179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286179).length < 2 ^ (prefixWord ++ tailWord_286179).sum := by decide
  have hdescent : baseEnd_286179 < baseStart_286179 := by decide
  rcases family_descends (prefixWord ++ tailWord_286179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286202 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2]
def baseStart_286202 : Nat := 118140960795 + 286202 * 2 ^ 59
def prefixEnd_286202 : Nat := 4983230072969 + 3 ^ 40 * 286202 * 2
def baseEnd_286202 : Nat := 146959190278194467058787

theorem tailTrace_286202 : CollatzResearch.WordTrace tailWord_286202 prefixEnd_286202 146959190278194467058787 := by
  unfold tailWord_286202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609661127286627063805215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6959096339431005503480573 2609661127286627063805215)
  ·
    refine ⟨3914491690929940595707823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2609661127286627063805215 3914491690929940595707823)
    ·
      refine ⟨5871737536394910893561735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3914491690929940595707823 5871737536394910893561735)
      ·
        refine ⟨8807606304592366340342603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871737536394910893561735 8807606304592366340342603)
        ·
          refine ⟨13211409456888549510513905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8807606304592366340342603 13211409456888549510513905)
          ·
            refine ⟨9908557092666412132885429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13211409456888549510513905 9908557092666412132885429)
            ·
              refine ⟨928927227437476137458009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9908557092666412132885429 928927227437476137458009)
              ·
                refine ⟨696695420578107103093507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928927227437476137458009 696695420578107103093507)
                ·
                  refine ⟨1045043130867160654640261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696695420578107103093507 1045043130867160654640261)
                  ·
                    refine ⟨195945587037592622745049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1045043130867160654640261 195945587037592622745049)
                    ·
                      refine ⟨146959190278194467058787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 195945587037592622745049 146959190278194467058787)
                      ·
                        rfl

theorem cell23_286202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_286202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286202 prefixEnd_286202 := by exact prefixLift 286202
  have htrace : WordTrace (prefixWord ++ tailWord_286202) baseStart_286202 baseEnd_286202 := by
    simpa [prefixWord, tailWord_286202, baseEnd_286202] using wordTrace_append hprefix tailTrace_286202
  have hstable : (prefixWord ++ tailWord_286202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286202).length < 2 ^ (prefixWord ++ tailWord_286202).sum := by decide
  have hdescent : baseEnd_286202 < baseStart_286202 := by decide
  rcases family_descends (prefixWord ++ tailWord_286202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286205 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_286205 : Nat := 118140960795 + 286205 * 2 ^ 59
def prefixEnd_286205 : Nat := 4983230072969 + 3 ^ 40 * 286205 * 2
def baseEnd_286205 : Nat := 146960730720157955321273

theorem tailTrace_286205 : CollatzResearch.WordTrace tailWord_286205 prefixEnd_286205 146960730720157955321273 := by
  unfold tailWord_286205
  simp only [CollatzResearch.WordTrace]
  refine ⟨10438753928135639767580069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6959169285423759845053379 10438753928135639767580069)
  ·
    refine ⟨1957266361525432456421263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10438753928135639767580069 1957266361525432456421263)
    ·
      refine ⟨2935899542288148684631895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957266361525432456421263 2935899542288148684631895)
      ·
        refine ⟨4403849313432223026947843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935899542288148684631895 4403849313432223026947843)
        ·
          refine ⟨6605773970148334540421765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403849313432223026947843 6605773970148334540421765)
          ·
            refine ⟨1238582619402812726329081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6605773970148334540421765 1238582619402812726329081)
            ·
              refine ⟨928936964552109544746811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1238582619402812726329081 928936964552109544746811)
              ·
                refine ⟨1393405446828164317120217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928936964552109544746811 1393405446828164317120217)
                ·
                  refine ⟨1045054085121123237840163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393405446828164317120217 1045054085121123237840163)
                  ·
                    refine ⟨1567581127681684856760245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045054085121123237840163 1567581127681684856760245)
                    ·
                      refine ⟨146960730720157955321273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1567581127681684856760245 146960730720157955321273)
                      ·
                        rfl

theorem cell23_286205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_286205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286205 prefixEnd_286205 := by exact prefixLift 286205
  have htrace : WordTrace (prefixWord ++ tailWord_286205) baseStart_286205 baseEnd_286205 := by
    simpa [prefixWord, tailWord_286205, baseEnd_286205] using wordTrace_append hprefix tailTrace_286205
  have hstable : (prefixWord ++ tailWord_286205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286205).length < 2 ^ (prefixWord ++ tailWord_286205).sum := by decide
  have hdescent : baseEnd_286205 < baseStart_286205 := by decide
  rcases family_descends (prefixWord ++ tailWord_286205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286232 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_286232 : Nat := 118140960795 + 286232 * 2 ^ 59
def prefixEnd_286232 : Nat := 4983230072969 + 3 ^ 40 * 286232 * 2
def baseEnd_286232 : Nat := 146974594697829349683649

theorem tailTrace_286232 : CollatzResearch.WordTrace tailWord_286232 prefixEnd_286232 146974594697829349683649 := by
  unfold tailWord_286232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5219869349518911689406475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6959825799358548919208633 5219869349518911689406475)
  ·
    refine ⟨7829804024278367534109713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5219869349518911689406475 7829804024278367534109713)
    ·
      refine ⟨5872353018208775650582285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7829804024278367534109713 5872353018208775650582285)
      ·
        refine ⟨2202132381828290868968357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5872353018208775650582285 2202132381828290868968357)
        ·
          refine ⟨412899821592804537931567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2202132381828290868968357 412899821592804537931567)
          ·
            refine ⟨619349732389206806897351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412899821592804537931567 619349732389206806897351)
            ·
              refine ⟨929024598583810210346027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619349732389206806897351 929024598583810210346027)
              ·
                refine ⟨1393536897875715315519041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929024598583810210346027 1393536897875715315519041)
                ·
                  refine ⟨1045152673406786486639281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393536897875715315519041 1045152673406786486639281)
                  ·
                    refine ⟨783864505055089864979461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1045152673406786486639281 783864505055089864979461)
                    ·
                      refine ⟨146974594697829349683649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 783864505055089864979461 146974594697829349683649)
                      ·
                        rfl

theorem cell23_286232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_286232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286232 prefixEnd_286232 := by exact prefixLift 286232
  have htrace : WordTrace (prefixWord ++ tailWord_286232) baseStart_286232 baseEnd_286232 := by
    simpa [prefixWord, tailWord_286232, baseEnd_286232] using wordTrace_append hprefix tailTrace_286232
  have hstable : (prefixWord ++ tailWord_286232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286232).length < 2 ^ (prefixWord ++ tailWord_286232).sum := by decide
  have hdescent : baseEnd_286232 < baseStart_286232 := by decide
  rcases family_descends (prefixWord ++ tailWord_286232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286305 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_286305 : Nat := 118140960795 + 286305 * 2 ^ 59
def prefixEnd_286305 : Nat := 4983230072969 + 3 ^ 40 * 286305 * 2
def baseEnd_286305 : Nat := 147012078785607564070813

theorem tailTrace_286305 : CollatzResearch.WordTrace tailWord_286305 prefixEnd_286305 147012078785607564070813 := by
  unfold tailWord_286305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10442401227773356846220369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6961600818515571230813579 10442401227773356846220369)
  ·
    refine ⟨7831800920830017634665277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10442401227773356846220369 7831800920830017634665277)
    ·
      refine ⟨2936925345311256612999479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7831800920830017634665277 2936925345311256612999479)
      ·
        refine ⟨4405388017966884919499219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936925345311256612999479 4405388017966884919499219)
        ·
          refine ⟨6608082026950327379248829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405388017966884919499219 6608082026950327379248829)
          ·
            refine ⟨2478030760106372767218311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6608082026950327379248829 2478030760106372767218311)
            ·
              refine ⟨3717046140159559150827467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478030760106372767218311 3717046140159559150827467)
              ·
                refine ⟨5575569210239338726241201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717046140159559150827467 5575569210239338726241201)
                ·
                  refine ⟨4181676907679504044680901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5575569210239338726241201 4181676907679504044680901)
                  ·
                    refine ⟨784064420189907008377669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4181676907679504044680901 784064420189907008377669)
                    ·
                      refine ⟨147012078785607564070813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 784064420189907008377669 147012078785607564070813)
                      ·
                        rfl

theorem cell23_286305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_286305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286305 prefixEnd_286305 := by exact prefixLift 286305
  have htrace : WordTrace (prefixWord ++ tailWord_286305) baseStart_286305 baseEnd_286305 := by
    simpa [prefixWord, tailWord_286305, baseEnd_286305] using wordTrace_append hprefix tailTrace_286305
  have hstable : (prefixWord ++ tailWord_286305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286305).length < 2 ^ (prefixWord ++ tailWord_286305).sum := by decide
  have hdescent : baseEnd_286305 < baseStart_286305 := by decide
  rcases family_descends (prefixWord ++ tailWord_286305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286336 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 1, 4]
def baseStart_286336 : Nat := 118140960795 + 286336 * 2 ^ 59
def prefixEnd_286336 : Nat := 4983230072969 + 3 ^ 40 * 286336 * 2
def baseEnd_286336 : Nat := 49009332228632314261057

theorem tailTrace_286336 : CollatzResearch.WordTrace tailWord_286336 prefixEnd_286336 49009332228632314261057 := by
  unfold tailWord_286336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221765945330524570299431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6962354593774032760399241 5221765945330524570299431)
  ·
    refine ⟨7832648917995786855449147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5221765945330524570299431 7832648917995786855449147)
    ·
      refine ⟨11748973376993680283173721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7832648917995786855449147 11748973376993680283173721)
      ·
        refine ⟨8811730032745260212380291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11748973376993680283173721 8811730032745260212380291)
        ·
          refine ⟨13217595049117890318570437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8811730032745260212380291 13217595049117890318570437)
          ·
            refine ⟨2478299071709604434731957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13217595049117890318570437 2478299071709604434731957)
            ·
              refine ⟨232340537972775415756121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2478299071709604434731957 232340537972775415756121)
              ·
                refine ⟨174255403479581561817091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232340537972775415756121 174255403479581561817091)
                ·
                  refine ⟨261383105219372342725637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174255403479581561817091 261383105219372342725637)
                  ·
                    refine ⟨49009332228632314261057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261383105219372342725637 49009332228632314261057)
                    ·
                      rfl

theorem cell23_286336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 4].length) (baseStart_286336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286336 prefixEnd_286336 := by exact prefixLift 286336
  have htrace : WordTrace (prefixWord ++ tailWord_286336) baseStart_286336 baseEnd_286336 := by
    simpa [prefixWord, tailWord_286336, baseEnd_286336] using wordTrace_append hprefix tailTrace_286336
  have hstable : (prefixWord ++ tailWord_286336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286336).length < 2 ^ (prefixWord ++ tailWord_286336).sum := by decide
  have hdescent : baseEnd_286336 < baseStart_286336 := by decide
  rcases family_descends (prefixWord ++ tailWord_286336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286352 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 3, 5, 2]
def baseStart_286352 : Nat := 118140960795 + 286352 * 2 ^ 59
def prefixEnd_286352 : Nat := 4983230072969 + 3 ^ 40 * 286352 * 2
def baseEnd_286352 : Nat := 147036212376368880183097

theorem tailTrace_286352 : CollatzResearch.WordTrace tailWord_286352 prefixEnd_286352 147036212376368880183097 := by
  unfold tailWord_286352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222057729301541936590655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6962743639068722582120873 5222057729301541936590655)
  ·
    refine ⟨7833086593952312904885983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5222057729301541936590655 7833086593952312904885983)
    ·
      refine ⟨11749629890928469357328975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7833086593952312904885983 11749629890928469357328975)
      ·
        refine ⟨17624444836392704035993463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11749629890928469357328975 17624444836392704035993463)
        ·
          refine ⟨26436667254589056053990195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17624444836392704035993463 26436667254589056053990195)
          ·
            refine ⟨39655000881883584080985293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26436667254589056053990195 39655000881883584080985293)
            ·
              refine ⟨14870625330706344030369485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39655000881883584080985293 14870625330706344030369485)
              ·
                refine ⟨5576484499014879011388557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14870625330706344030369485 5576484499014879011388557)
                ·
                  refine ⟨2091181687130579629270709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5576484499014879011388557 2091181687130579629270709)
                  ·
                    refine ⟨196048283168491840244129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2091181687130579629270709 196048283168491840244129)
                    ·
                      refine ⟨147036212376368880183097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196048283168491840244129 147036212376368880183097)
                      ·
                        rfl

theorem cell23_286352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 5, 2].length) (baseStart_286352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286352 prefixEnd_286352 := by exact prefixLift 286352
  have htrace : WordTrace (prefixWord ++ tailWord_286352) baseStart_286352 baseEnd_286352 := by
    simpa [prefixWord, tailWord_286352, baseEnd_286352] using wordTrace_append hprefix tailTrace_286352
  have hstable : (prefixWord ++ tailWord_286352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286352).length < 2 ^ (prefixWord ++ tailWord_286352).sum := by decide
  have hdescent : baseEnd_286352 < baseStart_286352 := by decide
  rcases family_descends (prefixWord ++ tailWord_286352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286392 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 4, 4]
def baseStart_286392 : Nat := 118140960795 + 286392 * 2 ^ 59
def prefixEnd_286392 : Nat := 4983230072969 + 3 ^ 40 * 286392 * 2
def baseEnd_286392 : Nat := 49018917200849574560971

theorem tailTrace_286392 : CollatzResearch.WordTrace tailWord_286392 prefixEnd_286392 49018917200849574560971 := by
  unfold tailWord_286392
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222787189229085352318715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6963716252305447136424953 5222787189229085352318715)
  ·
    refine ⟨7834180783843628028478073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5222787189229085352318715 7834180783843628028478073)
    ·
      refine ⟨5875635587882721021358555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7834180783843628028478073 5875635587882721021358555)
      ·
        refine ⟨8813453381824081532037833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875635587882721021358555 8813453381824081532037833)
        ·
          refine ⟨6610090036368061149028375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8813453381824081532037833 6610090036368061149028375)
          ·
            refine ⟨9915135054552091723542563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6610090036368061149028375 9915135054552091723542563)
            ·
              refine ⟨14872702581828137585313845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915135054552091723542563 14872702581828137585313845)
              ·
                refine ⟨1394315867046387898623173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14872702581828137585313845 1394315867046387898623173)
                ·
                  refine ⟨261434225071197730991845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394315867046387898623173 261434225071197730991845)
                  ·
                    refine ⟨49018917200849574560971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261434225071197730991845 49018917200849574560971)
                    ·
                      rfl

theorem cell23_286392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_286392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286392 prefixEnd_286392 := by exact prefixLift 286392
  have htrace : WordTrace (prefixWord ++ tailWord_286392) baseStart_286392 baseEnd_286392 := by
    simpa [prefixWord, tailWord_286392, baseEnd_286392] using wordTrace_append hprefix tailTrace_286392
  have hstable : (prefixWord ++ tailWord_286392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286392).length < 2 ^ (prefixWord ++ tailWord_286392).sum := by decide
  have hdescent : baseEnd_286392 < baseStart_286392 := by decide
  rcases family_descends (prefixWord ++ tailWord_286392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286393 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 1, 1, 3]
def baseStart_286393 : Nat := 118140960795 + 286393 * 2 ^ 59
def prefixEnd_286393 : Nat := 4983230072969 + 3 ^ 40 * 286393 * 2
def baseEnd_286393 : Nat := 147057265083203219770409

theorem tailTrace_286393 : CollatzResearch.WordTrace tailWord_286393 prefixEnd_286393 147057265083203219770409 := by
  unfold tailWord_286393
  simp only [CollatzResearch.WordTrace]
  refine ⟨10445610851454547875423833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6963740567636365250282555 10445610851454547875423833)
  ·
    refine ⟨7834208138590910906567875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10445610851454547875423833 7834208138590910906567875)
    ·
      refine ⟨11751312207886366359851813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7834208138590910906567875 11751312207886366359851813)
      ·
        refine ⟨2203371038978693692472215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11751312207886366359851813 2203371038978693692472215)
        ·
          refine ⟨3305056558468040538708323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203371038978693692472215 3305056558468040538708323)
          ·
            refine ⟨4957584837702060808062485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305056558468040538708323 4957584837702060808062485)
            ·
              refine ⟨232386789267284100377929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4957584837702060808062485 232386789267284100377929)
              ·
                refine ⟨174290091950463075283447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232386789267284100377929 174290091950463075283447)
                ·
                  refine ⟨261435137925694612925171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174290091950463075283447 261435137925694612925171)
                  ·
                    refine ⟨392152706888541919387757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 261435137925694612925171 392152706888541919387757)
                    ·
                      refine ⟨147057265083203219770409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 392152706888541919387757 147057265083203219770409)
                      ·
                        rfl

theorem cell23_286393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_286393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286393 prefixEnd_286393 := by exact prefixLift 286393
  have htrace : WordTrace (prefixWord ++ tailWord_286393) baseStart_286393 baseEnd_286393 := by
    simpa [prefixWord, tailWord_286393, baseEnd_286393] using wordTrace_append hprefix tailTrace_286393
  have hstable : (prefixWord ++ tailWord_286393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286393).length < 2 ^ (prefixWord ++ tailWord_286393).sum := by decide
  have hdescent : baseEnd_286393 < baseStart_286393 := by decide
  rcases family_descends (prefixWord ++ tailWord_286393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286395 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_286395 : Nat := 118140960795 + 286395 * 2 ^ 59
def prefixEnd_286395 : Nat := 4983230072969 + 3 ^ 40 * 286395 * 2
def baseEnd_286395 : Nat := 147058292044512211945399

theorem tailTrace_286395 : CollatzResearch.WordTrace tailWord_286395 prefixEnd_286395 147058292044512211945399 := by
  unfold tailWord_286395
  simp only [CollatzResearch.WordTrace]
  refine ⟨10445683797447302216996639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6963789198298201477997759 10445683797447302216996639)
  ·
    refine ⟨15668525696170953325494959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10445683797447302216996639 15668525696170953325494959)
    ·
      refine ⟨23502788544256429988242439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15668525696170953325494959 23502788544256429988242439)
      ·
        refine ⟨35254182816384644982363659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23502788544256429988242439 35254182816384644982363659)
        ·
          refine ⟨52881274224576967473545489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35254182816384644982363659 52881274224576967473545489)
          ·
            refine ⟨39660955668432725605159117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52881274224576967473545489 39660955668432725605159117)
            ·
              refine ⟨14872858375662272101934669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39660955668432725605159117 14872858375662272101934669)
              ·
                refine ⟨5577321890873352038225501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14872858375662272101934669 5577321890873352038225501)
                ·
                  refine ⟨2091495709077507014334563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5577321890873352038225501 2091495709077507014334563)
                  ·
                    refine ⟨3137243563616260521501845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2091495709077507014334563 3137243563616260521501845)
                    ·
                      refine ⟨147058292044512211945399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3137243563616260521501845 147058292044512211945399)
                      ·
                        rfl

theorem cell23_286395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_286395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286395 prefixEnd_286395 := by exact prefixLift 286395
  have htrace : WordTrace (prefixWord ++ tailWord_286395) baseStart_286395 baseEnd_286395 := by
    simpa [prefixWord, tailWord_286395, baseEnd_286395] using wordTrace_append hprefix tailTrace_286395
  have hstable : (prefixWord ++ tailWord_286395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286395).length < 2 ^ (prefixWord ++ tailWord_286395).sum := by decide
  have hdescent : baseEnd_286395 < baseStart_286395 := by decide
  rcases family_descends (prefixWord ++ tailWord_286395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286415 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_286415 : Nat := 118140960795 + 286415 * 2 ^ 59
def prefixEnd_286415 : Nat := 4983230072969 + 3 ^ 40 * 286415 * 2
def baseEnd_286415 : Nat := 147068561657602133695307

theorem tailTrace_286415 : CollatzResearch.WordTrace tailWord_286415 prefixEnd_286415 147068561657602133695307 := by
  unfold tailWord_286415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446413257374845632724699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6964275504916563755149799 10446413257374845632724699)
  ·
    refine ⟨15669619886062268449087049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10446413257374845632724699 15669619886062268449087049)
    ·
      refine ⟨11752214914546701336815287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15669619886062268449087049 11752214914546701336815287)
      ·
        refine ⟨17628322371820052005222931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11752214914546701336815287 17628322371820052005222931)
        ·
          refine ⟨26442483557730078007834397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17628322371820052005222931 26442483557730078007834397)
          ·
            refine ⟨9915931334148779252937899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26442483557730078007834397 9915931334148779252937899)
            ·
              refine ⟨14873897001223168879406849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915931334148779252937899 14873897001223168879406849)
              ·
                refine ⟨11155422750917376659555137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14873897001223168879406849 11155422750917376659555137)
                ·
                  refine ⟨8366567063188032494666353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11155422750917376659555137 8366567063188032494666353)
                  ·
                    refine ⟨6274925297391024370999765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8366567063188032494666353 6274925297391024370999765)
                    ·
                      refine ⟨147068561657602133695307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6274925297391024370999765 147068561657602133695307)
                      ·
                        rfl

theorem cell23_286415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_286415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286415 prefixEnd_286415 := by exact prefixLift 286415
  have htrace : WordTrace (prefixWord ++ tailWord_286415) baseStart_286415 baseEnd_286415 := by
    simpa [prefixWord, tailWord_286415, baseEnd_286415] using wordTrace_append hprefix tailTrace_286415
  have hstable : (prefixWord ++ tailWord_286415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286415).length < 2 ^ (prefixWord ++ tailWord_286415).sum := by decide
  have hdescent : baseEnd_286415 < baseStart_286415 := by decide
  rcases family_descends (prefixWord ++ tailWord_286415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286433 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_286433 : Nat := 118140960795 + 286433 * 2 ^ 59
def prefixEnd_286433 : Nat := 4983230072969 + 3 ^ 40 * 286433 * 2
def baseEnd_286433 : Nat := 147077804309383063270225

theorem tailTrace_286433 : CollatzResearch.WordTrace tailWord_286433 prefixEnd_286433 147077804309383063270225 := by
  unfold tailWord_286433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10447069771309634706879953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6964713180873089804586635 10447069771309634706879953)
  ·
    refine ⟨7835302328482226030159965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10447069771309634706879953 7835302328482226030159965)
    ·
      refine ⟨2938238373180834761309987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7835302328482226030159965 2938238373180834761309987)
      ·
        refine ⟨4407357559771252141964981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2938238373180834761309987 4407357559771252141964981)
        ·
          refine ⟨413189771228554888309217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4407357559771252141964981 413189771228554888309217)
          ·
            refine ⟨309892328421416166231913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413189771228554888309217 309892328421416166231913)
            ·
              refine ⟨232419246316062124673935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309892328421416166231913 232419246316062124673935)
              ·
                refine ⟨348628869474093187010903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232419246316062124673935 348628869474093187010903)
                ·
                  refine ⟨522943304211139780516355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348628869474093187010903 522943304211139780516355)
                  ·
                    refine ⟨784414956316709670774533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522943304211139780516355 784414956316709670774533)
                    ·
                      refine ⟨147077804309383063270225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 784414956316709670774533 147077804309383063270225)
                      ·
                        rfl

theorem cell23_286433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_286433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286433 prefixEnd_286433 := by exact prefixLift 286433
  have htrace : WordTrace (prefixWord ++ tailWord_286433) baseStart_286433 baseEnd_286433 := by
    simpa [prefixWord, tailWord_286433, baseEnd_286433] using wordTrace_append hprefix tailTrace_286433
  have hstable : (prefixWord ++ tailWord_286433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286433).length < 2 ^ (prefixWord ++ tailWord_286433).sum := by decide
  have hdescent : baseEnd_286433 < baseStart_286433 := by decide
  rcases family_descends (prefixWord ++ tailWord_286433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286439 : List Nat := [1, 1, 5, 4, 1, 1, 10]
def baseStart_286439 : Nat := 118140960795 + 286439 * 2 ^ 59
def prefixEnd_286439 : Nat := 4983230072969 + 3 ^ 40 * 286439 * 2
def baseEnd_286439 : Nat := 1815813397448272096237

theorem tailTrace_286439 : CollatzResearch.WordTrace tailWord_286439 prefixEnd_286439 1815813397448272096237 := by
  unfold tailWord_286439
  simp only [CollatzResearch.WordTrace]
  refine ⟨10447288609287897731598371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6964859072858598487732247 10447288609287897731598371)
  ·
    refine ⟨15670932913931846597397557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10447288609287897731598371 15670932913931846597397557)
    ·
      refine ⟨1469149960681110618506021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15670932913931846597397557 1469149960681110618506021)
      ·
        refine ⟨275465617627708240969879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1469149960681110618506021 275465617627708240969879)
        ·
          refine ⟨413198426441562361454819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275465617627708240969879 413198426441562361454819)
          ·
            refine ⟨619797639662343542182229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413198426441562361454819 619797639662343542182229)
            ·
              refine ⟨1815813397448272096237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 619797639662343542182229 1815813397448272096237)
              ·
                rfl

theorem cell23_286439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 10].length) (baseStart_286439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286439 prefixEnd_286439 := by exact prefixLift 286439
  have htrace : WordTrace (prefixWord ++ tailWord_286439) baseStart_286439 baseEnd_286439 := by
    simpa [prefixWord, tailWord_286439, baseEnd_286439] using wordTrace_append hprefix tailTrace_286439
  have hstable : (prefixWord ++ tailWord_286439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286439).length < 2 ^ (prefixWord ++ tailWord_286439).sum := by decide
  have hdescent : baseEnd_286439 < baseStart_286439 := by decide
  rcases family_descends (prefixWord ++ tailWord_286439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286459 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 3, 3, 2]
def baseStart_286459 : Nat := 118140960795 + 286459 * 2 ^ 59
def prefixEnd_286459 : Nat := 4983230072969 + 3 ^ 40 * 286459 * 2
def baseEnd_286459 : Nat := 147091154806399961545105

theorem tailTrace_286459 : CollatzResearch.WordTrace tailWord_286459 prefixEnd_286459 147091154806399961545105 := by
  unfold tailWord_286459
  simp only [CollatzResearch.WordTrace]
  refine ⟨10448018069215441147326431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6965345379476960764884287 10448018069215441147326431)
  ·
    refine ⟨15672027103823161720989647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10448018069215441147326431 15672027103823161720989647)
    ·
      refine ⟨23508040655734742581484471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15672027103823161720989647 23508040655734742581484471)
      ·
        refine ⟨35262060983602113872226707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23508040655734742581484471 35262060983602113872226707)
        ·
          refine ⟨52893091475403170808340061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35262060983602113872226707 52893091475403170808340061)
          ·
            refine ⟨19834909303276189053127523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52893091475403170808340061 19834909303276189053127523)
            ·
              refine ⟨29752363954914283579691285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19834909303276189053127523 29752363954914283579691285)
              ·
                refine ⟨1394642060386607042798029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29752363954914283579691285 1394642060386607042798029)
                ·
                  refine ⟨522990772644977641049261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1394642060386607042798029 522990772644977641049261)
                  ·
                    refine ⟨196121539741866615393473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522990772644977641049261 196121539741866615393473)
                    ·
                      refine ⟨147091154806399961545105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196121539741866615393473 147091154806399961545105)
                      ·
                        rfl

theorem cell23_286459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3, 2].length) (baseStart_286459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286459 prefixEnd_286459 := by exact prefixLift 286459
  have htrace : WordTrace (prefixWord ++ tailWord_286459) baseStart_286459 baseEnd_286459 := by
    simpa [prefixWord, tailWord_286459, baseEnd_286459] using wordTrace_append hprefix tailTrace_286459
  have hstable : (prefixWord ++ tailWord_286459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286459).length < 2 ^ (prefixWord ++ tailWord_286459).sum := by decide
  have hdescent : baseEnd_286459 < baseStart_286459 := by decide
  rcases family_descends (prefixWord ++ tailWord_286459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286476 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 1, 3, 2]
def baseStart_286476 : Nat := 118140960795 + 286476 * 2 ^ 59
def prefixEnd_286476 : Nat := 4983230072969 + 3 ^ 40 * 286476 * 2
def baseEnd_286476 : Nat := 147099883977526395032527

theorem tailTrace_286476 : CollatzResearch.WordTrace tailWord_286476 prefixEnd_286476 147099883977526395032527 := by
  unfold tailWord_286476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224319055076926525347641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6965758740102568700463521 5224319055076926525347641)
  ·
    refine ⟨3918239291307694894010731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5224319055076926525347641 3918239291307694894010731)
    ·
      refine ⟨5877358936961542341016097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3918239291307694894010731 5877358936961542341016097)
      ·
        refine ⟨4408019202721156755762073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5877358936961542341016097 4408019202721156755762073)
        ·
          refine ⟨3306014402040867566821555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4408019202721156755762073 3306014402040867566821555)
          ·
            refine ⟨4959021603061301350232333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306014402040867566821555 4959021603061301350232333)
            ·
              refine ⟨1859633101147988006337125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4959021603061301350232333 1859633101147988006337125)
              ·
                refine ⟨348681206465247751188211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1859633101147988006337125 348681206465247751188211)
                ·
                  refine ⟨523021809697871626782317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348681206465247751188211 523021809697871626782317)
                  ·
                    refine ⟨196133178636701860043369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523021809697871626782317 196133178636701860043369)
                    ·
                      refine ⟨147099883977526395032527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196133178636701860043369 147099883977526395032527)
                      ·
                        rfl

theorem cell23_286476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_286476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286476 prefixEnd_286476 := by exact prefixLift 286476
  have htrace : WordTrace (prefixWord ++ tailWord_286476) baseStart_286476 baseEnd_286476 := by
    simpa [prefixWord, tailWord_286476, baseEnd_286476] using wordTrace_append hprefix tailTrace_286476
  have hstable : (prefixWord ++ tailWord_286476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286476).length < 2 ^ (prefixWord ++ tailWord_286476).sum := by decide
  have hdescent : baseEnd_286476 < baseStart_286476 := by decide
  rcases family_descends (prefixWord ++ tailWord_286476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286517 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_286517 : Nat := 118140960795 + 286517 * 2 ^ 59
def prefixEnd_286517 : Nat := 4983230072969 + 3 ^ 40 * 286517 * 2
def baseEnd_286517 : Nat := 147120936684360734619839

theorem tailTrace_286517 : CollatzResearch.WordTrace tailWord_286517 prefixEnd_286517 147120936684360734619839 := by
  unfold tailWord_286517
  simp only [CollatzResearch.WordTrace]
  refine ⟨10450133503005317052937805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6966755668670211368625203 10450133503005317052937805)
  ·
    refine ⟨3918800063626993894851677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10450133503005317052937805 3918800063626993894851677)
    ·
      refine ⟨1469550023860122710569379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3918800063626993894851677 1469550023860122710569379)
      ·
        refine ⟨2204325035790184065854069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469550023860122710569379 2204325035790184065854069)
        ·
          refine ⟨206655472105329756173819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2204325035790184065854069 206655472105329756173819)
          ·
            refine ⟨309983208157994634260729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206655472105329756173819 309983208157994634260729)
            ·
              refine ⟨232487406118495975695547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309983208157994634260729 232487406118495975695547)
              ·
                refine ⟨348731109177743963543321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232487406118495975695547 348731109177743963543321)
                ·
                  refine ⟨261548331883307972657491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348731109177743963543321 261548331883307972657491)
                  ·
                    refine ⟨392322497824961958986237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 261548331883307972657491 392322497824961958986237)
                    ·
                      refine ⟨147120936684360734619839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 392322497824961958986237 147120936684360734619839)
                      ·
                        rfl

theorem cell23_286517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_286517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286517 prefixEnd_286517 := by exact prefixLift 286517
  have htrace : WordTrace (prefixWord ++ tailWord_286517) baseStart_286517 baseEnd_286517 := by
    simpa [prefixWord, tailWord_286517, baseEnd_286517] using wordTrace_append hprefix tailTrace_286517
  have hstable : (prefixWord ++ tailWord_286517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286517).length < 2 ^ (prefixWord ++ tailWord_286517).sum := by decide
  have hdescent : baseEnd_286517 < baseStart_286517 := by decide
  rcases family_descends (prefixWord ++ tailWord_286517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286559 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 2, 5]
def baseStart_286559 : Nat := 118140960795 + 286559 * 2 ^ 59
def prefixEnd_286559 : Nat := 4983230072969 + 3 ^ 40 * 286559 * 2
def baseEnd_286559 : Nat := 49047500957283190098215

theorem tailTrace_286559 : CollatzResearch.WordTrace tailWord_286559 prefixEnd_286559 49047500957283190098215 := by
  unfold tailWord_286559
  simp only [CollatzResearch.WordTrace]
  refine ⟨10451665368853158225966731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6967776912568772150644487 10451665368853158225966731)
  ·
    refine ⟨15677498053279737338950097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10451665368853158225966731 15677498053279737338950097)
    ·
      refine ⟨11758123539959803004212573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15677498053279737338950097 11758123539959803004212573)
      ·
        refine ⟨4409296327484926126579715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11758123539959803004212573 4409296327484926126579715)
        ·
          refine ⟨6613944491227389189869573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409296327484926126579715 6613944491227389189869573)
          ·
            refine ⟨1240114592105135473100545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6613944491227389189869573 1240114592105135473100545)
            ·
              refine ⟨930085944078851604825409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240114592105135473100545 930085944078851604825409)
              ·
                refine ⟨697564458059138703619057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930085944078851604825409 697564458059138703619057)
                ·
                  refine ⟨523173343544354027714293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697564458059138703619057 523173343544354027714293)
                  ·
                    refine ⟨49047500957283190098215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 523173343544354027714293 49047500957283190098215)
                    ·
                      rfl

theorem cell23_286559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_286559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286559 prefixEnd_286559 := by exact prefixLift 286559
  have htrace : WordTrace (prefixWord ++ tailWord_286559) baseStart_286559 baseEnd_286559 := by
    simpa [prefixWord, tailWord_286559, baseEnd_286559] using wordTrace_append hprefix tailTrace_286559
  have hstable : (prefixWord ++ tailWord_286559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286559).length < 2 ^ (prefixWord ++ tailWord_286559).sum := by decide
  have hdescent : baseEnd_286559 < baseStart_286559 := by decide
  rcases family_descends (prefixWord ++ tailWord_286559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286596 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_286596 : Nat := 118140960795 + 286596 * 2 ^ 59
def prefixEnd_286596 : Nat := 4983230072969 + 3 ^ 40 * 286596 * 2
def baseEnd_286596 : Nat := 147161501656065925531975

theorem tailTrace_286596 : CollatzResearch.WordTrace tailWord_286596 prefixEnd_286596 147161501656065925531975 := by
  unfold tailWord_286596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226507434859556772531821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6968676579812742363375761 5226507434859556772531821)
  ·
    refine ⟨1959940288072333789699433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5226507434859556772531821 1959940288072333789699433)
    ·
      refine ⟨1469955216054250342274575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1959940288072333789699433 1469955216054250342274575)
      ·
        refine ⟨2204932824081375513411863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469955216054250342274575 2204932824081375513411863)
        ·
          refine ⟨3307399236122063270117795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204932824081375513411863 3307399236122063270117795)
          ·
            refine ⟨4961098854183094905176693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307399236122063270117795 4961098854183094905176693)
            ·
              refine ⟨465103017579665147360315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4961098854183094905176693 465103017579665147360315)
              ·
                refine ⟨697654526369497721040473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465103017579665147360315 697654526369497721040473)
                ·
                  refine ⟨523240894777123290780355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697654526369497721040473 523240894777123290780355)
                  ·
                    refine ⟨784861342165684936170533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523240894777123290780355 784861342165684936170533)
                    ·
                      refine ⟨147161501656065925531975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 784861342165684936170533 147161501656065925531975)
                      ·
                        rfl

theorem cell23_286596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_286596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286596 prefixEnd_286596 := by exact prefixLift 286596
  have htrace : WordTrace (prefixWord ++ tailWord_286596) baseStart_286596 baseEnd_286596 := by
    simpa [prefixWord, tailWord_286596, baseEnd_286596] using wordTrace_append hprefix tailTrace_286596
  have hstable : (prefixWord ++ tailWord_286596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286596).length < 2 ^ (prefixWord ++ tailWord_286596).sum := by decide
  have hdescent : baseEnd_286596 < baseStart_286596 := by decide
  rcases family_descends (prefixWord ++ tailWord_286596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286623 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 3, 4]
def baseStart_286623 : Nat := 118140960795 + 286623 * 2 ^ 59
def prefixEnd_286623 : Nat := 4983230072969 + 3 ^ 40 * 286623 * 2
def baseEnd_286623 : Nat := 49058455211245773298117

theorem tailTrace_286623 : CollatzResearch.WordTrace tailWord_286623 prefixEnd_286623 49058455211245773298117 := by
  unfold tailWord_286623
  simp only [CollatzResearch.WordTrace]
  refine ⟨10453999640621297156296523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6969333093747531437531015 10453999640621297156296523)
  ·
    refine ⟨15680999460931945734444785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10453999640621297156296523 15680999460931945734444785)
    ·
      refine ⟨11760749595698959300833589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15680999460931945734444785 11760749595698959300833589)
      ·
        refine ⟨1102570274596777434453149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11760749595698959300833589 1102570274596777434453149)
        ·
          refine ⟨413463852973791537919931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1102570274596777434453149 413463852973791537919931)
          ·
            refine ⟨620195779460687306879897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413463852973791537919931 620195779460687306879897)
            ·
              refine ⟨465146834595515480159923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620195779460687306879897 465146834595515480159923)
              ·
                refine ⟨697720251893273220239885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465146834595515480159923 697720251893273220239885)
                ·
                  refine ⟨261645094459977457589957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697720251893273220239885 261645094459977457589957)
                  ·
                    refine ⟨49058455211245773298117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261645094459977457589957 49058455211245773298117)
                    ·
                      rfl

theorem cell23_286623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_286623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286623 prefixEnd_286623 := by exact prefixLift 286623
  have htrace : WordTrace (prefixWord ++ tailWord_286623) baseStart_286623 baseEnd_286623 := by
    simpa [prefixWord, tailWord_286623, baseEnd_286623] using wordTrace_append hprefix tailTrace_286623
  have hstable : (prefixWord ++ tailWord_286623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286623).length < 2 ^ (prefixWord ++ tailWord_286623).sum := by decide
  have hdescent : baseEnd_286623 < baseStart_286623 := by decide
  rcases family_descends (prefixWord ++ tailWord_286623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286656 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 1, 5, 2]
def baseStart_286656 : Nat := 118140960795 + 286656 * 2 ^ 59
def prefixEnd_286656 : Nat := 4983230072969 + 3 ^ 40 * 286656 * 2
def baseEnd_286656 : Nat := 147192310495335690781699

theorem tailTrace_286656 : CollatzResearch.WordTrace tailWord_286656 prefixEnd_286656 147192310495335690781699 := by
  unfold tailWord_286656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227601624750871896123911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6970135499667829194831881 5227601624750871896123911)
  ·
    refine ⟨7841402437126307844185867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5227601624750871896123911 7841402437126307844185867)
    ·
      refine ⟨11762103655689461766278801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7841402437126307844185867 11762103655689461766278801)
      ·
        refine ⟨8821577741767096324709101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11762103655689461766278801 8821577741767096324709101)
        ·
          refine ⟨3308091653162661121765913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8821577741767096324709101 3308091653162661121765913)
          ·
            refine ⟨2481068739871995841324435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3308091653162661121765913 2481068739871995841324435)
            ·
              refine ⟨3721603109807993761986653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481068739871995841324435 3721603109807993761986653)
              ·
                refine ⟨1395601166177997660744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3721603109807993761986653 1395601166177997660744995)
                ·
                  refine ⟨2093401749266996491117493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395601166177997660744995 2093401749266996491117493)
                  ·
                    refine ⟨196256413993780921042265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2093401749266996491117493 196256413993780921042265)
                    ·
                      refine ⟨147192310495335690781699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196256413993780921042265 147192310495335690781699)
                      ·
                        rfl

theorem cell23_286656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_286656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286656 prefixEnd_286656 := by exact prefixLift 286656
  have htrace : WordTrace (prefixWord ++ tailWord_286656) baseStart_286656 baseEnd_286656 := by
    simpa [prefixWord, tailWord_286656, baseEnd_286656] using wordTrace_append hprefix tailTrace_286656
  have hstable : (prefixWord ++ tailWord_286656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286656).length < 2 ^ (prefixWord ++ tailWord_286656).sum := by decide
  have hdescent : baseEnd_286656 < baseStart_286656 := by decide
  rcases family_descends (prefixWord ++ tailWord_286656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286666 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_286666 : Nat := 118140960795 + 286666 * 2 ^ 59
def prefixEnd_286666 : Nat := 4983230072969 + 3 ^ 40 * 286666 * 2
def baseEnd_286666 : Nat := 49065815100626883885551

theorem tailTrace_286666 : CollatzResearch.WordTrace tailWord_286666 prefixEnd_286666 49065815100626883885551 := by
  unfold tailWord_286666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613891994866378875027963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6970378652977010333407901 2613891994866378875027963)
  ·
    refine ⟨3920837992299568312541945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613891994866378875027963 3920837992299568312541945)
    ·
      refine ⟨2940628494224676234406459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3920837992299568312541945 2940628494224676234406459)
      ·
        refine ⟨4410942741337014351609689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940628494224676234406459 4410942741337014351609689)
        ·
          refine ⟨3308207056002760763707267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4410942741337014351609689 3308207056002760763707267)
          ·
            refine ⟨4962310584004141145560901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308207056002760763707267 4962310584004141145560901)
            ·
              refine ⟨930433234500776464792669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4962310584004141145560901 930433234500776464792669)
              ·
                refine ⟨348912462937791174297251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930433234500776464792669 348912462937791174297251)
                ·
                  refine ⟨523368694406686761445877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348912462937791174297251 523368694406686761445877)
                  ·
                    refine ⟨49065815100626883885551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 523368694406686761445877 49065815100626883885551)
                    ·
                      rfl

theorem cell23_286666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_286666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286666 prefixEnd_286666 := by exact prefixLift 286666
  have htrace : WordTrace (prefixWord ++ tailWord_286666) baseStart_286666 baseEnd_286666 := by
    simpa [prefixWord, tailWord_286666, baseEnd_286666] using wordTrace_append hprefix tailTrace_286666
  have hstable : (prefixWord ++ tailWord_286666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286666).length < 2 ^ (prefixWord ++ tailWord_286666).sum := by decide
  have hdescent : baseEnd_286666 < baseStart_286666 := by decide
  rcases family_descends (prefixWord ++ tailWord_286666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286699 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4]
def baseStart_286699 : Nat := 118140960795 + 286699 * 2 ^ 59
def prefixEnd_286699 : Nat := 4983230072969 + 3 ^ 40 * 286699 * 2
def baseEnd_286699 : Nat := 147214390163479022544001

theorem tailTrace_286699 : CollatzResearch.WordTrace tailWord_286699 prefixEnd_286699 147214390163479022544001 := by
  unfold tailWord_286699
  simp only [CollatzResearch.WordTrace]
  refine ⟨10456771588345962136063151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6971181058897308090708767 10456771588345962136063151)
  ·
    refine ⟨15685157382518943204094727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10456771588345962136063151 15685157382518943204094727)
    ·
      refine ⟨23527736073778414806142091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15685157382518943204094727 23527736073778414806142091)
      ·
        refine ⟨35291604110667622209213137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23527736073778414806142091 35291604110667622209213137)
        ·
          refine ⟨26468703083000716656909853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35291604110667622209213137 26468703083000716656909853)
          ·
            refine ⟨9925763656125268746341195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26468703083000716656909853 9925763656125268746341195)
            ·
              refine ⟨14888645484187903119511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9925763656125268746341195 14888645484187903119511793)
              ·
                refine ⟨11166484113140927339633845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14888645484187903119511793 11166484113140927339633845)
                ·
                  refine ⟨1046857885606961938090673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11166484113140927339633845 1046857885606961938090673)
                  ·
                    refine ⟨785143414205221453568005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046857885606961938090673 785143414205221453568005)
                    ·
                      refine ⟨147214390163479022544001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 785143414205221453568005 147214390163479022544001)
                      ·
                        rfl

theorem cell23_286699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_286699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286699 prefixEnd_286699 := by exact prefixLift 286699
  have htrace : WordTrace (prefixWord ++ tailWord_286699) baseStart_286699 baseEnd_286699 := by
    simpa [prefixWord, tailWord_286699, baseEnd_286699] using wordTrace_append hprefix tailTrace_286699
  have hstable : (prefixWord ++ tailWord_286699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286699).length < 2 ^ (prefixWord ++ tailWord_286699).sum := by decide
  have hdescent : baseEnd_286699 < baseStart_286699 := by decide
  rcases family_descends (prefixWord ++ tailWord_286699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286703 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 5, 2, 2]
def baseStart_286703 : Nat := 118140960795 + 286703 * 2 ^ 59
def prefixEnd_286703 : Nat := 4983230072969 + 3 ^ 40 * 286703 * 2
def baseEnd_286703 : Nat := 147216444086097006893983

theorem tailTrace_286703 : CollatzResearch.WordTrace tailWord_286703 prefixEnd_286703 147216444086097006893983 := by
  unfold tailWord_286703
  simp only [CollatzResearch.WordTrace]
  refine ⟨10456917480331470819208763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6971278320220980546139175 10456917480331470819208763)
  ·
    refine ⟨15685376220497206228813145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10456917480331470819208763 15685376220497206228813145)
    ·
      refine ⟨11764032165372904671609859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15685376220497206228813145 11764032165372904671609859)
      ·
        refine ⟨17646048248059357007414789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11764032165372904671609859 17646048248059357007414789)
        ·
          refine ⟨3308634046511129438890273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17646048248059357007414789 3308634046511129438890273)
          ·
            refine ⟨2481475534883347079167705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3308634046511129438890273 2481475534883347079167705)
            ·
              refine ⟨1861106651162510309375779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2481475534883347079167705 1861106651162510309375779)
              ·
                refine ⟨2791659976743765464063669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861106651162510309375779 2791659976743765464063669)
                ·
                  refine ⟨261718122819728012255969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2791659976743765464063669 261718122819728012255969)
                  ·
                    refine ⟨196288592114796009191977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 261718122819728012255969 196288592114796009191977)
                    ·
                      refine ⟨147216444086097006893983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196288592114796009191977 147216444086097006893983)
                      ·
                        rfl

theorem cell23_286703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 2, 2].length) (baseStart_286703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286703 prefixEnd_286703 := by exact prefixLift 286703
  have htrace : WordTrace (prefixWord ++ tailWord_286703) baseStart_286703 baseEnd_286703 := by
    simpa [prefixWord, tailWord_286703, baseEnd_286703] using wordTrace_append hprefix tailTrace_286703
  have hstable : (prefixWord ++ tailWord_286703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286703).length < 2 ^ (prefixWord ++ tailWord_286703).sum := by decide
  have hdescent : baseEnd_286703 < baseStart_286703 := by decide
  rcases family_descends (prefixWord ++ tailWord_286703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286716 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_286716 : Nat := 118140960795 + 286716 * 2 ^ 59
def prefixEnd_286716 : Nat := 4983230072969 + 3 ^ 40 * 286716 * 2
def baseEnd_286716 : Nat := 147223119334605456031423

theorem tailTrace_286716 : CollatzResearch.WordTrace tailWord_286716 prefixEnd_286716 147223119334605456031423 := by
  unfold tailWord_286716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228695814642187019716001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6971594419522916026288001 5228695814642187019716001)
  ·
    refine ⟨3921521860981640264787001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5228695814642187019716001 3921521860981640264787001)
    ·
      refine ⟨2941141395736230198590251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3921521860981640264787001 2941141395736230198590251)
      ·
        refine ⟨4411712093604345297885377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941141395736230198590251 4411712093604345297885377)
        ·
          refine ⟨3308784070203258973414033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4411712093604345297885377 3308784070203258973414033)
          ·
            refine ⟨2481588052652444230060525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3308784070203258973414033 2481588052652444230060525)
            ·
              refine ⟨930595519744666586272697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2481588052652444230060525 930595519744666586272697)
              ·
                refine ⟨697946639808499939704523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930595519744666586272697 697946639808499939704523)
                ·
                  refine ⟨1046919959712749909556785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697946639808499939704523 1046919959712749909556785)
                  ·
                    refine ⟨785189969784562432167589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046919959712749909556785 785189969784562432167589)
                    ·
                      refine ⟨147223119334605456031423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 785189969784562432167589 147223119334605456031423)
                      ·
                        rfl

theorem cell23_286716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_286716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286716 prefixEnd_286716 := by exact prefixLift 286716
  have htrace : WordTrace (prefixWord ++ tailWord_286716) baseStart_286716 baseEnd_286716 := by
    simpa [prefixWord, tailWord_286716, baseEnd_286716] using wordTrace_append hprefix tailTrace_286716
  have hstable : (prefixWord ++ tailWord_286716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286716).length < 2 ^ (prefixWord ++ tailWord_286716).sum := by decide
  have hdescent : baseEnd_286716 < baseStart_286716 := by decide
  rcases family_descends (prefixWord ++ tailWord_286716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286730 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_286730 : Nat := 118140960795 + 286730 * 2 ^ 59
def prefixEnd_286730 : Nat := 4983230072969 + 3 ^ 40 * 286730 * 2
def baseEnd_286730 : Nat := 49076769354589467085453

theorem tailTrace_286730 : CollatzResearch.WordTrace tailWord_286730 prefixEnd_286730 49076769354589467085453 := by
  unfold tailWord_286730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614475562808413607610411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6971934834155769620294429 2614475562808413607610411)
  ·
    refine ⟨3921713344212620411415617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2614475562808413607610411 3921713344212620411415617)
    ·
      refine ⟨2941285008159465308561713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3921713344212620411415617 2941285008159465308561713)
      ·
        refine ⟨2205963756119598981421285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2941285008159465308561713 2205963756119598981421285)
        ·
          refine ⟨413618204272424809016491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2205963756119598981421285 413618204272424809016491)
          ·
            refine ⟨620427306408637213524737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413618204272424809016491 620427306408637213524737)
            ·
              refine ⟨465320479806477910143553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620427306408637213524737 465320479806477910143553)
              ·
                refine ⟨348990359854858432607665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465320479806477910143553 348990359854858432607665)
                ·
                  refine ⟨261742769891143824455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348990359854858432607665 261742769891143824455749)
                  ·
                    refine ⟨49076769354589467085453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261742769891143824455749 49076769354589467085453)
                    ·
                      rfl

theorem cell23_286730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_286730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286730 prefixEnd_286730 := by exact prefixLift 286730
  have htrace : WordTrace (prefixWord ++ tailWord_286730) baseStart_286730 baseEnd_286730 := by
    simpa [prefixWord, tailWord_286730, baseEnd_286730] using wordTrace_append hprefix tailTrace_286730
  have hstable : (prefixWord ++ tailWord_286730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286730).length < 2 ^ (prefixWord ++ tailWord_286730).sum := by decide
  have hdescent : baseEnd_286730 < baseStart_286730 := by decide
  rcases family_descends (prefixWord ++ tailWord_286730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286739 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 2, 7]
def baseStart_286739 : Nat := 118140960795 + 286739 * 2 ^ 59
def prefixEnd_286739 : Nat := 4983230072969 + 3 ^ 40 * 286739 * 2
def baseEnd_286739 : Nat := 49078309796552955347939

theorem tailTrace_286739 : CollatzResearch.WordTrace tailWord_286739 prefixEnd_286739 49078309796552955347939 := by
  unfold tailWord_286739
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458230508201048967519271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6972153672134032645012847 10458230508201048967519271)
  ·
    refine ⟨15687345762301573451278907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10458230508201048967519271 15687345762301573451278907)
    ·
      refine ⟨23531018643452360176918361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15687345762301573451278907 23531018643452360176918361)
      ·
        refine ⟨17648263982589270132688771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23531018643452360176918361 17648263982589270132688771)
        ·
          refine ⟨26472395973883905199033157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17648263982589270132688771 26472395973883905199033157)
          ·
            refine ⟨4963574245103232224818717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26472395973883905199033157 4963574245103232224818717)
            ·
              refine ⟨1861340341913712084307019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4963574245103232224818717 1861340341913712084307019)
              ·
                refine ⟨2792010512870568126460529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861340341913712084307019 2792010512870568126460529)
                ·
                  refine ⟨2094007884652926094845397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2792010512870568126460529 2094007884652926094845397)
                  ·
                    refine ⟨49078309796552955347939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2094007884652926094845397 49078309796552955347939)
                    ·
                      rfl

theorem cell23_286739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_286739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286739 prefixEnd_286739 := by exact prefixLift 286739
  have htrace : WordTrace (prefixWord ++ tailWord_286739) baseStart_286739 baseEnd_286739 := by
    simpa [prefixWord, tailWord_286739, baseEnd_286739] using wordTrace_append hprefix tailTrace_286739
  have hstable : (prefixWord ++ tailWord_286739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286739).length < 2 ^ (prefixWord ++ tailWord_286739).sum := by decide
  have hdescent : baseEnd_286739 < baseStart_286739 := by decide
  rcases family_descends (prefixWord ++ tailWord_286739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286743 : List Nat := [1, 1, 3, 5, 2, 2, 1, 8]
def baseStart_286743 : Nat := 118140960795 + 286743 * 2 ^ 59
def prefixEnd_286743 : Nat := 4983230072969 + 3 ^ 40 * 286743 * 2
def baseEnd_286743 : Nat := 5453221604158401866437

theorem tailTrace_286743 : CollatzResearch.WordTrace tailWord_286743 prefixEnd_286743 5453221604158401866437 := by
  unfold tailWord_286743
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458376400186557650664883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6972250933457705100443255 10458376400186557650664883)
  ·
    refine ⟨15687564600279836475997325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10458376400186557650664883 15687564600279836475997325)
    ·
      refine ⟨5882836725104938678498997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15687564600279836475997325 5882836725104938678498997)
      ·
        refine ⟨551515942978588001109281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5882836725104938678498997 551515942978588001109281)
        ·
          refine ⟨413636957233941000831961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551515942978588001109281 413636957233941000831961)
          ·
            refine ⟨310227717925455750623971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413636957233941000831961 310227717925455750623971)
            ·
              refine ⟨465341576888183625935957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310227717925455750623971 465341576888183625935957)
              ·
                refine ⟨5453221604158401866437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 465341576888183625935957 5453221604158401866437)
                ·
                  rfl

theorem cell23_286743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 8].length) (baseStart_286743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286743 prefixEnd_286743 := by exact prefixLift 286743
  have htrace : WordTrace (prefixWord ++ tailWord_286743) baseStart_286743 baseEnd_286743 := by
    simpa [prefixWord, tailWord_286743, baseEnd_286743] using wordTrace_append hprefix tailTrace_286743
  have hstable : (prefixWord ++ tailWord_286743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286743).length < 2 ^ (prefixWord ++ tailWord_286743).sum := by decide
  have hdescent : baseEnd_286743 < baseStart_286743 := by decide
  rcases family_descends (prefixWord ++ tailWord_286743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286760 : List Nat := [2, 1, 5, 3, 1, 1, 3, 7]
def baseStart_286760 : Nat := 118140960795 + 286760 * 2 ^ 59
def prefixEnd_286760 : Nat := 4983230072969 + 3 ^ 40 * 286760 * 2
def baseEnd_286760 : Nat := 5453544906792714217823

theorem tailTrace_286760 : CollatzResearch.WordTrace tailWord_286760 prefixEnd_286760 5453544906792714217823 := by
  unfold tailWord_286760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229498220562484777016867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6972664294083313036022489 5229498220562484777016867)
  ·
    refine ⟨7844247330843727165525301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5229498220562484777016867 7844247330843727165525301)
    ·
      refine ⟨735398187266599421767997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7844247330843727165525301 735398187266599421767997)
      ·
        refine ⟨275774320224974783162999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 735398187266599421767997 275774320224974783162999)
        ·
          refine ⟨413661480337462174744499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275774320224974783162999 413661480337462174744499)
          ·
            refine ⟨620492220506193262116749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413661480337462174744499 620492220506193262116749)
            ·
              refine ⟨232684582689822473293781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620492220506193262116749 232684582689822473293781)
              ·
                refine ⟨5453544906792714217823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232684582689822473293781 5453544906792714217823)
                ·
                  rfl

theorem cell23_286760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 7].length) (baseStart_286760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286760 prefixEnd_286760 := by exact prefixLift 286760
  have htrace : WordTrace (prefixWord ++ tailWord_286760) baseStart_286760 baseEnd_286760 := by
    simpa [prefixWord, tailWord_286760, baseEnd_286760] using wordTrace_append hprefix tailTrace_286760
  have hstable : (prefixWord ++ tailWord_286760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286760).length < 2 ^ (prefixWord ++ tailWord_286760).sum := by decide
  have hdescent : baseEnd_286760 < baseStart_286760 := by decide
  rcases family_descends (prefixWord ++ tailWord_286760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286780 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_286780 : Nat := 118140960795 + 286780 * 2 ^ 59
def prefixEnd_286780 : Nat := 4983230072969 + 3 ^ 40 * 286780 * 2
def baseEnd_286780 : Nat := 147255982096493205631129

theorem tailTrace_286780 : CollatzResearch.WordTrace tailWord_286780 prefixEnd_286780 147255982096493205631129 := by
  unfold tailWord_286780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229862950526256484880897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6973150600701675313174529 5229862950526256484880897)
  ·
    refine ⟨3922397212894692363660673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5229862950526256484880897 3922397212894692363660673)
    ·
      refine ⟨2941797909671019272745505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3922397212894692363660673 2941797909671019272745505)
      ·
        refine ⟨2206348432253264454559129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2941797909671019272745505 2206348432253264454559129)
        ·
          refine ⟨1654761324189948340919347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2206348432253264454559129 1654761324189948340919347)
          ·
            refine ⟨2482141986284922511379021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654761324189948340919347 2482141986284922511379021)
            ·
              refine ⟨930803244856845941767133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2482141986284922511379021 930803244856845941767133)
              ·
                refine ⟨349051216821317228162675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930803244856845941767133 349051216821317228162675)
                ·
                  refine ⟨523576825231975842244013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349051216821317228162675 523576825231975842244013)
                  ·
                    refine ⟨196341309461990940841505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523576825231975842244013 196341309461990940841505)
                    ·
                      refine ⟨147255982096493205631129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196341309461990940841505 147255982096493205631129)
                      ·
                        rfl

theorem cell23_286780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_286780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286780 prefixEnd_286780 := by exact prefixLift 286780
  have htrace : WordTrace (prefixWord ++ tailWord_286780) baseStart_286780 baseEnd_286780 := by
    simpa [prefixWord, tailWord_286780, baseEnd_286780] using wordTrace_append hprefix tailTrace_286780
  have hstable : (prefixWord ++ tailWord_286780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286780).length < 2 ^ (prefixWord ++ tailWord_286780).sum := by decide
  have hdescent : baseEnd_286780 < baseStart_286780 := by decide
  rcases family_descends (prefixWord ++ tailWord_286780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286796 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_286796 : Nat := 118140960795 + 286796 * 2 ^ 59
def prefixEnd_286796 : Nat := 4983230072969 + 3 ^ 40 * 286796 * 2
def baseEnd_286796 : Nat := 147264197786965143031055

theorem tailTrace_286796 : CollatzResearch.WordTrace tailWord_286796 prefixEnd_286796 147264197786965143031055 := by
  unfold tailWord_286796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230154734497273851172121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6973539645996365134896161 5230154734497273851172121)
  ·
    refine ⟨3922616050872955388379091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5230154734497273851172121 3922616050872955388379091)
    ·
      refine ⟨5883924076309433082568637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3922616050872955388379091 5883924076309433082568637)
      ·
        refine ⟨2206471528616037405963239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5883924076309433082568637 2206471528616037405963239)
        ·
          refine ⟨3309707292924056108944859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206471528616037405963239 3309707292924056108944859)
          ·
            refine ⟨4964560939386084163417289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309707292924056108944859 4964560939386084163417289)
            ·
              refine ⟨3723420704539563122562967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4964560939386084163417289 3723420704539563122562967)
              ·
                refine ⟨5585131056809344683844451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723420704539563122562967 5585131056809344683844451)
                ·
                  refine ⟨8377696585214017025766677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5585131056809344683844451 8377696585214017025766677)
                  ·
                    refine ⟨392704527431907048082813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8377696585214017025766677 392704527431907048082813)
                    ·
                      refine ⟨147264197786965143031055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 392704527431907048082813 147264197786965143031055)
                      ·
                        rfl

theorem cell23_286796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_286796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286796 prefixEnd_286796 := by exact prefixLift 286796
  have htrace : WordTrace (prefixWord ++ tailWord_286796) baseStart_286796 baseEnd_286796 := by
    simpa [prefixWord, tailWord_286796, baseEnd_286796] using wordTrace_append hprefix tailTrace_286796
  have hstable : (prefixWord ++ tailWord_286796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286796).length < 2 ^ (prefixWord ++ tailWord_286796).sum := by decide
  have hdescent : baseEnd_286796 < baseStart_286796 := by decide
  rcases family_descends (prefixWord ++ tailWord_286796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286799 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 11]
def baseStart_286799 : Nat := 118140960795 + 286799 * 2 ^ 59
def prefixEnd_286799 : Nat := 4983230072969 + 3 ^ 40 * 286799 * 2
def baseEnd_286799 : Nat := 16362859803214292365949

theorem tailTrace_286799 : CollatzResearch.WordTrace tailWord_286799 prefixEnd_286799 16362859803214292365949 := by
  unfold tailWord_286799
  simp only [CollatzResearch.WordTrace]
  refine ⟨10460418887983679214703451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6973612591989119476468967 10460418887983679214703451)
  ·
    refine ⟨15690628331975518822055177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10460418887983679214703451 15690628331975518822055177)
    ·
      refine ⟨11767971248981639116541383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15690628331975518822055177 11767971248981639116541383)
      ·
        refine ⟨17651956873472458674812075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11767971248981639116541383 17651956873472458674812075)
        ·
          refine ⟨26477935310208688012218113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17651956873472458674812075 26477935310208688012218113)
          ·
            refine ⟨19858451482656516009163585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26477935310208688012218113 19858451482656516009163585)
            ·
              refine ⟨14893838611992387006872689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19858451482656516009163585 14893838611992387006872689)
              ·
                refine ⟨11170378958994290255154517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14893838611992387006872689 11170378958994290255154517)
                ·
                  refine ⟨16362859803214292365949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 11170378958994290255154517 16362859803214292365949)
                  ·
                    rfl

theorem cell23_286799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 11].length) (baseStart_286799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286799 prefixEnd_286799 := by exact prefixLift 286799
  have htrace : WordTrace (prefixWord ++ tailWord_286799) baseStart_286799 baseEnd_286799 := by
    simpa [prefixWord, tailWord_286799, baseEnd_286799] using wordTrace_append hprefix tailTrace_286799
  have hstable : (prefixWord ++ tailWord_286799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286799).length < 2 ^ (prefixWord ++ tailWord_286799).sum := by decide
  have hdescent : baseEnd_286799 < baseStart_286799 := by decide
  rcases family_descends (prefixWord ++ tailWord_286799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286816 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 7]
def baseStart_286816 : Nat := 118140960795 + 286816 * 2 ^ 59
def prefixEnd_286816 : Nat := 4983230072969 + 3 ^ 40 * 286816 * 2
def baseEnd_286816 : Nat := 16363829711117229420107

theorem tailTrace_286816 : CollatzResearch.WordTrace tailWord_286816 prefixEnd_286816 16363829711117229420107 := by
  unfold tailWord_286816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230519464461045559036151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6974025952614727412048201 5230519464461045559036151)
  ·
    refine ⟨7845779196691568338554227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5230519464461045559036151 7845779196691568338554227)
    ·
      refine ⟨11768668795037352507831341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7845779196691568338554227 11768668795037352507831341)
      ·
        refine ⟨4413250798139007190436753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11768668795037352507831341 4413250798139007190436753)
        ·
          refine ⟨3309938098604255392827565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4413250798139007190436753 3309938098604255392827565)
          ·
            refine ⟨1241226786976595772310337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3309938098604255392827565 1241226786976595772310337)
            ·
              refine ⟨930920090232446829232753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241226786976595772310337 930920090232446829232753)
              ·
                refine ⟨698190067674335121924565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930920090232446829232753 698190067674335121924565)
                ·
                  refine ⟨16363829711117229420107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 698190067674335121924565 16363829711117229420107)
                  ·
                    rfl

theorem cell23_286816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_286816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286816 prefixEnd_286816 := by exact prefixLift 286816
  have htrace : WordTrace (prefixWord ++ tailWord_286816) baseStart_286816 baseEnd_286816 := by
    simpa [prefixWord, tailWord_286816, baseEnd_286816] using wordTrace_append hprefix tailTrace_286816
  have hstable : (prefixWord ++ tailWord_286816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286816).length < 2 ^ (prefixWord ++ tailWord_286816).sum := by decide
  have hdescent : baseEnd_286816 < baseStart_286816 := by decide
  rcases family_descends (prefixWord ++ tailWord_286816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286883 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 6, 4, 2]
def baseStart_286883 : Nat := 118140960795 + 286883 * 2 ^ 59
def prefixEnd_286883 : Nat := 4983230072969 + 3 ^ 40 * 286883 * 2
def baseEnd_286883 : Nat := 147308870603906302643155

theorem tailTrace_286883 : CollatzResearch.WordTrace tailWord_286883 prefixEnd_286883 147308870603906302643155 := by
  unfold tailWord_286883
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463482619679361560761303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6975655079786241040507535 10463482619679361560761303)
  ·
    refine ⟨15695223929519042341141955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10463482619679361560761303 15695223929519042341141955)
    ·
      refine ⟨23542835894278563511712933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15695223929519042341141955 23542835894278563511712933)
      ·
        refine ⟨4414281730177230658446175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23542835894278563511712933 4414281730177230658446175)
        ·
          refine ⟨6621422595265845987669263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414281730177230658446175 6621422595265845987669263)
          ·
            refine ⟨9932133892898768981503895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621422595265845987669263 9932133892898768981503895)
            ·
              refine ⟨14898200839348153472255843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9932133892898768981503895 14898200839348153472255843)
              ·
                refine ⟨22347301259022230208383765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14898200839348153472255843 22347301259022230208383765)
                ·
                  refine ⟨1047529746516667041017989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22347301259022230208383765 1047529746516667041017989)
                  ·
                    refine ⟨196411827471875070190873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047529746516667041017989 196411827471875070190873)
                    ·
                      refine ⟨147308870603906302643155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196411827471875070190873 147308870603906302643155)
                      ·
                        rfl

theorem cell23_286883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_286883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286883 prefixEnd_286883 := by exact prefixLift 286883
  have htrace : WordTrace (prefixWord ++ tailWord_286883) baseStart_286883 baseEnd_286883 := by
    simpa [prefixWord, tailWord_286883, baseEnd_286883] using wordTrace_append hprefix tailTrace_286883
  have hstable : (prefixWord ++ tailWord_286883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286883).length < 2 ^ (prefixWord ++ tailWord_286883).sum := by decide
  have hdescent : baseEnd_286883 < baseStart_286883 := by decide
  rcases family_descends (prefixWord ++ tailWord_286883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286901 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 5]
def baseStart_286901 : Nat := 118140960795 + 286901 * 2 ^ 59
def prefixEnd_286901 : Nat := 4983230072969 + 3 ^ 40 * 286901 * 2
def baseEnd_286901 : Nat := 16368679250631914690897

theorem tailTrace_286901 : CollatzResearch.WordTrace tailWord_286901 prefixEnd_286901 16368679250631914690897 := by
  unfold tailWord_286901
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464139133614150634916557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6976092755742767089944371 10464139133614150634916557)
  ·
    refine ⟨3924052175105306488093709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10464139133614150634916557 3924052175105306488093709)
    ·
      refine ⟨1471519565664489933035141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3924052175105306488093709 1471519565664489933035141)
      ·
        refine ⟨275909918562091862444089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1471519565664489933035141 275909918562091862444089)
        ·
          refine ⟨206932438921568896833067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275909918562091862444089 206932438921568896833067)
          ·
            refine ⟨310398658382353345249601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206932438921568896833067 310398658382353345249601)
            ·
              refine ⟨232798993786765008937201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310398658382353345249601 232798993786765008937201)
              ·
                refine ⟨174599245340073756702901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232798993786765008937201 174599245340073756702901)
                ·
                  refine ⟨16368679250631914690897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174599245340073756702901 16368679250631914690897)
                  ·
                    rfl

theorem cell23_286901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_286901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286901 prefixEnd_286901 := by exact prefixLift 286901
  have htrace : WordTrace (prefixWord ++ tailWord_286901) baseStart_286901 baseEnd_286901 := by
    simpa [prefixWord, tailWord_286901, baseEnd_286901] using wordTrace_append hprefix tailTrace_286901
  have hstable : (prefixWord ++ tailWord_286901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286901).length < 2 ^ (prefixWord ++ tailWord_286901).sum := by decide
  have hdescent : baseEnd_286901 < baseStart_286901 := by decide
  rcases family_descends (prefixWord ++ tailWord_286901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286906 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_286906 : Nat := 118140960795 + 286906 * 2 ^ 59
def prefixEnd_286906 : Nat := 4983230072969 + 3 ^ 40 * 286906 * 2
def baseEnd_286906 : Nat := 16368964517662190295061

theorem tailTrace_286906 : CollatzResearch.WordTrace tailWord_286906 prefixEnd_286906 16368964517662190295061 := by
  unfold tailWord_286906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616080374649009122212143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6976214332397357659232381 2616080374649009122212143)
  ·
    refine ⟨3924120561973513683318215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2616080374649009122212143 3924120561973513683318215)
    ·
      refine ⟨5886180842960270524977323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3924120561973513683318215 5886180842960270524977323)
      ·
        refine ⟨8829271264440405787465985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5886180842960270524977323 8829271264440405787465985)
        ·
          refine ⟨6621953448330304340599489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8829271264440405787465985 6621953448330304340599489)
          ·
            refine ⟨4966465086247728255449617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6621953448330304340599489 4966465086247728255449617)
            ·
              refine ⟨3724848814685796191587213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966465086247728255449617 3724848814685796191587213)
              ·
                refine ⟨1396818305507173571845205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3724848814685796191587213 1396818305507173571845205)
                ·
                  refine ⟨16368964517662190295061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1396818305507173571845205 16368964517662190295061)
                  ·
                    rfl

theorem cell23_286906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_286906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286906 prefixEnd_286906 := by exact prefixLift 286906
  have htrace : WordTrace (prefixWord ++ tailWord_286906) baseStart_286906 baseEnd_286906 := by
    simpa [prefixWord, tailWord_286906, baseEnd_286906] using wordTrace_append hprefix tailTrace_286906
  have hstable : (prefixWord ++ tailWord_286906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286906).length < 2 ^ (prefixWord ++ tailWord_286906).sum := by decide
  have hdescent : baseEnd_286906 < baseStart_286906 := by decide
  rcases family_descends (prefixWord ++ tailWord_286906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286934 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_286934 : Nat := 118140960795 + 286934 * 2 ^ 59
def prefixEnd_286934 : Nat := 4983230072969 + 3 ^ 40 * 286934 * 2
def baseEnd_286934 : Nat := 147335058117285603105421

theorem tailTrace_286934 : CollatzResearch.WordTrace tailWord_286934 prefixEnd_286934 147335058117285603105421 := by
  unfold tailWord_286934
  simp only [CollatzResearch.WordTrace]
  refine ⟨654083921405912329429241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6976895161663064847245237 654083921405912329429241)
  ·
    refine ⟨490562941054434247071931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 654083921405912329429241 490562941054434247071931)
    ·
      refine ⟨735844411581651370607897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490562941054434247071931 735844411581651370607897)
      ·
        refine ⟨551883308686238527955923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 735844411581651370607897 551883308686238527955923)
        ·
          refine ⟨827824963029357791933885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551883308686238527955923 827824963029357791933885)
          ·
            refine ⟨310434361136009171975207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 827824963029357791933885 310434361136009171975207)
            ·
              refine ⟨465651541704013757962811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310434361136009171975207 465651541704013757962811)
              ·
                refine ⟨698477312556020636944217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465651541704013757962811 698477312556020636944217)
                ·
                  refine ⟨523857984417015477708163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 698477312556020636944217 523857984417015477708163)
                  ·
                    refine ⟨785786976625523216562245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523857984417015477708163 785786976625523216562245)
                    ·
                      refine ⟨147335058117285603105421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 785786976625523216562245 147335058117285603105421)
                      ·
                        rfl

theorem cell23_286934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_286934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286934 prefixEnd_286934 := by exact prefixLift 286934
  have htrace : WordTrace (prefixWord ++ tailWord_286934) baseStart_286934 baseEnd_286934 := by
    simpa [prefixWord, tailWord_286934, baseEnd_286934] using wordTrace_append hprefix tailTrace_286934
  have hstable : (prefixWord ++ tailWord_286934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286934).length < 2 ^ (prefixWord ++ tailWord_286934).sum := by decide
  have hdescent : baseEnd_286934 < baseStart_286934 := by decide
  rcases family_descends (prefixWord ++ tailWord_286934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286953 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 1, 5]
def baseStart_286953 : Nat := 118140960795 + 286953 * 2 ^ 59
def prefixEnd_286953 : Nat := 4983230072969 + 3 ^ 40 * 286953 * 2
def baseEnd_286953 : Nat := 49114938083240342922611

theorem tailTrace_286953 : CollatzResearch.WordTrace tailWord_286953 prefixEnd_286953 49114938083240342922611 := by
  unfold tailWord_286953
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466035729425763515809513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6977357152950509010539675 10466035729425763515809513)
  ·
    refine ⟨7849526797069322636857135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10466035729425763515809513 7849526797069322636857135)
    ·
      refine ⟨11774290195603983955285703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7849526797069322636857135 11774290195603983955285703)
      ·
        refine ⟨17661435293405975932928555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11774290195603983955285703 17661435293405975932928555)
        ·
          refine ⟨26492152940108963899392833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17661435293405975932928555 26492152940108963899392833)
          ·
            refine ⟨19869114705081722924544625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26492152940108963899392833 19869114705081722924544625)
            ·
              refine ⟨14901836028811292193408469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19869114705081722924544625 14901836028811292193408469)
              ·
                refine ⟨349261781925264660783011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14901836028811292193408469 349261781925264660783011)
                ·
                  refine ⟨523892672887896991174517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349261781925264660783011 523892672887896991174517)
                  ·
                    refine ⟨49114938083240342922611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 523892672887896991174517 49114938083240342922611)
                    ·
                      rfl

theorem cell23_286953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_286953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286953 prefixEnd_286953 := by exact prefixLift 286953
  have htrace : WordTrace (prefixWord ++ tailWord_286953) baseStart_286953 baseEnd_286953 := by
    simpa [prefixWord, tailWord_286953, baseEnd_286953] using wordTrace_append hprefix tailTrace_286953
  have hstable : (prefixWord ++ tailWord_286953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286953).length < 2 ^ (prefixWord ++ tailWord_286953).sum := by decide
  have hdescent : baseEnd_286953 < baseStart_286953 := by decide
  rcases family_descends (prefixWord ++ tailWord_286953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286957 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 6]
def baseStart_286957 : Nat := 118140960795 + 286957 * 2 ^ 59
def prefixEnd_286957 : Nat := 4983230072969 + 3 ^ 40 * 286957 * 2
def baseEnd_286957 : Nat := 16371874241371001457535

theorem tailTrace_286957 : CollatzResearch.WordTrace tailWord_286957 prefixEnd_286957 16371874241371001457535 := by
  unfold tailWord_286957
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466181621411272198955125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6977454414274181465970083 10466181621411272198955125)
  ·
    refine ⟨981204527007306768652043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10466181621411272198955125 981204527007306768652043)
    ·
      refine ⟨1471806790510960152978065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981204527007306768652043 1471806790510960152978065)
      ·
        refine ⟨1103855092883220114733549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1471806790510960152978065 1103855092883220114733549)
        ·
          refine ⟨413945659831207543025081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1103855092883220114733549 413945659831207543025081)
          ·
            refine ⟨310459244873405657268811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413945659831207543025081 310459244873405657268811)
            ·
              refine ⟨465688867310108485903217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310459244873405657268811 465688867310108485903217)
              ·
                refine ⟨349266650482581364427413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465688867310108485903217 349266650482581364427413)
                ·
                  refine ⟨16371874241371001457535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 349266650482581364427413 16371874241371001457535)
                  ·
                    rfl

theorem cell23_286957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_286957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286957 prefixEnd_286957 := by exact prefixLift 286957
  have htrace : WordTrace (prefixWord ++ tailWord_286957) baseStart_286957 baseEnd_286957 := by
    simpa [prefixWord, tailWord_286957, baseEnd_286957] using wordTrace_append hprefix tailTrace_286957
  have hstable : (prefixWord ++ tailWord_286957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286957).length < 2 ^ (prefixWord ++ tailWord_286957).sum := by decide
  have hdescent : baseEnd_286957 < baseStart_286957 := by decide
  rcases family_descends (prefixWord ++ tailWord_286957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286960 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 2, 3, 2]
def baseStart_286960 : Nat := 118140960795 + 286960 * 2 ^ 59
def prefixEnd_286960 : Nat := 4983230072969 + 3 ^ 40 * 286960 * 2
def baseEnd_286960 : Nat := 147348408614302501380301

theorem tailTrace_286960 : CollatzResearch.WordTrace tailWord_286960 prefixEnd_286960 147348408614302501380301 := by
  unfold tailWord_286960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233145520200201855657167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6977527360266935807542889 5233145520200201855657167)
  ·
    refine ⟨7849718280300302783485751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5233145520200201855657167 7849718280300302783485751)
    ·
      refine ⟨11774577420450454175228627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7849718280300302783485751 11774577420450454175228627)
      ·
        refine ⟨17661866130675681262842941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11774577420450454175228627 17661866130675681262842941)
        ·
          refine ⟨6623199799003380473566103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17661866130675681262842941 6623199799003380473566103)
          ·
            refine ⟨9934799698505070710349155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623199799003380473566103 9934799698505070710349155)
            ·
              refine ⟨14902199547757606065523733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9934799698505070710349155 14902199547757606065523733)
              ·
                refine ⟨698540603801137784321425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14902199547757606065523733 698540603801137784321425)
                ·
                  refine ⟨523905452850853338241069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 698540603801137784321425 523905452850853338241069)
                  ·
                    refine ⟨196464544819070001840401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523905452850853338241069 196464544819070001840401)
                    ·
                      refine ⟨147348408614302501380301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196464544819070001840401 147348408614302501380301)
                      ·
                        rfl

theorem cell23_286960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 3, 2].length) (baseStart_286960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286960 prefixEnd_286960 := by exact prefixLift 286960
  have htrace : WordTrace (prefixWord ++ tailWord_286960) baseStart_286960 baseEnd_286960 := by
    simpa [prefixWord, tailWord_286960, baseEnd_286960] using wordTrace_append hprefix tailTrace_286960
  have hstable : (prefixWord ++ tailWord_286960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286960).length < 2 ^ (prefixWord ++ tailWord_286960).sum := by decide
  have hdescent : baseEnd_286960 < baseStart_286960 := by decide
  rcases family_descends (prefixWord ++ tailWord_286960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286973 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_286973 : Nat := 118140960795 + 286973 * 2 ^ 59
def prefixEnd_286973 : Nat := 4983230072969 + 3 ^ 40 * 286973 * 2
def baseEnd_286973 : Nat := 147355083862810950517741

theorem tailTrace_286973 : CollatzResearch.WordTrace tailWord_286973 prefixEnd_286973 147355083862810950517741 := by
  unfold tailWord_286973
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466765189353306931537573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6977843459568871287691715 10466765189353306931537573)
  ·
    refine ⟨1962518473003745049663295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10466765189353306931537573 1962518473003745049663295)
    ·
      refine ⟨2943777709505617574494943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962518473003745049663295 2943777709505617574494943)
      ·
        refine ⟨4415666564258426361742415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943777709505617574494943 4415666564258426361742415)
        ·
          refine ⟨6623499846387639542613623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4415666564258426361742415 6623499846387639542613623)
          ·
            refine ⟨9935249769581459313920435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623499846387639542613623 9935249769581459313920435)
            ·
              refine ⟨14902874654372188970880653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9935249769581459313920435 14902874654372188970880653)
              ·
                refine ⟨5588577995389570864080245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14902874654372188970880653 5588577995389570864080245)
                ·
                  refine ⟨523929187067772268507523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5588577995389570864080245 523929187067772268507523)
                  ·
                    refine ⟨785893780601658402761285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523929187067772268507523 785893780601658402761285)
                    ·
                      refine ⟨147355083862810950517741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 785893780601658402761285 147355083862810950517741)
                      ·
                        rfl

theorem cell23_286973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_286973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286973 prefixEnd_286973 := by exact prefixLift 286973
  have htrace : WordTrace (prefixWord ++ tailWord_286973) baseStart_286973 baseEnd_286973 := by
    simpa [prefixWord, tailWord_286973, baseEnd_286973] using wordTrace_append hprefix tailTrace_286973
  have hstable : (prefixWord ++ tailWord_286973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286973).length < 2 ^ (prefixWord ++ tailWord_286973).sum := by decide
  have hdescent : baseEnd_286973 < baseStart_286973 := by decide
  rcases family_descends (prefixWord ++ tailWord_286973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286990 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_286990 : Nat := 118140960795 + 286990 * 2 ^ 59
def prefixEnd_286990 : Nat := 4983230072969 + 3 ^ 40 * 286990 * 2
def baseEnd_286990 : Nat := 147363813033937384005163

theorem tailTrace_286990 : CollatzResearch.WordTrace tailWord_286990 prefixEnd_286990 147363813033937384005163 := by
  unfold tailWord_286990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308423153786464854363303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6978256820194479223270949 1308423153786464854363303)
  ·
    refine ⟨1962634730679697281544955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1308423153786464854363303 1962634730679697281544955)
    ·
      refine ⟨2943952096019545922317433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962634730679697281544955 2943952096019545922317433)
      ·
        refine ⟨2207964072014659441738075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2943952096019545922317433 2207964072014659441738075)
        ·
          refine ⟨3311946108021989162607113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207964072014659441738075 3311946108021989162607113)
          ·
            refine ⟨2483959581016491871955335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3311946108021989162607113 2483959581016491871955335)
            ·
              refine ⟨3725939371524737807933003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483959581016491871955335 3725939371524737807933003)
              ·
                refine ⟨5588909057287106711899505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725939371524737807933003 5588909057287106711899505)
                ·
                  refine ⟨4191681792965330033924629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5588909057287106711899505 4191681792965330033924629)
                  ·
                    refine ⟨196485084045249845340217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4191681792965330033924629 196485084045249845340217)
                    ·
                      refine ⟨147363813033937384005163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196485084045249845340217 147363813033937384005163)
                      ·
                        rfl

theorem cell23_286990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_286990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_286990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_286990 prefixEnd_286990 := by exact prefixLift 286990
  have htrace : WordTrace (prefixWord ++ tailWord_286990) baseStart_286990 baseEnd_286990 := by
    simpa [prefixWord, tailWord_286990, baseEnd_286990] using wordTrace_append hprefix tailTrace_286990
  have hstable : (prefixWord ++ tailWord_286990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286990).length < 2 ^ (prefixWord ++ tailWord_286990).sum := by decide
  have hdescent : baseEnd_286990 < baseStart_286990 := by decide
  rcases family_descends (prefixWord ++ tailWord_286990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287003 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4]
def baseStart_287003 : Nat := 118140960795 + 287003 * 2 ^ 59
def prefixEnd_287003 : Nat := 4983230072969 + 3 ^ 40 * 287003 * 2
def baseEnd_287003 : Nat := 147370488282445833142603

theorem tailTrace_287003 : CollatzResearch.WordTrace tailWord_287003 prefixEnd_287003 147370488282445833142603 := by
  unfold tailWord_287003
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467859379244622055129663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6978572919496414703419775 10467859379244622055129663)
  ·
    refine ⟨15701789068866933082694495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10467859379244622055129663 15701789068866933082694495)
    ·
      refine ⟨23552683603300399624041743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15701789068866933082694495 23552683603300399624041743)
      ·
        refine ⟨35329025404950599436062615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23552683603300399624041743 35329025404950599436062615)
        ·
          refine ⟨52993538107425899154093923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35329025404950599436062615 52993538107425899154093923)
          ·
            refine ⟨79490307161138848731140885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52993538107425899154093923 79490307161138848731140885)
            ·
              refine ⟨3726108148178383534272229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79490307161138848731140885 3726108148178383534272229)
              ·
                refine ⟨698645277783446912676043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3726108148178383534272229 698645277783446912676043)
                ·
                  refine ⟨1047967916675170369014065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698645277783446912676043 1047967916675170369014065)
                  ·
                    refine ⟨785975937506377776760549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1047967916675170369014065 785975937506377776760549)
                    ·
                      refine ⟨147370488282445833142603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 785975937506377776760549 147370488282445833142603)
                      ·
                        rfl

theorem cell23_287003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].length) (baseStart_287003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287003 prefixEnd_287003 := by exact prefixLift 287003
  have htrace : WordTrace (prefixWord ++ tailWord_287003) baseStart_287003 baseEnd_287003 := by
    simpa [prefixWord, tailWord_287003, baseEnd_287003] using wordTrace_append hprefix tailTrace_287003
  have hstable : (prefixWord ++ tailWord_287003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287003).length < 2 ^ (prefixWord ++ tailWord_287003).sum := by decide
  have hdescent : baseEnd_287003 < baseStart_287003 := by decide
  rcases family_descends (prefixWord ++ tailWord_287003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287010 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_287010 : Nat := 118140960795 + 287010 * 2 ^ 59
def prefixEnd_287010 : Nat := 4983230072969 + 3 ^ 40 * 287010 * 2
def baseEnd_287010 : Nat := 147374082647027305755071

theorem tailTrace_287010 : CollatzResearch.WordTrace tailWord_287010 prefixEnd_287010 147374082647027305755071 := by
  unfold tailWord_287010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617028672554815562658621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6978743126812841500422989 2617028672554815562658621)
  ·
    refine ⟨981385752208055835996983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2617028672554815562658621 981385752208055835996983)
    ·
      refine ⟨1472078628312083753995475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981385752208055835996983 1472078628312083753995475)
      ·
        refine ⟨2208117942468125630993213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472078628312083753995475 2208117942468125630993213)
        ·
          refine ⟨828044228425547111622455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2208117942468125630993213 828044228425547111622455)
          ·
            refine ⟨1242066342638320667433683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828044228425547111622455 1242066342638320667433683)
            ·
              refine ⟨1863099513957481001150525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242066342638320667433683 1863099513957481001150525)
              ·
                refine ⟨698662317734055375431447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1863099513957481001150525 698662317734055375431447)
                ·
                  refine ⟨1047993476601083063147171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698662317734055375431447 1047993476601083063147171)
                  ·
                    refine ⟨1571990214901624594720757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1047993476601083063147171 1571990214901624594720757)
                    ·
                      refine ⟨147374082647027305755071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1571990214901624594720757 147374082647027305755071)
                      ·
                        rfl

theorem cell23_287010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_287010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287010 prefixEnd_287010 := by exact prefixLift 287010
  have htrace : WordTrace (prefixWord ++ tailWord_287010) baseStart_287010 baseEnd_287010 := by
    simpa [prefixWord, tailWord_287010, baseEnd_287010] using wordTrace_append hprefix tailTrace_287010
  have hstable : (prefixWord ++ tailWord_287010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287010).length < 2 ^ (prefixWord ++ tailWord_287010).sum := by decide
  have hdescent : baseEnd_287010 < baseStart_287010 := by decide
  rcases family_descends (prefixWord ++ tailWord_287010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287018 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_287018 : Nat := 118140960795 + 287018 * 2 ^ 59
def prefixEnd_287018 : Nat := 4983230072969 + 3 ^ 40 * 287018 * 2
def baseEnd_287018 : Nat := 147378190492263274455035

theorem tailTrace_287018 : CollatzResearch.WordTrace tailWord_287018 prefixEnd_287018 147378190492263274455035 := by
  unfold tailWord_287018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617101618547569904231427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6978937649460186411283805 2617101618547569904231427)
  ·
    refine ⟨3925652427821354856347141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2617101618547569904231427 3925652427821354856347141)
    ·
      refine ⟨736059830216504035565089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3925652427821354856347141 736059830216504035565089)
      ·
        refine ⟨552044872662378026673817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 736059830216504035565089 552044872662378026673817)
        ·
          refine ⟨414033654496783520005363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552044872662378026673817 414033654496783520005363)
          ·
            refine ⟨621050481745175280008045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414033654496783520005363 621050481745175280008045)
            ·
              refine ⟨232893930654440730003017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 621050481745175280008045 232893930654440730003017)
              ·
                refine ⟨174670447990830547502263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232893930654440730003017 174670447990830547502263)
                ·
                  refine ⟨262005671986245821253395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174670447990830547502263 262005671986245821253395)
                  ·
                    refine ⟨393008507979368731880093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262005671986245821253395 393008507979368731880093)
                    ·
                      refine ⟨147378190492263274455035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393008507979368731880093 147378190492263274455035)
                      ·
                        rfl

theorem cell23_287018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_287018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287018 prefixEnd_287018 := by exact prefixLift 287018
  have htrace : WordTrace (prefixWord ++ tailWord_287018) baseStart_287018 baseEnd_287018 := by
    simpa [prefixWord, tailWord_287018, baseEnd_287018] using wordTrace_append hprefix tailTrace_287018
  have hstable : (prefixWord ++ tailWord_287018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287018).length < 2 ^ (prefixWord ++ tailWord_287018).sum := by decide
  have hdescent : baseEnd_287018 < baseStart_287018 := by decide
  rcases family_descends (prefixWord ++ tailWord_287018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287034 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_287034 : Nat := 118140960795 + 287034 * 2 ^ 59
def prefixEnd_287034 : Nat := 4983230072969 + 3 ^ 40 * 287034 * 2
def baseEnd_287034 : Nat := 49128802060911737284987

theorem tailTrace_287034 : CollatzResearch.WordTrace tailWord_287034 prefixEnd_287034 49128802060911737284987 := by
  unfold tailWord_287034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617247510533078587377039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6979326694754876233005437 2617247510533078587377039)
  ·
    refine ⟨3925871265799617881065559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2617247510533078587377039 3925871265799617881065559)
    ·
      refine ⟨5888806898699426821598339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3925871265799617881065559 5888806898699426821598339)
      ·
        refine ⟨8833210348049140232397509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888806898699426821598339 8833210348049140232397509)
        ·
          refine ⟨1656226940259213793574533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8833210348049140232397509 1656226940259213793574533)
          ·
            refine ⟨310542551298602586295225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1656226940259213793574533 310542551298602586295225)
            ·
              refine ⟨232906913473951939721419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310542551298602586295225 232906913473951939721419)
              ·
                refine ⟨349360370210927909582129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232906913473951939721419 349360370210927909582129)
                ·
                  refine ⟨262020277658195932186597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349360370210927909582129 262020277658195932186597)
                  ·
                    refine ⟨49128802060911737284987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262020277658195932186597 49128802060911737284987)
                    ·
                      rfl

theorem cell23_287034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_287034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287034 prefixEnd_287034 := by exact prefixLift 287034
  have htrace : WordTrace (prefixWord ++ tailWord_287034) baseStart_287034 baseEnd_287034 := by
    simpa [prefixWord, tailWord_287034, baseEnd_287034] using wordTrace_append hprefix tailTrace_287034
  have hstable : (prefixWord ++ tailWord_287034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287034).length < 2 ^ (prefixWord ++ tailWord_287034).sum := by decide
  have hdescent : baseEnd_287034 < baseStart_287034 := by decide
  rcases family_descends (prefixWord ++ tailWord_287034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287040 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 6, 1, 3]
def baseStart_287040 : Nat := 118140960795 + 287040 * 2 ^ 59
def prefixEnd_287040 : Nat := 4983230072969 + 3 ^ 40 * 287040 * 2
def baseEnd_287040 : Nat := 147389487066662188379933

theorem tailTrace_287040 : CollatzResearch.WordTrace tailWord_287040 prefixEnd_287040 147389487066662188379933 := by
  unfold tailWord_287040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234604440055288687113287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6979472586740384916151049 5234604440055288687113287)
  ·
    refine ⟨7851906660082933030669931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5234604440055288687113287 7851906660082933030669931)
    ·
      refine ⟨11777859990124399546004897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7851906660082933030669931 11777859990124399546004897)
      ·
        refine ⟨8833394992593299659503673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11777859990124399546004897 8833394992593299659503673)
        ·
          refine ⟨6625046244444974744627755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8833394992593299659503673 6625046244444974744627755)
          ·
            refine ⟨9937569366667462116941633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6625046244444974744627755 9937569366667462116941633)
            ·
              refine ⟨7453177025000596587706225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9937569366667462116941633 7453177025000596587706225)
              ·
                refine ⟨5589882768750447440779669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7453177025000596587706225 5589882768750447440779669)
                ·
                  refine ⟨262025754785177223786547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5589882768750447440779669 262025754785177223786547)
                  ·
                    refine ⟨393038632177765835679821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262025754785177223786547 393038632177765835679821)
                    ·
                      refine ⟨147389487066662188379933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393038632177765835679821 147389487066662188379933)
                      ·
                        rfl

theorem cell23_287040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_287040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287040 prefixEnd_287040 := by exact prefixLift 287040
  have htrace : WordTrace (prefixWord ++ tailWord_287040) baseStart_287040 baseEnd_287040 := by
    simpa [prefixWord, tailWord_287040, baseEnd_287040] using wordTrace_append hprefix tailTrace_287040
  have hstable : (prefixWord ++ tailWord_287040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287040).length < 2 ^ (prefixWord ++ tailWord_287040).sum := by decide
  have hdescent : baseEnd_287040 < baseStart_287040 := by decide
  rcases family_descends (prefixWord ++ tailWord_287040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287041 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_287041 : Nat := 118140960795 + 287041 * 2 ^ 59
def prefixEnd_287041 : Nat := 4983230072969 + 3 ^ 40 * 287041 * 2
def baseEnd_287041 : Nat := 147390000547316684467429

theorem tailTrace_287041 : CollatzResearch.WordTrace tailWord_287041 prefixEnd_287041 147390000547316684467429 := by
  unfold tailWord_287041
  simp only [CollatzResearch.WordTrace]
  refine ⟨10469245353106954545012977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6979496902071303030008651 10469245353106954545012977)
  ·
    refine ⟨7851934014830215908759733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10469245353106954545012977 7851934014830215908759733)
    ·
      refine ⟨736118813890332741446225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7851934014830215908759733 736118813890332741446225)
      ·
        refine ⟨552089110417749556084669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 736118813890332741446225 552089110417749556084669)
        ·
          refine ⟨207033416406656083531751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552089110417749556084669 207033416406656083531751)
          ·
            refine ⟨310550124609984125297627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207033416406656083531751 310550124609984125297627)
            ·
              refine ⟨465825186914976187946441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310550124609984125297627 465825186914976187946441)
              ·
                refine ⟨349368890186232140959831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465825186914976187946441 349368890186232140959831)
                ·
                  refine ⟨524053335279348211439747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349368890186232140959831 524053335279348211439747)
                  ·
                    refine ⟨786080002919022317159621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 524053335279348211439747 786080002919022317159621)
                    ·
                      refine ⟨147390000547316684467429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 786080002919022317159621 147390000547316684467429)
                      ·
                        rfl

theorem cell23_287041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_287041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287041 prefixEnd_287041 := by exact prefixLift 287041
  have htrace : WordTrace (prefixWord ++ tailWord_287041) baseStart_287041 baseEnd_287041 := by
    simpa [prefixWord, tailWord_287041, baseEnd_287041] using wordTrace_append hprefix tailTrace_287041
  have hstable : (prefixWord ++ tailWord_287041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287041).length < 2 ^ (prefixWord ++ tailWord_287041).sum := by decide
  have hdescent : baseEnd_287041 < baseStart_287041 := by decide
  rcases family_descends (prefixWord ++ tailWord_287041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287044 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_287044 : Nat := 118140960795 + 287044 * 2 ^ 59
def prefixEnd_287044 : Nat := 4983230072969 + 3 ^ 40 * 287044 * 2
def baseEnd_287044 : Nat := 147391540989280172729915

theorem tailTrace_287044 : CollatzResearch.WordTrace tailWord_287044 prefixEnd_287044 147391540989280172729915 := by
  unfold tailWord_287044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234677386048043028686093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6979569848064057371581457 5234677386048043028686093)
  ·
    refine ⟨1963004019768016135757285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5234677386048043028686093 1963004019768016135757285)
    ·
      refine ⟨368063253706503025454491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1963004019768016135757285 368063253706503025454491)
      ·
        refine ⟨552094880559754538181737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368063253706503025454491 552094880559754538181737)
        ·
          refine ⟨414071160419815903636303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552094880559754538181737 414071160419815903636303)
          ·
            refine ⟨621106740629723855454455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414071160419815903636303 621106740629723855454455)
            ·
              refine ⟨931660110944585783181683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621106740629723855454455 931660110944585783181683)
              ·
                refine ⟨1397490166416878674772525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931660110944585783181683 1397490166416878674772525)
                ·
                  refine ⟨524058812406329503039697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1397490166416878674772525 524058812406329503039697)
                  ·
                    refine ⟨393044109304747127279773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 524058812406329503039697 393044109304747127279773)
                    ·
                      refine ⟨147391540989280172729915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393044109304747127279773 147391540989280172729915)
                      ·
                        rfl

theorem cell23_287044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_287044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287044 prefixEnd_287044 := by exact prefixLift 287044
  have htrace : WordTrace (prefixWord ++ tailWord_287044) baseStart_287044 baseEnd_287044 := by
    simpa [prefixWord, tailWord_287044, baseEnd_287044] using wordTrace_append hprefix tailTrace_287044
  have hstable : (prefixWord ++ tailWord_287044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287044).length < 2 ^ (prefixWord ++ tailWord_287044).sum := by decide
  have hdescent : baseEnd_287044 < baseStart_287044 := by decide
  rcases family_descends (prefixWord ++ tailWord_287044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287074 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_287074 : Nat := 118140960795 + 287074 * 2 ^ 59
def prefixEnd_287074 : Nat := 4983230072969 + 3 ^ 40 * 287074 * 2
def baseEnd_287074 : Nat := 147406945408915055354777

theorem tailTrace_287074 : CollatzResearch.WordTrace tailWord_287074 prefixEnd_287074 147406945408915055354777 := by
  unfold tailWord_287074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617612240496850295241069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6980299307991600787309517 2617612240496850295241069)
  ·
    refine ⟨981604590186318860715401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2617612240496850295241069 981604590186318860715401)
    ·
      refine ⟨736203442639739145536551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981604590186318860715401 736203442639739145536551)
      ·
        refine ⟨1104305163959608718304827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736203442639739145536551 1104305163959608718304827)
        ·
          refine ⟨1656457745939413077457241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104305163959608718304827 1656457745939413077457241)
          ·
            refine ⟨1242343309454559808092931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1656457745939413077457241 1242343309454559808092931)
            ·
              refine ⟨1863514964181839712139397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242343309454559808092931 1863514964181839712139397)
              ·
                refine ⟨349409055784094946026137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1863514964181839712139397 349409055784094946026137)
                ·
                  refine ⟨262056791838071209519603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349409055784094946026137 262056791838071209519603)
                  ·
                    refine ⟨393085187757106814279405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262056791838071209519603 393085187757106814279405)
                    ·
                      refine ⟨147406945408915055354777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393085187757106814279405 147406945408915055354777)
                      ·
                        rfl

theorem cell23_287074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_287074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287074 prefixEnd_287074 := by exact prefixLift 287074
  have htrace : WordTrace (prefixWord ++ tailWord_287074) baseStart_287074 baseEnd_287074 := by
    simpa [prefixWord, tailWord_287074, baseEnd_287074] using wordTrace_append hprefix tailTrace_287074
  have hstable : (prefixWord ++ tailWord_287074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287074).length < 2 ^ (prefixWord ++ tailWord_287074).sum := by decide
  have hdescent : baseEnd_287074 < baseStart_287074 := by decide
  rcases family_descends (prefixWord ++ tailWord_287074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287080 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_287080 : Nat := 118140960795 + 287080 * 2 ^ 59
def prefixEnd_287080 : Nat := 4983230072969 + 3 ^ 40 * 287080 * 2
def baseEnd_287080 : Nat := 147410026292842031879749

theorem tailTrace_287080 : CollatzResearch.WordTrace tailWord_287080 prefixEnd_287080 147410026292842031879749 := by
  unfold tailWord_287080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235333899982832102841347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6980445199977109470455129 5235333899982832102841347)
  ·
    refine ⟨7853000849974248154262021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5235333899982832102841347 7853000849974248154262021)
    ·
      refine ⟨1472437659370171528924129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7853000849974248154262021 1472437659370171528924129)
      ·
        refine ⟨1104328244527628646693097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1472437659370171528924129 1104328244527628646693097)
        ·
          refine ⟨828246183395721485019823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104328244527628646693097 828246183395721485019823)
          ·
            refine ⟨1242369275093582227529735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828246183395721485019823 1242369275093582227529735)
            ·
              refine ⟨1863553912640373341294603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242369275093582227529735 1863553912640373341294603)
              ·
                refine ⟨2795330868960560011941905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863553912640373341294603 2795330868960560011941905)
                ·
                  refine ⟨2096498151720420008956429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795330868960560011941905 2096498151720420008956429)
                  ·
                    refine ⟨786186806895157503358661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096498151720420008956429 786186806895157503358661)
                    ·
                      refine ⟨147410026292842031879749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 786186806895157503358661 147410026292842031879749)
                      ·
                        rfl

theorem cell23_287080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_287080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287080 prefixEnd_287080 := by exact prefixLift 287080
  have htrace : WordTrace (prefixWord ++ tailWord_287080) baseStart_287080 baseEnd_287080 := by
    simpa [prefixWord, tailWord_287080, baseEnd_287080] using wordTrace_append hprefix tailTrace_287080
  have hstable : (prefixWord ++ tailWord_287080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287080).length < 2 ^ (prefixWord ++ tailWord_287080).sum := by decide
  have hdescent : baseEnd_287080 < baseStart_287080 := by decide
  rcases family_descends (prefixWord ++ tailWord_287080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287090 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_287090 : Nat := 118140960795 + 287090 * 2 ^ 59
def prefixEnd_287090 : Nat := 4983230072969 + 3 ^ 40 * 287090 * 2
def baseEnd_287090 : Nat := 49138387033128997584901

theorem tailTrace_287090 : CollatzResearch.WordTrace tailWord_287090 prefixEnd_287090 49138387033128997584901 := by
  unfold tailWord_287090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617758132482358978386681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6980688353286290609031149 2617758132482358978386681)
  ·
    refine ⟨1963318599361769233790011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2617758132482358978386681 1963318599361769233790011)
    ·
      refine ⟨2944977899042653850685017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963318599361769233790011 2944977899042653850685017)
      ·
        refine ⟨2208733424281990388013763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2944977899042653850685017 2208733424281990388013763)
        ·
          refine ⟨3313100136422985582020645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208733424281990388013763 3313100136422985582020645)
          ·
            refine ⟨621206275579309796628871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3313100136422985582020645 621206275579309796628871)
            ·
              refine ⟨931809413368964694943307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621206275579309796628871 931809413368964694943307)
              ·
                refine ⟨1397714120053447042414961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931809413368964694943307 1397714120053447042414961)
                ·
                  refine ⟨1048285590040085281811221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1397714120053447042414961 1048285590040085281811221)
                  ·
                    refine ⟨49138387033128997584901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1048285590040085281811221 49138387033128997584901)
                    ·
                      rfl

theorem cell23_287090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_287090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287090 prefixEnd_287090 := by exact prefixLift 287090
  have htrace : WordTrace (prefixWord ++ tailWord_287090) baseStart_287090 baseEnd_287090 := by
    simpa [prefixWord, tailWord_287090, baseEnd_287090] using wordTrace_append hprefix tailTrace_287090
  have hstable : (prefixWord ++ tailWord_287090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287090).length < 2 ^ (prefixWord ++ tailWord_287090).sum := by decide
  have hdescent : baseEnd_287090 < baseStart_287090 := by decide
  rcases family_descends (prefixWord ++ tailWord_287090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287097 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 6, 2, 2]
def baseStart_287097 : Nat := 118140960795 + 287097 * 2 ^ 59
def prefixEnd_287097 : Nat := 4983230072969 + 3 ^ 40 * 287097 * 2
def baseEnd_287097 : Nat := 147418755463968465367171

theorem tailTrace_287097 : CollatzResearch.WordTrace tailWord_287097 prefixEnd_287097 147418755463968465367171 := by
  unfold tailWord_287097
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471287840904076109051545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6980858560602717406034363 10471287840904076109051545)
  ·
    refine ⟨7853465880678057081788659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10471287840904076109051545 7853465880678057081788659)
    ·
      refine ⟨11780198821017085622682989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7853465880678057081788659 11780198821017085622682989)
      ·
        refine ⟨4417574557881407108506121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11780198821017085622682989 4417574557881407108506121)
        ·
          refine ⟨3313180918411055331379591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4417574557881407108506121 3313180918411055331379591)
          ·
            refine ⟨4969771377616582997069387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313180918411055331379591 4969771377616582997069387)
            ·
              refine ⟨7454657066424874495604081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969771377616582997069387 7454657066424874495604081)
              ·
                refine ⟨5590992799818655871703061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7454657066424874495604081 5590992799818655871703061)
                ·
                  refine ⟨262077787491499493986081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5590992799818655871703061 262077787491499493986081)
                  ·
                    refine ⟨196558340618624620489561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262077787491499493986081 196558340618624620489561)
                    ·
                      refine ⟨147418755463968465367171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196558340618624620489561 147418755463968465367171)
                      ·
                        rfl

theorem cell23_287097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_287097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287097 prefixEnd_287097 := by exact prefixLift 287097
  have htrace : WordTrace (prefixWord ++ tailWord_287097) baseStart_287097 baseEnd_287097 := by
    simpa [prefixWord, tailWord_287097, baseEnd_287097] using wordTrace_append hprefix tailTrace_287097
  have hstable : (prefixWord ++ tailWord_287097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287097).length < 2 ^ (prefixWord ++ tailWord_287097).sum := by decide
  have hdescent : baseEnd_287097 < baseStart_287097 := by decide
  rcases family_descends (prefixWord ++ tailWord_287097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287103 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 7]
def baseStart_287103 : Nat := 118140960795 + 287103 * 2 ^ 59
def prefixEnd_287103 : Nat := 4983230072969 + 3 ^ 40 * 287103 * 2
def baseEnd_287103 : Nat := 16380204038655049099127

theorem tailTrace_287103 : CollatzResearch.WordTrace tailWord_287103 prefixEnd_287103 16380204038655049099127 := by
  unfold tailWord_287103
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471506678882339133769963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6981004452588226089179975 10471506678882339133769963)
  ·
    refine ⟨15707260018323508700654945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10471506678882339133769963 15707260018323508700654945)
    ·
      refine ⟨11780445013742631525491209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15707260018323508700654945 11780445013742631525491209)
      ·
        refine ⟨8835333760306973644118407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11780445013742631525491209 8835333760306973644118407)
        ·
          refine ⟨13253000640460460466177611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8835333760306973644118407 13253000640460460466177611)
          ·
            refine ⟨19879500960690690699266417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13253000640460460466177611 19879500960690690699266417)
            ·
              refine ⟨14909625720518018024449813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19879500960690690699266417 14909625720518018024449813)
              ·
                refine ⟨698888705649282094896085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14909625720518018024449813 698888705649282094896085)
                ·
                  refine ⟨16380204038655049099127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 698888705649282094896085 16380204038655049099127)
                  ·
                    rfl

theorem cell23_287103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 7].length) (baseStart_287103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287103 prefixEnd_287103 := by exact prefixLift 287103
  have htrace : WordTrace (prefixWord ++ tailWord_287103) baseStart_287103 baseEnd_287103 := by
    simpa [prefixWord, tailWord_287103, baseEnd_287103] using wordTrace_append hprefix tailTrace_287103
  have hstable : (prefixWord ++ tailWord_287103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287103).length < 2 ^ (prefixWord ++ tailWord_287103).sum := by decide
  have hdescent : baseEnd_287103 < baseStart_287103 := by decide
  rcases family_descends (prefixWord ++ tailWord_287103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287118 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_287118 : Nat := 118140960795 + 287118 * 2 ^ 59
def prefixEnd_287118 : Nat := 4983230072969 + 3 ^ 40 * 287118 * 2
def baseEnd_287118 : Nat := 147429538557712883204575

theorem tailTrace_287118 : CollatzResearch.WordTrace tailWord_287118 prefixEnd_287118 147429538557712883204575 := by
  unfold tailWord_287118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309006721728499586945751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6981369182551997797044005 1309006721728499586945751)
  ·
    refine ⟨1963510082592749380418627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1309006721728499586945751 1963510082592749380418627)
    ·
      refine ⟨2945265123889124070627941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963510082592749380418627 2945265123889124070627941)
      ·
        refine ⟨552237210729210763242739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2945265123889124070627941 552237210729210763242739)
        ·
          refine ⟨828355816093816144864109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552237210729210763242739 828355816093816144864109)
          ·
            refine ⟨310633431035181054324041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 828355816093816144864109 310633431035181054324041)
            ·
              refine ⟨232975073276385790743031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310633431035181054324041 232975073276385790743031)
              ·
                refine ⟨349462609914578686114547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232975073276385790743031 349462609914578686114547)
                ·
                  refine ⟨524193914871868029171821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349462609914578686114547 524193914871868029171821)
                  ·
                    refine ⟨196572718076950510939433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524193914871868029171821 196572718076950510939433)
                    ·
                      refine ⟨147429538557712883204575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196572718076950510939433 147429538557712883204575)
                      ·
                        rfl

theorem cell23_287118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_287118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287118 prefixEnd_287118 := by exact prefixLift 287118
  have htrace : WordTrace (prefixWord ++ tailWord_287118) baseStart_287118 baseEnd_287118 := by
    simpa [prefixWord, tailWord_287118, baseEnd_287118] using wordTrace_append hprefix tailTrace_287118
  have hstable : (prefixWord ++ tailWord_287118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287118).length < 2 ^ (prefixWord ++ tailWord_287118).sum := by decide
  have hdescent : baseEnd_287118 < baseStart_287118 := by decide
  rcases family_descends (prefixWord ++ tailWord_287118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287207 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_287207 : Nat := 118140960795 + 287207 * 2 ^ 59
def prefixEnd_287207 : Nat := 4983230072969 + 3 ^ 40 * 287207 * 2
def baseEnd_287207 : Nat := 147475238335963034991665

theorem tailTrace_287207 : CollatzResearch.WordTrace tailWord_287207 prefixEnd_287207 147475238335963034991665 := by
  unfold tailWord_287207
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475299870505564895555875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6983533247003709930370583 10475299870505564895555875)
  ·
    refine ⟨15712949805758347343333813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10475299870505564895555875 15712949805758347343333813)
    ·
      refine ⟨1473089044289845063437545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15712949805758347343333813 1473089044289845063437545)
      ·
        refine ⟨1104816783217383797578159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1473089044289845063437545 1104816783217383797578159)
        ·
          refine ⟨1657225174826075696367239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104816783217383797578159 1657225174826075696367239)
          ·
            refine ⟨2485837762239113544550859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657225174826075696367239 2485837762239113544550859)
            ·
              refine ⟨3728756643358670316826289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485837762239113544550859 3728756643358670316826289)
              ·
                refine ⟨2796567482519002737619717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728756643358670316826289 2796567482519002737619717)
                ·
                  refine ⟨524356402972313013303697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2796567482519002737619717 524356402972313013303697)
                  ·
                    refine ⟨393267302229234759977773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 524356402972313013303697 393267302229234759977773)
                    ·
                      refine ⟨147475238335963034991665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393267302229234759977773 147475238335963034991665)
                      ·
                        rfl

theorem cell23_287207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_287207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287207 prefixEnd_287207 := by exact prefixLift 287207
  have htrace : WordTrace (prefixWord ++ tailWord_287207) baseStart_287207 baseEnd_287207 := by
    simpa [prefixWord, tailWord_287207, baseEnd_287207] using wordTrace_append hprefix tailTrace_287207
  have hstable : (prefixWord ++ tailWord_287207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287207).length < 2 ^ (prefixWord ++ tailWord_287207).sum := by decide
  have hdescent : baseEnd_287207 < baseStart_287207 := by decide
  rcases family_descends (prefixWord ++ tailWord_287207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287221 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_287221 : Nat := 118140960795 + 287221 * 2 ^ 59
def prefixEnd_287221 : Nat := 4983230072969 + 3 ^ 40 * 287221 * 2
def baseEnd_287221 : Nat := 147482427065125980216601

theorem tailTrace_287221 : CollatzResearch.WordTrace tailWord_287221 prefixEnd_287221 147482427065125980216601 := by
  unfold tailWord_287221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475810492454845286565517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6983873661636563524377011 10475810492454845286565517)
  ·
    refine ⟨3928428934670566982462069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10475810492454845286565517 3928428934670566982462069)
    ·
      refine ⟨368290212625365654605819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3928428934670566982462069 368290212625365654605819)
      ·
        refine ⟨552435318938048481908729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368290212625365654605819 552435318938048481908729)
        ·
          refine ⟨414326489203536361431547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552435318938048481908729 414326489203536361431547)
          ·
            refine ⟨621489733805304542147321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414326489203536361431547 621489733805304542147321)
            ·
              refine ⟨466117300353978406610491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621489733805304542147321 466117300353978406610491)
              ·
                refine ⟨699175950530967609915737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466117300353978406610491 699175950530967609915737)
                ·
                  refine ⟨524381962898225707436803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699175950530967609915737 524381962898225707436803)
                  ·
                    refine ⟨786572944347338561155205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 524381962898225707436803 786572944347338561155205)
                    ·
                      refine ⟨147482427065125980216601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 786572944347338561155205 147482427065125980216601)
                      ·
                        rfl

theorem cell23_287221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_287221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287221 prefixEnd_287221 := by exact prefixLift 287221
  have htrace : WordTrace (prefixWord ++ tailWord_287221) baseStart_287221 baseEnd_287221 := by
    simpa [prefixWord, tailWord_287221, baseEnd_287221] using wordTrace_append hprefix tailTrace_287221
  have hstable : (prefixWord ++ tailWord_287221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287221).length < 2 ^ (prefixWord ++ tailWord_287221).sum := by decide
  have hdescent : baseEnd_287221 < baseStart_287221 := by decide
  rcases family_descends (prefixWord ++ tailWord_287221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287238 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_287238 : Nat := 118140960795 + 287238 * 2 ^ 59
def prefixEnd_287238 : Nat := 4983230072969 + 3 ^ 40 * 287238 * 2
def baseEnd_287238 : Nat := 147491156236252413704023

theorem tailTrace_287238 : CollatzResearch.WordTrace tailWord_287238 prefixEnd_287238 147491156236252413704023 := by
  unfold tailWord_287238
  simp only [CollatzResearch.WordTrace]
  refine ⟨327388454168539287185449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6984287022262171459956245 327388454168539287185449)
  ·
    refine ⟨245541340626404465389087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 327388454168539287185449 245541340626404465389087)
    ·
      refine ⟨368312010939606698083631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245541340626404465389087 368312010939606698083631)
      ·
        refine ⟨552468016409410047125447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368312010939606698083631 552468016409410047125447)
        ·
          refine ⟨828702024614115070688171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552468016409410047125447 828702024614115070688171)
          ·
            refine ⟨1243053036921172606032257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828702024614115070688171 1243053036921172606032257)
            ·
              refine ⟨932289777690879454524193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243053036921172606032257 932289777690879454524193)
              ·
                refine ⟨699217333268159590893145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932289777690879454524193 699217333268159590893145)
                ·
                  refine ⟨524412999951119693169859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699217333268159590893145 524412999951119693169859)
                  ·
                    refine ⟨786619499926679539754789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 524412999951119693169859 786619499926679539754789)
                    ·
                      refine ⟨147491156236252413704023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 786619499926679539754789 147491156236252413704023)
                      ·
                        rfl

theorem cell23_287238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_287238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287238 prefixEnd_287238 := by exact prefixLift 287238
  have htrace : WordTrace (prefixWord ++ tailWord_287238) baseStart_287238 baseEnd_287238 := by
    simpa [prefixWord, tailWord_287238, baseEnd_287238] using wordTrace_append hprefix tailTrace_287238
  have hstable : (prefixWord ++ tailWord_287238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287238).length < 2 ^ (prefixWord ++ tailWord_287238).sum := by decide
  have hdescent : baseEnd_287238 < baseStart_287238 := by decide
  rcases family_descends (prefixWord ++ tailWord_287238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287287 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 4, 4]
def baseStart_287287 : Nat := 118140960795 + 287287 * 2 ^ 59
def prefixEnd_287287 : Nat := 4983230072969 + 3 ^ 40 * 287287 * 2
def baseEnd_287287 : Nat := 49172105596107573997099

theorem tailTrace_287287 : CollatzResearch.WordTrace tailWord_287287 prefixEnd_287287 49172105596107573997099 := by
  unfold tailWord_287287
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478217710215738558468115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6985478473477159038978743 10478217710215738558468115)
  ·
    refine ⟨15717326565323607837702173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10478217710215738558468115 15717326565323607837702173)
    ·
      refine ⟨5893997461996352939138315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15717326565323607837702173 5893997461996352939138315)
      ·
        refine ⟨8840996192994529408707473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893997461996352939138315 8840996192994529408707473)
        ·
          refine ⟨6630747144745897056530605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8840996192994529408707473 6630747144745897056530605)
          ·
            refine ⟨2486530179279711396198977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6630747144745897056530605 2486530179279711396198977)
            ·
              refine ⟨1864897634459783547149233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486530179279711396198977 1864897634459783547149233)
              ·
                refine ⟨1398673225844837660361925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864897634459783547149233 1398673225844837660361925)
                ·
                  refine ⟨262251229845907061317861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398673225844837660361925 262251229845907061317861)
                  ·
                    refine ⟨49172105596107573997099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262251229845907061317861 49172105596107573997099)
                    ·
                      rfl

theorem cell23_287287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_287287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287287 prefixEnd_287287 := by exact prefixLift 287287
  have htrace : WordTrace (prefixWord ++ tailWord_287287) baseStart_287287 baseEnd_287287 := by
    simpa [prefixWord, tailWord_287287, baseEnd_287287] using wordTrace_append hprefix tailTrace_287287
  have hstable : (prefixWord ++ tailWord_287287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287287).length < 2 ^ (prefixWord ++ tailWord_287287).sum := by decide
  have hdescent : baseEnd_287287 < baseStart_287287 := by decide
  rcases family_descends (prefixWord ++ tailWord_287287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287324 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_287324 : Nat := 118140960795 + 287324 * 2 ^ 59
def prefixEnd_287324 : Nat := 4983230072969 + 3 ^ 40 * 287324 * 2
def baseEnd_287324 : Nat := 147535315572539077228627

theorem tailTrace_287324 : CollatzResearch.WordTrace tailWord_287324 prefixEnd_287324 147535315572539077228627 := by
  unfold tailWord_287324
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239783605540846938782513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6986378140721129251710017 5239783605540846938782513)
  ·
    refine ⟨3929837704155635204086885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5239783605540846938782513 3929837704155635204086885)
    ·
      refine ⟨736844569529181600766291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3929837704155635204086885 736844569529181600766291)
      ·
        refine ⟨1105266854293772401149437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736844569529181600766291 1105266854293772401149437)
        ·
          refine ⟨414475070360164650431039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1105266854293772401149437 414475070360164650431039)
          ·
            refine ⟨621712605540246975646559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414475070360164650431039 621712605540246975646559)
            ·
              refine ⟨932568908310370463469839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621712605540246975646559 932568908310370463469839)
              ·
                refine ⟨1398853362465555695204759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932568908310370463469839 1398853362465555695204759)
                ·
                  refine ⟨2098280043698333542807139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398853362465555695204759 2098280043698333542807139)
                  ·
                    refine ⟨3147420065547500314210709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098280043698333542807139 3147420065547500314210709)
                    ·
                      refine ⟨147535315572539077228627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3147420065547500314210709 147535315572539077228627)
                      ·
                        rfl

theorem cell23_287324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_287324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287324 prefixEnd_287324 := by exact prefixLift 287324
  have htrace : WordTrace (prefixWord ++ tailWord_287324) baseStart_287324 baseEnd_287324 := by
    simpa [prefixWord, tailWord_287324, baseEnd_287324] using wordTrace_append hprefix tailTrace_287324
  have hstable : (prefixWord ++ tailWord_287324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287324).length < 2 ^ (prefixWord ++ tailWord_287324).sum := by decide
  have hdescent : baseEnd_287324 < baseStart_287324 := by decide
  rcases family_descends (prefixWord ++ tailWord_287324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287361 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_287361 : Nat := 118140960795 + 287361 * 2 ^ 59
def prefixEnd_287361 : Nat := 4983230072969 + 3 ^ 40 * 287361 * 2
def baseEnd_287361 : Nat := 147554314356755432465957

theorem tailTrace_287361 : CollatzResearch.WordTrace tailWord_287361 prefixEnd_287361 147554314356755432465957 := by
  unfold tailWord_287361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10480916711947649196661937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6987277807965099464441291 10480916711947649196661937)
  ·
    refine ⟨7860687533960736897496453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10480916711947649196661937 7860687533960736897496453)
    ·
      refine ⟨1473878912617638168280585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7860687533960736897496453 1473878912617638168280585)
      ·
        refine ⟨1105409184463228626210439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1473878912617638168280585 1105409184463228626210439)
        ·
          refine ⟨1658113776694842939315659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105409184463228626210439 1658113776694842939315659)
          ·
            refine ⟨2487170665042264408973489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658113776694842939315659 2487170665042264408973489)
            ·
              refine ⟨1865377998781698306730117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2487170665042264408973489 1865377998781698306730117)
              ·
                refine ⟨349758374771568432511897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1865377998781698306730117 349758374771568432511897)
                ·
                  refine ⟨262318781078676324383923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349758374771568432511897 262318781078676324383923)
                  ·
                    refine ⟨393478171618014486575885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262318781078676324383923 393478171618014486575885)
                    ·
                      refine ⟨147554314356755432465957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393478171618014486575885 147554314356755432465957)
                      ·
                        rfl

theorem cell23_287361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_287361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287361 prefixEnd_287361 := by exact prefixLift 287361
  have htrace : WordTrace (prefixWord ++ tailWord_287361) baseStart_287361 baseEnd_287361 := by
    simpa [prefixWord, tailWord_287361, baseEnd_287361] using wordTrace_append hprefix tailTrace_287361
  have hstable : (prefixWord ++ tailWord_287361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287361).length < 2 ^ (prefixWord ++ tailWord_287361).sum := by decide
  have hdescent : baseEnd_287361 < baseStart_287361 := by decide
  rcases family_descends (prefixWord ++ tailWord_287361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287367 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_287367 : Nat := 118140960795 + 287367 * 2 ^ 59
def prefixEnd_287367 : Nat := 4983230072969 + 3 ^ 40 * 287367 * 2
def baseEnd_287367 : Nat := 147557395240682408990929

theorem tailTrace_287367 : CollatzResearch.WordTrace tailWord_287367 prefixEnd_287367 147557395240682408990929 := by
  unfold tailWord_287367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10481135549925912221380355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6987423699950608147586903 10481135549925912221380355)
  ·
    refine ⟨15721703324888868332070533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10481135549925912221380355 15721703324888868332070533)
    ·
      refine ⟨2947819373416662812263225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15721703324888868332070533 2947819373416662812263225)
      ·
        refine ⟨2210864530062497109197419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2947819373416662812263225 2210864530062497109197419)
        ·
          refine ⟨3316296795093745663796129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210864530062497109197419 3316296795093745663796129)
          ·
            refine ⟨2487222596320309247847097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3316296795093745663796129 2487222596320309247847097)
            ·
              refine ⟨1865416947240231935885323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2487222596320309247847097 1865416947240231935885323)
              ·
                refine ⟨2798125420860347903827985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865416947240231935885323 2798125420860347903827985)
                ·
                  refine ⟨2098594065645260927870989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798125420860347903827985 2098594065645260927870989)
                  ·
                    refine ⟨786972774616972847951621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098594065645260927870989 786972774616972847951621)
                    ·
                      refine ⟨147557395240682408990929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 786972774616972847951621 147557395240682408990929)
                      ·
                        rfl

theorem cell23_287367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_287367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287367 prefixEnd_287367 := by exact prefixLift 287367
  have htrace : WordTrace (prefixWord ++ tailWord_287367) baseStart_287367 baseEnd_287367 := by
    simpa [prefixWord, tailWord_287367, baseEnd_287367] using wordTrace_append hprefix tailTrace_287367
  have hstable : (prefixWord ++ tailWord_287367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287367).length < 2 ^ (prefixWord ++ tailWord_287367).sum := by decide
  have hdescent : baseEnd_287367 < baseStart_287367 := by decide
  rcases family_descends (prefixWord ++ tailWord_287367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287378 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_287378 : Nat := 118140960795 + 287378 * 2 ^ 59
def prefixEnd_287378 : Nat := 4983230072969 + 3 ^ 40 * 287378 * 2
def baseEnd_287378 : Nat := 147563043527881865953379

theorem tailTrace_287378 : CollatzResearch.WordTrace tailWord_287378 prefixEnd_287378 147563043527881865953379 := by
  unfold tailWord_287378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620384188221515275007697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6987691168590707400020525 2620384188221515275007697)
  ·
    refine ⟨1965288141166136456255773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2620384188221515275007697 1965288141166136456255773)
    ·
      refine ⟨736983052937301171095915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1965288141166136456255773 736983052937301171095915)
      ·
        refine ⟨1105474579405951756643873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736983052937301171095915 1105474579405951756643873)
        ·
          refine ⟨829105934554463817482905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105474579405951756643873 829105934554463817482905)
          ·
            refine ⟨621829450915847863112179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829105934554463817482905 621829450915847863112179)
            ·
              refine ⟨932744176373771794668269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621829450915847863112179 932744176373771794668269)
              ·
                refine ⟨349779066140164423000601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932744176373771794668269 349779066140164423000601)
                ·
                  refine ⟨262334299605123317250451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349779066140164423000601 262334299605123317250451)
                  ·
                    refine ⟨393501449407684975875677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262334299605123317250451 393501449407684975875677)
                    ·
                      refine ⟨147563043527881865953379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393501449407684975875677 147563043527881865953379)
                      ·
                        rfl

theorem cell23_287378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_287378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287378 prefixEnd_287378 := by exact prefixLift 287378
  have htrace : WordTrace (prefixWord ++ tailWord_287378) baseStart_287378 baseEnd_287378 := by
    simpa [prefixWord, tailWord_287378, baseEnd_287378] using wordTrace_append hprefix tailTrace_287378
  have hstable : (prefixWord ++ tailWord_287378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287378).length < 2 ^ (prefixWord ++ tailWord_287378).sum := by decide
  have hdescent : baseEnd_287378 < baseStart_287378 := by decide
  rcases family_descends (prefixWord ++ tailWord_287378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287388 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_287388 : Nat := 118140960795 + 287388 * 2 ^ 59
def prefixEnd_287388 : Nat := 4983230072969 + 3 ^ 40 * 287388 * 2
def baseEnd_287388 : Nat := 147568178334426826828333

theorem tailTrace_287388 : CollatzResearch.WordTrace tailWord_287388 prefixEnd_287388 147568178334426826828333 := by
  unfold tailWord_287388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5240950741424916403947409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6987934321899888538596545 5240950741424916403947409)
  ·
    refine ⟨3930713056068687302960557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5240950741424916403947409 3930713056068687302960557)
    ·
      refine ⟨1474017396025757738610209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3930713056068687302960557 1474017396025757738610209)
      ·
        refine ⟨1105513047019318303957657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1474017396025757738610209 1105513047019318303957657)
        ·
          refine ⟨829134785264488727968243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105513047019318303957657 829134785264488727968243)
          ·
            refine ⟨1243702177896733091952365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829134785264488727968243 1243702177896733091952365)
            ·
              refine ⟨466388316711274909482137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243702177896733091952365 466388316711274909482137)
              ·
                refine ⟨349791237533456182111603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466388316711274909482137 349791237533456182111603)
                ·
                  refine ⟨524686856300184273167405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349791237533456182111603 524686856300184273167405)
                  ·
                    refine ⟨196757571112569102437777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524686856300184273167405 196757571112569102437777)
                    ·
                      refine ⟨147568178334426826828333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196757571112569102437777 147568178334426826828333)
                      ·
                        rfl

theorem cell23_287388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_287388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287388 prefixEnd_287388 := by exact prefixLift 287388
  have htrace : WordTrace (prefixWord ++ tailWord_287388) baseStart_287388 baseEnd_287388 := by
    simpa [prefixWord, tailWord_287388, baseEnd_287388] using wordTrace_append hprefix tailTrace_287388
  have hstable : (prefixWord ++ tailWord_287388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287388).length < 2 ^ (prefixWord ++ tailWord_287388).sum := by decide
  have hdescent : baseEnd_287388 < baseStart_287388 := by decide
  rcases family_descends (prefixWord ++ tailWord_287388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287397 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_287397 : Nat := 118140960795 + 287397 * 2 ^ 59
def prefixEnd_287397 : Nat := 4983230072969 + 3 ^ 40 * 287397 * 2
def baseEnd_287397 : Nat := 147572799660317291615791

theorem tailTrace_287397 : CollatzResearch.WordTrace tailWord_287397 prefixEnd_287397 147572799660317291615791 := by
  unfold tailWord_287397
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482229739817227344972445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6988153159878151563314963 10482229739817227344972445)
  ·
    refine ⟨3930836152431460254364667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10482229739817227344972445 3930836152431460254364667)
    ·
      refine ⟨5896254228647190381547001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3930836152431460254364667 5896254228647190381547001)
      ·
        refine ⟨4422190671485392786160251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5896254228647190381547001 4422190671485392786160251)
        ·
          refine ⟨6633286007228089179240377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422190671485392786160251 6633286007228089179240377)
          ·
            refine ⟨4974964505421066884430283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6633286007228089179240377 4974964505421066884430283)
            ·
              refine ⟨7462446758131600326645425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974964505421066884430283 7462446758131600326645425)
              ·
                refine ⟨5596835068598700244984069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7462446758131600326645425 5596835068598700244984069)
                ·
                  refine ⟨1049406575362256295934513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5596835068598700244984069 1049406575362256295934513)
                  ·
                    refine ⟨787054931521692221950885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1049406575362256295934513 787054931521692221950885)
                    ·
                      refine ⟨147572799660317291615791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 787054931521692221950885 147572799660317291615791)
                      ·
                        rfl

theorem cell23_287397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_287397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287397 prefixEnd_287397 := by exact prefixLift 287397
  have htrace : WordTrace (prefixWord ++ tailWord_287397) baseStart_287397 baseEnd_287397 := by
    simpa [prefixWord, tailWord_287397, baseEnd_287397] using wordTrace_append hprefix tailTrace_287397
  have hstable : (prefixWord ++ tailWord_287397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287397).length < 2 ^ (prefixWord ++ tailWord_287397).sum := by decide
  have hdescent : baseEnd_287397 < baseStart_287397 := by decide
  rcases family_descends (prefixWord ++ tailWord_287397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287405 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_287405 : Nat := 118140960795 + 287405 * 2 ^ 59
def prefixEnd_287405 : Nat := 4983230072969 + 3 ^ 40 * 287405 * 2
def baseEnd_287405 : Nat := 147576907505553260315755

theorem tailTrace_287405 : CollatzResearch.WordTrace tailWord_287405 prefixEnd_287405 147576907505553260315755 := by
  unfold tailWord_287405
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482521523788244711263669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6988347682525496474175779 10482521523788244711263669)
  ·
    refine ⟨982736392855147941680969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10482521523788244711263669 982736392855147941680969)
    ·
      refine ⟨737052294641360956260727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 982736392855147941680969 737052294641360956260727)
      ·
        refine ⟨1105578441962041434391091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737052294641360956260727 1105578441962041434391091)
        ·
          refine ⟨1658367662943062151586637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105578441962041434391091 1658367662943062151586637)
          ·
            refine ⟨621887873603648306844989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1658367662943062151586637 621887873603648306844989)
            ·
              refine ⟨233207952601368115066871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 621887873603648306844989 233207952601368115066871)
              ·
                refine ⟨349811928902052172600307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233207952601368115066871 349811928902052172600307)
                ·
                  refine ⟨524717893353078258900461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349811928902052172600307 524717893353078258900461)
                  ·
                    refine ⟨196769210007404347087673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524717893353078258900461 196769210007404347087673)
                    ·
                      refine ⟨147576907505553260315755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196769210007404347087673 147576907505553260315755)
                      ·
                        rfl

theorem cell23_287405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_287405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287405 prefixEnd_287405 := by exact prefixLift 287405
  have htrace : WordTrace (prefixWord ++ tailWord_287405) baseStart_287405 baseEnd_287405 := by
    simpa [prefixWord, tailWord_287405, baseEnd_287405] using wordTrace_append hprefix tailTrace_287405
  have hstable : (prefixWord ++ tailWord_287405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287405).length < 2 ^ (prefixWord ++ tailWord_287405).sum := by decide
  have hdescent : baseEnd_287405 < baseStart_287405 := by decide
  rcases family_descends (prefixWord ++ tailWord_287405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287418 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2]
def baseStart_287418 : Nat := 118140960795 + 287418 * 2 ^ 59
def prefixEnd_287418 : Nat := 4983230072969 + 3 ^ 40 * 287418 * 2
def baseEnd_287418 : Nat := 147583582754061709453195

theorem tailTrace_287418 : CollatzResearch.WordTrace tailWord_287418 prefixEnd_287418 147583582754061709453195 := by
  unfold tailWord_287418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620748918185286982871727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6988663781827431954324605 2620748918185286982871727)
  ·
    refine ⟨3931123377277930474307591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2620748918185286982871727 3931123377277930474307591)
    ·
      refine ⟨5896685065916895711461387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931123377277930474307591 5896685065916895711461387)
      ·
        refine ⟨8845027598875343567192081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5896685065916895711461387 8845027598875343567192081)
        ·
          refine ⟨6633770699156507675394061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8845027598875343567192081 6633770699156507675394061)
          ·
            refine ⟨2487664012183690378272773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6633770699156507675394061 2487664012183690378272773)
            ·
              refine ⟨466437002284441945926145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2487664012183690378272773 466437002284441945926145)
              ·
                refine ⟨349827751713331459444609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466437002284441945926145 349827751713331459444609)
                ·
                  refine ⟨262370813784998594583457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349827751713331459444609 262370813784998594583457)
                  ·
                    refine ⟨196778110338748945937593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262370813784998594583457 196778110338748945937593)
                    ·
                      refine ⟨147583582754061709453195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196778110338748945937593 147583582754061709453195)
                      ·
                        rfl

theorem cell23_287418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_287418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287418 prefixEnd_287418 := by exact prefixLift 287418
  have htrace : WordTrace (prefixWord ++ tailWord_287418) baseStart_287418 baseEnd_287418 := by
    simpa [prefixWord, tailWord_287418, baseEnd_287418] using wordTrace_append hprefix tailTrace_287418
  have hstable : (prefixWord ++ tailWord_287418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287418).length < 2 ^ (prefixWord ++ tailWord_287418).sum := by decide
  have hdescent : baseEnd_287418 < baseStart_287418 := by decide
  rcases family_descends (prefixWord ++ tailWord_287418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287434 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_287434 : Nat := 118140960795 + 287434 * 2 ^ 59
def prefixEnd_287434 : Nat := 4983230072969 + 3 ^ 40 * 287434 * 2
def baseEnd_287434 : Nat := 147591798444533646853121

theorem tailTrace_287434 : CollatzResearch.WordTrace tailWord_287434 prefixEnd_287434 147591798444533646853121 := by
  unfold tailWord_287434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620894810170795666017339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6989052827122121776046237 2620894810170795666017339)
  ·
    refine ⟨3931342215256193499026009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2620894810170795666017339 3931342215256193499026009)
    ·
      refine ⟨2948506661442145124269507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3931342215256193499026009 2948506661442145124269507)
      ·
        refine ⟨4422759992163217686404261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948506661442145124269507 4422759992163217686404261)
        ·
          refine ⟨829267498530603316200799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4422759992163217686404261 829267498530603316200799)
          ·
            refine ⟨1243901247795904974301199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829267498530603316200799 1243901247795904974301199)
            ·
              refine ⟨1865851871693857461451799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243901247795904974301199 1865851871693857461451799)
              ·
                refine ⟨2798777807540786192177699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865851871693857461451799 2798777807540786192177699)
                ·
                  refine ⟨4198166711311179288266549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798777807540786192177699 4198166711311179288266549)
                  ·
                    refine ⟨393578129185423058274989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4198166711311179288266549 393578129185423058274989)
                    ·
                      refine ⟨147591798444533646853121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393578129185423058274989 147591798444533646853121)
                      ·
                        rfl

theorem cell23_287434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_287434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287434 prefixEnd_287434 := by exact prefixLift 287434
  have htrace : WordTrace (prefixWord ++ tailWord_287434) baseStart_287434 baseEnd_287434 := by
    simpa [prefixWord, tailWord_287434, baseEnd_287434] using wordTrace_append hprefix tailTrace_287434
  have hstable : (prefixWord ++ tailWord_287434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287434).length < 2 ^ (prefixWord ++ tailWord_287434).sum := by decide
  have hdescent : baseEnd_287434 < baseStart_287434 := by decide
  rcases family_descends (prefixWord ++ tailWord_287434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287487 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_287487 : Nat := 118140960795 + 287487 * 2 ^ 59
def prefixEnd_287487 : Nat := 4983230072969 + 3 ^ 40 * 287487 * 2
def baseEnd_287487 : Nat := 147619012919221939490377

theorem tailTrace_287487 : CollatzResearch.WordTrace tailWord_287487 prefixEnd_287487 147619012919221939490377 := by
  unfold tailWord_287487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10485512309491172715748715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6990341539660781810499143 10485512309491172715748715)
  ·
    refine ⟨15728268464236759073623073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10485512309491172715748715 15728268464236759073623073)
    ·
      refine ⟨11796201348177569305217305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15728268464236759073623073 11796201348177569305217305)
      ·
        refine ⟨8847151011133176978912979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11796201348177569305217305 8847151011133176978912979)
        ·
          refine ⟨13270726516699765468369469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8847151011133176978912979 13270726516699765468369469)
          ·
            refine ⟨4976522443762412050638551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13270726516699765468369469 4976522443762412050638551)
            ·
              refine ⟨7464783665643618075957827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976522443762412050638551 7464783665643618075957827)
              ·
                refine ⟨11197175498465427113936741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7464783665643618075957827 11197175498465427113936741)
                ·
                  refine ⟨2099470405962267583863139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11197175498465427113936741 2099470405962267583863139)
                  ·
                    refine ⟨3149205608943401375794709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099470405962267583863139 3149205608943401375794709)
                    ·
                      refine ⟨147619012919221939490377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3149205608943401375794709 147619012919221939490377)
                      ·
                        rfl

theorem cell23_287487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_287487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287487 prefixEnd_287487 := by exact prefixLift 287487
  have htrace : WordTrace (prefixWord ++ tailWord_287487) baseStart_287487 baseEnd_287487 := by
    simpa [prefixWord, tailWord_287487, baseEnd_287487] using wordTrace_append hprefix tailTrace_287487
  have hstable : (prefixWord ++ tailWord_287487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287487).length < 2 ^ (prefixWord ++ tailWord_287487).sum := by decide
  have hdescent : baseEnd_287487 < baseStart_287487 := by decide
  rcases family_descends (prefixWord ++ tailWord_287487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287544 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_287544 : Nat := 118140960795 + 287544 * 2 ^ 59
def prefixEnd_287544 : Nat := 4983230072969 + 3 ^ 40 * 287544 * 2
def baseEnd_287544 : Nat := 49216093772176072159205

theorem tailTrace_287544 : CollatzResearch.WordTrace tailWord_287544 prefixEnd_287544 49216093772176072159205 := by
  unfold tailWord_287544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5243795635142335725286843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6991727513523114300382457 5243795635142335725286843)
  ·
    refine ⟨7865693452713503587930265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5243795635142335725286843 7865693452713503587930265)
    ·
      refine ⟨5899270089535127690947699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7865693452713503587930265 5899270089535127690947699)
      ·
        refine ⟨8848905134302691536421549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899270089535127690947699 8848905134302691536421549)
        ·
          refine ⟨3318339425363509326158081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8848905134302691536421549 3318339425363509326158081)
          ·
            refine ⟨2488754569022631994618561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318339425363509326158081 2488754569022631994618561)
            ·
              refine ⟨1866565926766973995963921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488754569022631994618561 1866565926766973995963921)
              ·
                refine ⟨1399924445075230496972941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866565926766973995963921 1399924445075230496972941)
                ·
                  refine ⟨524971666903211436364853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1399924445075230496972941 524971666903211436364853)
                  ·
                    refine ⟨49216093772176072159205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 524971666903211436364853 49216093772176072159205)
                    ·
                      rfl

theorem cell23_287544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_287544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287544 prefixEnd_287544 := by exact prefixLift 287544
  have htrace : WordTrace (prefixWord ++ tailWord_287544) baseStart_287544 baseEnd_287544 := by
    simpa [prefixWord, tailWord_287544, baseEnd_287544] using wordTrace_append hprefix tailTrace_287544
  have hstable : (prefixWord ++ tailWord_287544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287544).length < 2 ^ (prefixWord ++ tailWord_287544).sum := by decide
  have hdescent : baseEnd_287544 < baseStart_287544 := by decide
  rcases family_descends (prefixWord ++ tailWord_287544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287547 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_287547 : Nat := 118140960795 + 287547 * 2 ^ 59
def prefixEnd_287547 : Nat := 4983230072969 + 3 ^ 40 * 287547 * 2
def baseEnd_287547 : Nat := 147649821758491704740101

theorem tailTrace_287547 : CollatzResearch.WordTrace tailWord_287547 prefixEnd_287547 147649821758491704740101 := by
  unfold tailWord_287547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10487700689273802962932895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6991800459515868641955263 10487700689273802962932895)
  ·
    refine ⟨15731551033910704444399343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10487700689273802962932895 15731551033910704444399343)
    ·
      refine ⟨23597326550866056666599015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15731551033910704444399343 23597326550866056666599015)
      ·
        refine ⟨35395989826299084999898523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23597326550866056666599015 35395989826299084999898523)
        ·
          refine ⟨53093984739448627499847785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35395989826299084999898523 53093984739448627499847785)
          ·
            refine ⟨39820488554586470624885839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53093984739448627499847785 39820488554586470624885839)
            ·
              refine ⟨59730732831879705937328759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39820488554586470624885839 59730732831879705937328759)
              ·
                refine ⟨89596099247819558905993139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59730732831879705937328759 89596099247819558905993139)
                ·
                  refine ⟨134394148871729338358989709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89596099247819558905993139 134394148871729338358989709)
                  ·
                    refine ⟨50397805826898501884621141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134394148871729338358989709 50397805826898501884621141)
                    ·
                      refine ⟨147649821758491704740101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 50397805826898501884621141 147649821758491704740101)
                      ·
                        rfl

theorem cell23_287547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_287547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287547 prefixEnd_287547 := by exact prefixLift 287547
  have htrace : WordTrace (prefixWord ++ tailWord_287547) baseStart_287547 baseEnd_287547 := by
    simpa [prefixWord, tailWord_287547, baseEnd_287547] using wordTrace_append hprefix tailTrace_287547
  have hstable : (prefixWord ++ tailWord_287547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287547).length < 2 ^ (prefixWord ++ tailWord_287547).sum := by decide
  have hdescent : baseEnd_287547 < baseStart_287547 := by decide
  rcases family_descends (prefixWord ++ tailWord_287547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287561 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 1, 5]
def baseStart_287561 : Nat := 118140960795 + 287561 * 2 ^ 59
def prefixEnd_287561 : Nat := 4983230072969 + 3 ^ 40 * 287561 * 2
def baseEnd_287561 : Nat := 49219003495884883321679

theorem tailTrace_287561 : CollatzResearch.WordTrace tailWord_287561 prefixEnd_287561 49219003495884883321679 := by
  unfold tailWord_287561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488211311223083353942537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6992140874148722235961691 10488211311223083353942537)
  ·
    refine ⟨7866158483417312515456903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10488211311223083353942537 7866158483417312515456903)
    ·
      refine ⟨11799237725125968773185355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7866158483417312515456903 11799237725125968773185355)
      ·
        refine ⟨17698856587688953159778033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11799237725125968773185355 17698856587688953159778033)
        ·
          refine ⟨13274142440766714869833525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17698856587688953159778033 13274142440766714869833525)
          ·
            refine ⟨1244450853821879519046893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13274142440766714869833525 1244450853821879519046893)
            ·
              refine ⟨466669070183204819642585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1244450853821879519046893 466669070183204819642585)
              ·
                refine ⟨350001802637403614731939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466669070183204819642585 350001802637403614731939)
                ·
                  refine ⟨525002703956105422097909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350001802637403614731939 525002703956105422097909)
                  ·
                    refine ⟨49219003495884883321679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 525002703956105422097909 49219003495884883321679)
                    ·
                      rfl

theorem cell23_287561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_287561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287561 prefixEnd_287561 := by exact prefixLift 287561
  have htrace : WordTrace (prefixWord ++ tailWord_287561) baseStart_287561 baseEnd_287561 := by
    simpa [prefixWord, tailWord_287561, baseEnd_287561] using wordTrace_append hprefix tailTrace_287561
  have hstable : (prefixWord ++ tailWord_287561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287561).length < 2 ^ (prefixWord ++ tailWord_287561).sum := by decide
  have hdescent : baseEnd_287561 < baseStart_287561 := by decide
  rcases family_descends (prefixWord ++ tailWord_287561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287578 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_287578 : Nat := 118140960795 + 287578 * 2 ^ 59
def prefixEnd_287578 : Nat := 4983230072969 + 3 ^ 40 * 287578 * 2
def baseEnd_287578 : Nat := 49221913219593694484153

theorem tailTrace_287578 : CollatzResearch.WordTrace tailWord_287578 prefixEnd_287578 49221913219593694484153 := by
  unfold tailWord_287578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622207838040373814327847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6992554234774330171540925 2622207838040373814327847)
  ·
    refine ⟨3933311757060560721491771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622207838040373814327847 3933311757060560721491771)
    ·
      refine ⟨5899967635590841082237657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933311757060560721491771 5899967635590841082237657)
      ·
        refine ⟨4424975726693130811678243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5899967635590841082237657 4424975726693130811678243)
        ·
          refine ⟨6637463590039696217517365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4424975726693130811678243 6637463590039696217517365)
          ·
            refine ⟨622262211566221520392253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6637463590039696217517365 622262211566221520392253)
            ·
              refine ⟨233348329337333070147095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 622262211566221520392253 233348329337333070147095)
              ·
                refine ⟨350022494005999605220643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233348329337333070147095 350022494005999605220643)
                ·
                  refine ⟨525033741008999407830965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350022494005999605220643 525033741008999407830965)
                  ·
                    refine ⟨49221913219593694484153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 525033741008999407830965 49221913219593694484153)
                    ·
                      rfl

theorem cell23_287578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_287578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287578 prefixEnd_287578 := by exact prefixLift 287578
  have htrace : WordTrace (prefixWord ++ tailWord_287578) baseStart_287578 baseEnd_287578 := by
    simpa [prefixWord, tailWord_287578, baseEnd_287578] using wordTrace_append hprefix tailTrace_287578
  have hstable : (prefixWord ++ tailWord_287578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287578).length < 2 ^ (prefixWord ++ tailWord_287578).sum := by decide
  have hdescent : baseEnd_287578 < baseStart_287578 := by decide
  rcases family_descends (prefixWord ++ tailWord_287578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287592 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_287592 : Nat := 118140960795 + 287592 * 2 ^ 59
def prefixEnd_287592 : Nat := 4983230072969 + 3 ^ 40 * 287592 * 2
def baseEnd_287592 : Nat := 147672928387944028677395

theorem tailTrace_287592 : CollatzResearch.WordTrace tailWord_287592 prefixEnd_287592 147672928387944028677395 := by
  unfold tailWord_287592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244670987055387824160515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6992894649407183765547353 5244670987055387824160515)
  ·
    refine ⟨7867006480583081736240773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5244670987055387824160515 7867006480583081736240773)
    ·
      refine ⟨1475063715109327825545145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7867006480583081736240773 1475063715109327825545145)
      ·
        refine ⟨1106297786331995869158859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1475063715109327825545145 1106297786331995869158859)
        ·
          refine ⟨1659446679497993803738289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106297786331995869158859 1659446679497993803738289)
          ·
            refine ⟨1244585009623495352803717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1659446679497993803738289 1244585009623495352803717)
            ·
              refine ⟨233359689304405378650697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1244585009623495352803717 233359689304405378650697)
              ·
                refine ⟨175019766978304033988023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233359689304405378650697 175019766978304033988023)
                ·
                  refine ⟨262529650467456050982035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175019766978304033988023 262529650467456050982035)
                  ·
                    refine ⟨393794475701184076473053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262529650467456050982035 393794475701184076473053)
                    ·
                      refine ⟨147672928387944028677395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393794475701184076473053 147672928387944028677395)
                      ·
                        rfl

theorem cell23_287592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_287592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287592 prefixEnd_287592 := by exact prefixLift 287592
  have htrace : WordTrace (prefixWord ++ tailWord_287592) baseStart_287592 baseEnd_287592 := by
    simpa [prefixWord, tailWord_287592, baseEnd_287592] using wordTrace_append hprefix tailTrace_287592
  have hstable : (prefixWord ++ tailWord_287592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287592).length < 2 ^ (prefixWord ++ tailWord_287592).sum := by decide
  have hdescent : baseEnd_287592 < baseStart_287592 := by decide
  rcases family_descends (prefixWord ++ tailWord_287592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287601 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_287601 : Nat := 118140960795 + 287601 * 2 ^ 59
def prefixEnd_287601 : Nat := 4983230072969 + 3 ^ 40 * 287601 * 2
def baseEnd_287601 : Nat := 147677549713834493464853

theorem tailTrace_287601 : CollatzResearch.WordTrace tailWord_287601 prefixEnd_287601 147677549713834493464853 := by
  unfold tailWord_287601
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489670231078170185398657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6993113487385446790265771 10489670231078170185398657)
  ·
    refine ⟨7867252673308627639048993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10489670231078170185398657 7867252673308627639048993)
    ·
      refine ⟨5900439504981470729286745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7867252673308627639048993 5900439504981470729286745)
      ·
        refine ⟨4425329628736103046965059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5900439504981470729286745 4425329628736103046965059)
        ·
          refine ⟨6637994443104154570447589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425329628736103046965059 6637994443104154570447589)
          ·
            refine ⟨1244623958082028981958923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6637994443104154570447589 1244623958082028981958923)
            ·
              refine ⟨1866935937123043472938385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244623958082028981958923 1866935937123043472938385)
              ·
                refine ⟨1400201952842282604703789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866935937123043472938385 1400201952842282604703789)
                ·
                  refine ⟨525075732315855976763921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1400201952842282604703789 525075732315855976763921)
                  ·
                    refine ⟨393806799236891982572941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 525075732315855976763921 393806799236891982572941)
                    ·
                      refine ⟨147677549713834493464853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393806799236891982572941 147677549713834493464853)
                      ·
                        rfl

theorem cell23_287601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_287601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287601 prefixEnd_287601 := by exact prefixLift 287601
  have htrace : WordTrace (prefixWord ++ tailWord_287601) baseStart_287601 baseEnd_287601 := by
    simpa [prefixWord, tailWord_287601, baseEnd_287601] using wordTrace_append hprefix tailTrace_287601
  have hstable : (prefixWord ++ tailWord_287601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287601).length < 2 ^ (prefixWord ++ tailWord_287601).sum := by decide
  have hdescent : baseEnd_287601 < baseStart_287601 := by decide
  rcases family_descends (prefixWord ++ tailWord_287601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287621 : List Nat := [1, 3, 1, 1, 3, 4, 3, 7]
def baseStart_287621 : Nat := 118140960795 + 287621 * 2 ^ 59
def prefixEnd_287621 : Nat := 4983230072969 + 3 ^ 40 * 287621 * 2
def baseEnd_287621 : Nat := 5469919234330533896843

theorem tailTrace_287621 : CollatzResearch.WordTrace tailWord_287621 prefixEnd_287621 5469919234330533896843 := by
  unfold tailWord_287621
  simp only [CollatzResearch.WordTrace]
  refine ⟨10490399691005713601126717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6993599794003809067417811 10490399691005713601126717)
  ·
    refine ⟨3933899884127142600422519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10490399691005713601126717 3933899884127142600422519)
    ·
      refine ⟨5900849826190713900633779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933899884127142600422519 5900849826190713900633779)
      ·
        refine ⟨8851274739286070850950669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5900849826190713900633779 8851274739286070850950669)
        ·
          refine ⟨3319228027232276569106501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8851274739286070850950669 3319228027232276569106501)
          ·
            refine ⟨622355255106051856707469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3319228027232276569106501 622355255106051856707469)
            ·
              refine ⟨233383220664769446265301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 622355255106051856707469 233383220664769446265301)
              ·
                refine ⟨5469919234330533896843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 233383220664769446265301 5469919234330533896843)
                ·
                  rfl

theorem cell23_287621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 7].length) (baseStart_287621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287621 prefixEnd_287621 := by exact prefixLift 287621
  have htrace : WordTrace (prefixWord ++ tailWord_287621) baseStart_287621 baseEnd_287621 := by
    simpa [prefixWord, tailWord_287621, baseEnd_287621] using wordTrace_append hprefix tailTrace_287621
  have hstable : (prefixWord ++ tailWord_287621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287621).length < 2 ^ (prefixWord ++ tailWord_287621).sum := by decide
  have hdescent : baseEnd_287621 < baseStart_287621 := by decide
  rcases family_descends (prefixWord ++ tailWord_287621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287642 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_287642 : Nat := 118140960795 + 287642 * 2 ^ 59
def prefixEnd_287642 : Nat := 4983230072969 + 3 ^ 40 * 287642 * 2
def baseEnd_287642 : Nat := 49232867473556277684055

theorem tailTrace_287642 : CollatzResearch.WordTrace tailWord_287642 prefixEnd_287642 49232867473556277684055 := by
  unfold tailWord_287642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622791405982408546910295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6994110415953089458427453 2622791405982408546910295)
  ·
    refine ⟨3934187108973612820365443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622791405982408546910295 3934187108973612820365443)
    ·
      refine ⟨5901280663460419230548165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3934187108973612820365443 5901280663460419230548165)
      ·
        refine ⟨1106490124398828605727781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5901280663460419230548165 1106490124398828605727781)
        ·
          refine ⟨207466898324780363573959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1106490124398828605727781 207466898324780363573959)
          ·
            refine ⟨311200347487170545360939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207466898324780363573959 311200347487170545360939)
            ·
              refine ⟨466800521230755818041409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311200347487170545360939 466800521230755818041409)
              ·
                refine ⟨350100390923066863531057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466800521230755818041409 350100390923066863531057)
                ·
                  refine ⟨262575293192300147648293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350100390923066863531057 262575293192300147648293)
                  ·
                    refine ⟨49232867473556277684055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262575293192300147648293 49232867473556277684055)
                    ·
                      rfl

theorem cell23_287642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_287642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287642 prefixEnd_287642 := by exact prefixLift 287642
  have htrace : WordTrace (prefixWord ++ tailWord_287642) baseStart_287642 baseEnd_287642 := by
    simpa [prefixWord, tailWord_287642, baseEnd_287642] using wordTrace_append hprefix tailTrace_287642
  have hstable : (prefixWord ++ tailWord_287642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287642).length < 2 ^ (prefixWord ++ tailWord_287642).sum := by decide
  have hdescent : baseEnd_287642 < baseStart_287642 := by decide
  rcases family_descends (prefixWord ++ tailWord_287642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287665 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_287665 : Nat := 118140960795 + 287665 * 2 ^ 59
def prefixEnd_287665 : Nat := 4983230072969 + 3 ^ 40 * 287665 * 2
def baseEnd_287665 : Nat := 147710412475722243064559

theorem tailTrace_287665 : CollatzResearch.WordTrace tailWord_287665 prefixEnd_287665 147710412475722243064559 := by
  unfold tailWord_287665
  simp only [CollatzResearch.WordTrace]
  refine ⟨10492004502846309115728449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6994669668564206077152299 10492004502846309115728449)
  ·
    refine ⟨7869003377134731836796337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10492004502846309115728449 7869003377134731836796337)
    ·
      refine ⟨5901752532851048877597253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7869003377134731836796337 5901752532851048877597253)
      ·
        refine ⟨1106578599909571664549485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5901752532851048877597253 1106578599909571664549485)
        ·
          refine ⟨414966974966089374206057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1106578599909571664549485 414966974966089374206057)
          ·
            refine ⟨311225231224567030654543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414966974966089374206057 311225231224567030654543)
            ·
              refine ⟨466837846836850545981815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311225231224567030654543 466837846836850545981815)
              ·
                refine ⟨700256770255275818972723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466837846836850545981815 700256770255275818972723)
                ·
                  refine ⟨1050385155382913728459085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700256770255275818972723 1050385155382913728459085)
                  ·
                    refine ⟨393894433268592648172157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1050385155382913728459085 393894433268592648172157)
                    ·
                      refine ⟨147710412475722243064559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 393894433268592648172157 147710412475722243064559)
                      ·
                        rfl

theorem cell23_287665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_287665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287665 prefixEnd_287665 := by exact prefixLift 287665
  have htrace : WordTrace (prefixWord ++ tailWord_287665) baseStart_287665 baseEnd_287665 := by
    simpa [prefixWord, tailWord_287665, baseEnd_287665] using wordTrace_append hprefix tailTrace_287665
  have hstable : (prefixWord ++ tailWord_287665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287665).length < 2 ^ (prefixWord ++ tailWord_287665).sum := by decide
  have hdescent : baseEnd_287665 < baseStart_287665 := by decide
  rcases family_descends (prefixWord ++ tailWord_287665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287691 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5]
def baseStart_287691 : Nat := 118140960795 + 287691 * 2 ^ 59
def prefixEnd_287691 : Nat := 4983230072969 + 3 ^ 40 * 287691 * 2
def baseEnd_287691 : Nat := 147723762972739141339439

theorem tailTrace_287691 : CollatzResearch.WordTrace tailWord_287691 prefixEnd_287691 147723762972739141339439 := by
  unfold tailWord_287691
  simp only [CollatzResearch.WordTrace]
  refine ⟨10492952800752115556174927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6995301867168077037449951 10492952800752115556174927)
  ·
    refine ⟨15739429201128173334262391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10492952800752115556174927 15739429201128173334262391)
    ·
      refine ⟨23609143801692260001393587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15739429201128173334262391 23609143801692260001393587)
      ·
        refine ⟨35413715702538390002090381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23609143801692260001393587 35413715702538390002090381)
        ·
          refine ⟨13280143388451896250783893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35413715702538390002090381 13280143388451896250783893)
          ·
            refine ⟨622506721333682636755495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13280143388451896250783893 622506721333682636755495)
            ·
              refine ⟨933760082000523955133243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622506721333682636755495 933760082000523955133243)
              ·
                refine ⟨1400640123000785932699865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933760082000523955133243 1400640123000785932699865)
                ·
                  refine ⟨1050480092250589449524899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1400640123000785932699865 1050480092250589449524899)
                  ·
                    refine ⟨1575720138375884174287349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1050480092250589449524899 1575720138375884174287349)
                    ·
                      refine ⟨147723762972739141339439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1575720138375884174287349 147723762972739141339439)
                      ·
                        rfl

theorem cell23_287691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].length) (baseStart_287691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287691 prefixEnd_287691 := by exact prefixLift 287691
  have htrace : WordTrace (prefixWord ++ tailWord_287691) baseStart_287691 baseEnd_287691 := by
    simpa [prefixWord, tailWord_287691, baseEnd_287691] using wordTrace_append hprefix tailTrace_287691
  have hstable : (prefixWord ++ tailWord_287691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287691).length < 2 ^ (prefixWord ++ tailWord_287691).sum := by decide
  have hdescent : baseEnd_287691 < baseStart_287691 := by decide
  rcases family_descends (prefixWord ++ tailWord_287691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287705 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 4, 2, 2]
def baseStart_287705 : Nat := 118140960795 + 287705 * 2 ^ 59
def prefixEnd_287705 : Nat := 4983230072969 + 3 ^ 40 * 287705 * 2
def baseEnd_287705 : Nat := 147730951701902086564375

theorem tailTrace_287705 : CollatzResearch.WordTrace tailWord_287705 prefixEnd_287705 147730951701902086564375 := by
  unfold tailWord_287705
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493463422701395947184569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6995642281800930631456379 10493463422701395947184569)
  ·
    refine ⟨7870097567026046960388427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10493463422701395947184569 7870097567026046960388427)
    ·
      refine ⟨11805146350539070440582641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7870097567026046960388427 11805146350539070440582641)
      ·
        refine ⟨8853859762904302830436981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11805146350539070440582641 8853859762904302830436981)
        ·
          refine ⟨830049352772278390353467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8853859762904302830436981 830049352772278390353467)
          ·
            refine ⟨1245074029158417585530201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830049352772278390353467 1245074029158417585530201)
            ·
              refine ⟨933805521868813189147651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245074029158417585530201 933805521868813189147651)
              ·
                refine ⟨1400708282803219783721477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933805521868813189147651 1400708282803219783721477)
                ·
                  refine ⟨262632803025603709447777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400708282803219783721477 262632803025603709447777)
                  ·
                    refine ⟨196974602269202782085833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262632803025603709447777 196974602269202782085833)
                    ·
                      refine ⟨147730951701902086564375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196974602269202782085833 147730951701902086564375)
                      ·
                        rfl

theorem cell23_287705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_287705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287705 prefixEnd_287705 := by exact prefixLift 287705
  have htrace : WordTrace (prefixWord ++ tailWord_287705) baseStart_287705 baseEnd_287705 := by
    simpa [prefixWord, tailWord_287705, baseEnd_287705] using wordTrace_append hprefix tailTrace_287705
  have hstable : (prefixWord ++ tailWord_287705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287705).length < 2 ^ (prefixWord ++ tailWord_287705).sum := by decide
  have hdescent : baseEnd_287705 < baseStart_287705 := by decide
  rcases family_descends (prefixWord ++ tailWord_287705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287722 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_287722 : Nat := 118140960795 + 287722 * 2 ^ 59
def prefixEnd_287722 : Nat := 4983230072969 + 3 ^ 40 * 287722 * 2
def baseEnd_287722 : Nat := 147739680873028520051797

theorem tailTrace_287722 : CollatzResearch.WordTrace tailWord_287722 prefixEnd_287722 147739680873028520051797 := by
  unfold tailWord_287722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623520865909951962638355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6996055642426538567035613 2623520865909951962638355)
  ·
    refine ⟨3935281298864927943957533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2623520865909951962638355 3935281298864927943957533)
    ·
      refine ⟨1475730487074347978984075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3935281298864927943957533 1475730487074347978984075)
      ·
        refine ⟨2213595730611521968476113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475730487074347978984075 2213595730611521968476113)
        ·
          refine ⟨1660196797958641476357085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213595730611521968476113 1660196797958641476357085)
          ·
            refine ⟨622573799234490553633907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1660196797958641476357085 622573799234490553633907)
            ·
              refine ⟨933860698851735830450861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622573799234490553633907 933860698851735830450861)
              ·
                refine ⟨350197762069400936419073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933860698851735830450861 350197762069400936419073)
                ·
                  refine ⟨262648321552050702314305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350197762069400936419073 262648321552050702314305)
                  ·
                    refine ⟨196986241164038026735729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262648321552050702314305 196986241164038026735729)
                    ·
                      refine ⟨147739680873028520051797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 196986241164038026735729 147739680873028520051797)
                      ·
                        rfl

theorem cell23_287722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_287722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287722 prefixEnd_287722 := by exact prefixLift 287722
  have htrace : WordTrace (prefixWord ++ tailWord_287722) baseStart_287722 baseEnd_287722 := by
    simpa [prefixWord, tailWord_287722, baseEnd_287722] using wordTrace_append hprefix tailTrace_287722
  have hstable : (prefixWord ++ tailWord_287722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287722).length < 2 ^ (prefixWord ++ tailWord_287722).sum := by decide
  have hdescent : baseEnd_287722 < baseStart_287722 := by decide
  rcases family_descends (prefixWord ++ tailWord_287722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287751 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_287751 : Nat := 118140960795 + 287751 * 2 ^ 59
def prefixEnd_287751 : Nat := 4983230072969 + 3 ^ 40 * 287751 * 2
def baseEnd_287751 : Nat := 147754571812008906589163

theorem tailTrace_287751 : CollatzResearch.WordTrace tailWord_287751 prefixEnd_287751 147754571812008906589163 := by
  unfold tailWord_287751
  simp only [CollatzResearch.WordTrace]
  refine ⟨10495141180534745803359107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6996760787023163868906071 10495141180534745803359107)
  ·
    refine ⟨15742711770802118705038661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10495141180534745803359107 15742711770802118705038661)
    ·
      refine ⟨2951758457025397257194749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15742711770802118705038661 2951758457025397257194749)
      ·
        refine ⟨1106909421384523971448031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2951758457025397257194749 1106909421384523971448031)
        ·
          refine ⟨1660364132076785957172047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106909421384523971448031 1660364132076785957172047)
          ·
            refine ⟨2490546198115178935758071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660364132076785957172047 2490546198115178935758071)
            ·
              refine ⟨3735819297172768403637107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490546198115178935758071 3735819297172768403637107)
              ·
                refine ⟨5603728945759152605455661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735819297172768403637107 5603728945759152605455661)
                ·
                  refine ⟨2101398354659682227045873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5603728945759152605455661 2101398354659682227045873)
                  ·
                    refine ⟨1576048765994761670284405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2101398354659682227045873 1576048765994761670284405)
                    ·
                      refine ⟨147754571812008906589163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1576048765994761670284405 147754571812008906589163)
                      ·
                        rfl

theorem cell23_287751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_287751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287751 prefixEnd_287751 := by exact prefixLift 287751
  have htrace : WordTrace (prefixWord ++ tailWord_287751) baseStart_287751 baseEnd_287751 := by
    simpa [prefixWord, tailWord_287751, baseEnd_287751] using wordTrace_append hprefix tailTrace_287751
  have hstable : (prefixWord ++ tailWord_287751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287751).length < 2 ^ (prefixWord ++ tailWord_287751).sum := by decide
  have hdescent : baseEnd_287751 < baseStart_287751 := by decide
  rcases family_descends (prefixWord ++ tailWord_287751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287758 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_287758 : Nat := 118140960795 + 287758 * 2 ^ 59
def prefixEnd_287758 : Nat := 4983230072969 + 3 ^ 40 * 287758 * 2
def baseEnd_287758 : Nat := 49252722058863459733877

theorem tailTrace_287758 : CollatzResearch.WordTrace tailWord_287758 prefixEnd_287758 49252722058863459733877 := by
  unfold tailWord_287758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311924561438673249857991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6996930994339590665909285 1311924561438673249857991)
  ·
    refine ⟨1967886842158009874786987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1311924561438673249857991 1967886842158009874786987)
    ·
      refine ⟨2951830263237014812180481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1967886842158009874786987 2951830263237014812180481)
      ·
        refine ⟨2213872697427761109135361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2951830263237014812180481 2213872697427761109135361)
        ·
          refine ⟨1660404523070820831851521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213872697427761109135361 1660404523070820831851521)
          ·
            refine ⟨1245303392303115623888641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660404523070820831851521 1245303392303115623888641)
            ·
              refine ⟨933977544227336717916481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245303392303115623888641 933977544227336717916481)
              ·
                refine ⟨700483158170502538437361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933977544227336717916481 700483158170502538437361)
                ·
                  refine ⟨525362368627876903828021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 700483158170502538437361 525362368627876903828021)
                  ·
                    refine ⟨49252722058863459733877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 525362368627876903828021 49252722058863459733877)
                    ·
                      rfl

theorem cell23_287758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_287758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287758 prefixEnd_287758 := by exact prefixLift 287758
  have htrace : WordTrace (prefixWord ++ tailWord_287758) baseStart_287758 baseEnd_287758 := by
    simpa [prefixWord, tailWord_287758, baseEnd_287758] using wordTrace_append hprefix tailTrace_287758
  have hstable : (prefixWord ++ tailWord_287758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287758).length < 2 ^ (prefixWord ++ tailWord_287758).sum := by decide
  have hdescent : baseEnd_287758 < baseStart_287758 := by decide
  rcases family_descends (prefixWord ++ tailWord_287758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287788 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_287788 : Nat := 118140960795 + 287788 * 2 ^ 59
def prefixEnd_287788 : Nat := 4983230072969 + 3 ^ 40 * 287788 * 2
def baseEnd_287788 : Nat := 49257856865408420608831

theorem tailTrace_287788 : CollatzResearch.WordTrace tailWord_287788 prefixEnd_287788 49257856865408420608831 := by
  unfold tailWord_287788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5248245340700350561228009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6997660454267134081637345 5248245340700350561228009)
  ·
    refine ⟨3936184005525262920921007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5248245340700350561228009 3936184005525262920921007)
    ·
      refine ⟨5904276008287894381381511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3936184005525262920921007 5904276008287894381381511)
      ·
        refine ⟨8856414012431841572072267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904276008287894381381511 8856414012431841572072267)
        ·
          refine ⟨13284621018647762358108401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8856414012431841572072267 13284621018647762358108401)
          ·
            refine ⟨9963465763985821768581301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13284621018647762358108401 9963465763985821768581301)
            ·
              refine ⟨934074915373670790804497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9963465763985821768581301 934074915373670790804497)
              ·
                refine ⟨700556186530253093103373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934074915373670790804497 700556186530253093103373)
                ·
                  refine ⟨262708569948844909913765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700556186530253093103373 262708569948844909913765)
                  ·
                    refine ⟨49257856865408420608831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262708569948844909913765 49257856865408420608831)
                    ·
                      rfl

theorem cell23_287788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_287788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287788 prefixEnd_287788 := by exact prefixLift 287788
  have htrace : WordTrace (prefixWord ++ tailWord_287788) baseStart_287788 baseEnd_287788 := by
    simpa [prefixWord, tailWord_287788, baseEnd_287788] using wordTrace_append hprefix tailTrace_287788
  have hstable : (prefixWord ++ tailWord_287788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287788).length < 2 ^ (prefixWord ++ tailWord_287788).sum := by decide
  have hdescent : baseEnd_287788 < baseStart_287788 := by decide
  rcases family_descends (prefixWord ++ tailWord_287788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287818 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_287818 : Nat := 118140960795 + 287818 * 2 ^ 59
def prefixEnd_287818 : Nat := 4983230072969 + 3 ^ 40 * 287818 * 2
def baseEnd_287818 : Nat := 16420997223984460494595

theorem tailTrace_287818 : CollatzResearch.WordTrace tailWord_287818 prefixEnd_287818 16420997223984460494595 := by
  unfold tailWord_287818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624396217823004061512027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6998389914194677497365405 2624396217823004061512027)
  ·
    refine ⟨3936594326734506092268041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624396217823004061512027 3936594326734506092268041)
    ·
      refine ⟨2952445745050879569201031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3936594326734506092268041 2952445745050879569201031)
      ·
        refine ⟨4428668617576319353801547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952445745050879569201031 4428668617576319353801547)
        ·
          refine ⟨6643002926364479030702321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4428668617576319353801547 6643002926364479030702321)
          ·
            refine ⟨4982252194773359273026741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6643002926364479030702321 4982252194773359273026741)
            ·
              refine ⟨467086143260002431846257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4982252194773359273026741 467086143260002431846257)
              ·
                refine ⟨350314607445001823884693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467086143260002431846257 350314607445001823884693)
                ·
                  refine ⟨16420997223984460494595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 350314607445001823884693 16420997223984460494595)
                  ·
                    rfl

theorem cell23_287818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_287818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287818 prefixEnd_287818 := by exact prefixLift 287818
  have htrace : WordTrace (prefixWord ++ tailWord_287818) baseStart_287818 baseEnd_287818 := by
    simpa [prefixWord, tailWord_287818, baseEnd_287818] using wordTrace_append hprefix tailTrace_287818
  have hstable : (prefixWord ++ tailWord_287818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287818).length < 2 ^ (prefixWord ++ tailWord_287818).sum := by decide
  have hdescent : baseEnd_287818 < baseStart_287818 := by decide
  rcases family_descends (prefixWord ++ tailWord_287818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287841 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_287841 : Nat := 118140960795 + 287841 * 2 ^ 59
def prefixEnd_287841 : Nat := 4983230072969 + 3 ^ 40 * 287841 * 2
def baseEnd_287841 : Nat := 147800785070913554463749

theorem tailTrace_287841 : CollatzResearch.WordTrace tailWord_287841 prefixEnd_287841 147800785070913554463749 := by
  unfold tailWord_287841
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498423750208691174135377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6998949166805794116090251 10498423750208691174135377)
  ·
    refine ⟨7873817812656518380601533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10498423750208691174135377 7873817812656518380601533)
    ·
      refine ⟨2952681679746194392725575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7873817812656518380601533 2952681679746194392725575)
      ·
        refine ⟨4429022519619291589088363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952681679746194392725575 4429022519619291589088363)
        ·
          refine ⟨6643533779428937383632545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429022519619291589088363 6643533779428937383632545)
          ·
            refine ⟨4982650334571703037724409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6643533779428937383632545 4982650334571703037724409)
            ·
              refine ⟨3736987750928777278293307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4982650334571703037724409 3736987750928777278293307)
              ·
                refine ⟨5605481626393165917439961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736987750928777278293307 5605481626393165917439961)
                ·
                  refine ⟨4204111219794874438079971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605481626393165917439961 4204111219794874438079971)
                  ·
                    refine ⟨6306166829692311657119957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204111219794874438079971 6306166829692311657119957)
                    ·
                      refine ⟨147800785070913554463749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6306166829692311657119957 147800785070913554463749)
                      ·
                        rfl

theorem cell23_287841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_287841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287841 prefixEnd_287841 := by exact prefixLift 287841
  have htrace : WordTrace (prefixWord ++ tailWord_287841) baseStart_287841 baseEnd_287841 := by
    simpa [prefixWord, tailWord_287841, baseEnd_287841] using wordTrace_append hprefix tailTrace_287841
  have hstable : (prefixWord ++ tailWord_287841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287841).length < 2 ^ (prefixWord ++ tailWord_287841).sum := by decide
  have hdescent : baseEnd_287841 < baseStart_287841 := by decide
  rcases family_descends (prefixWord ++ tailWord_287841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287845 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_287845 : Nat := 118140960795 + 287845 * 2 ^ 59
def prefixEnd_287845 : Nat := 4983230072969 + 3 ^ 40 * 287845 * 2
def baseEnd_287845 : Nat := 147802838993531538813731

theorem tailTrace_287845 : CollatzResearch.WordTrace tailWord_287845 prefixEnd_287845 147802838993531538813731 := by
  unfold tailWord_287845
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498569642194199857280989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6999046428129466571520659 10498569642194199857280989)
  ·
    refine ⟨3936963615822824946480371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10498569642194199857280989 3936963615822824946480371)
    ·
      refine ⟨5905445423734237419720557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3936963615822824946480371 5905445423734237419720557)
      ·
        refine ⟨2214542033900339032395209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5905445423734237419720557 2214542033900339032395209)
        ·
          refine ⟨1660906525425254274296407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2214542033900339032395209 1660906525425254274296407)
          ·
            refine ⟨2491359788137881411444611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660906525425254274296407 2491359788137881411444611)
            ·
              refine ⟨3737039682206822117166917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491359788137881411444611 3737039682206822117166917)
              ·
                refine ⟨700694940413779146968797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3737039682206822117166917 700694940413779146968797)
                ·
                  refine ⟨262760602655167180113299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700694940413779146968797 262760602655167180113299)
                  ·
                    refine ⟨394140903982750770169949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262760602655167180113299 394140903982750770169949)
                    ·
                      refine ⟨147802838993531538813731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 394140903982750770169949 147802838993531538813731)
                      ·
                        rfl

theorem cell23_287845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_287845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287845 prefixEnd_287845 := by exact prefixLift 287845
  have htrace : WordTrace (prefixWord ++ tailWord_287845) baseStart_287845 baseEnd_287845 := by
    simpa [prefixWord, tailWord_287845, baseEnd_287845] using wordTrace_append hprefix tailTrace_287845
  have hstable : (prefixWord ++ tailWord_287845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287845).length < 2 ^ (prefixWord ++ tailWord_287845).sum := by decide
  have hdescent : baseEnd_287845 < baseStart_287845 := by decide
  rcases family_descends (prefixWord ++ tailWord_287845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287851 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4]
def baseStart_287851 : Nat := 118140960795 + 287851 * 2 ^ 59
def prefixEnd_287851 : Nat := 4983230072969 + 3 ^ 40 * 287851 * 2
def baseEnd_287851 : Nat := 147805919877458515338703

theorem tailTrace_287851 : CollatzResearch.WordTrace tailWord_287851 prefixEnd_287851 147805919877458515338703 := by
  unfold tailWord_287851
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498788480172462881999407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6999192320114975254666271 10498788480172462881999407)
  ·
    refine ⟨15748182720258694322999111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10498788480172462881999407 15748182720258694322999111)
    ·
      refine ⟨23622274080388041484498667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15748182720258694322999111 23622274080388041484498667)
      ·
        refine ⟨35433411120582062226748001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23622274080388041484498667 35433411120582062226748001)
        ·
          refine ⟨26575058340436546670061001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35433411120582062226748001 26575058340436546670061001)
          ·
            refine ⟨19931293755327410002545751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26575058340436546670061001 19931293755327410002545751)
            ·
              refine ⟨29896940632991115003818627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19931293755327410002545751 29896940632991115003818627)
              ·
                refine ⟨44845410949486672505727941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29896940632991115003818627 44845410949486672505727941)
                ·
                  refine ⟨8408514553028751094823989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44845410949486672505727941 8408514553028751094823989)
                  ·
                    refine ⟨788298239346445415139749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8408514553028751094823989 788298239346445415139749)
                    ·
                      refine ⟨147805919877458515338703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 788298239346445415139749 147805919877458515338703)
                      ·
                        rfl

theorem cell23_287851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_287851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287851 prefixEnd_287851 := by exact prefixLift 287851
  have htrace : WordTrace (prefixWord ++ tailWord_287851) baseStart_287851 baseEnd_287851 := by
    simpa [prefixWord, tailWord_287851, baseEnd_287851] using wordTrace_append hprefix tailTrace_287851
  have hstable : (prefixWord ++ tailWord_287851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287851).length < 2 ^ (prefixWord ++ tailWord_287851).sum := by decide
  have hdescent : baseEnd_287851 < baseStart_287851 := by decide
  rcases family_descends (prefixWord ++ tailWord_287851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287855 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 2, 3, 2]
def baseStart_287855 : Nat := 118140960795 + 287855 * 2 ^ 59
def prefixEnd_287855 : Nat := 4983230072969 + 3 ^ 40 * 287855 * 2
def baseEnd_287855 : Nat := 147807973800076499688685

theorem tailTrace_287855 : CollatzResearch.WordTrace tailWord_287855 prefixEnd_287855 147807973800076499688685 := by
  unfold tailWord_287855
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498934372157971565145019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6999289581438647710096679 10498934372157971565145019)
  ·
    refine ⟨15748401558236957347717529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10498934372157971565145019 15748401558236957347717529)
    ·
      refine ⟨11811301168677718010788147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15748401558236957347717529 11811301168677718010788147)
      ·
        refine ⟨17716951753016577016182221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11811301168677718010788147 17716951753016577016182221)
        ·
          refine ⟨6643856907381216381068333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17716951753016577016182221 6643856907381216381068333)
          ·
            refine ⟨2491446340267956142900625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6643856907381216381068333 2491446340267956142900625)
            ·
              refine ⟨1868584755200967107175469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491446340267956142900625 1868584755200967107175469)
              ·
                refine ⟨700719283200362665190801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1868584755200967107175469 700719283200362665190801)
                ·
                  refine ⟨525539462400271998893101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 700719283200362665190801 525539462400271998893101)
                  ·
                    refine ⟨197077298400101999584913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525539462400271998893101 197077298400101999584913)
                    ·
                      refine ⟨147807973800076499688685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197077298400101999584913 147807973800076499688685)
                      ·
                        rfl

theorem cell23_287855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3, 2].length) (baseStart_287855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287855 prefixEnd_287855 := by exact prefixLift 287855
  have htrace : WordTrace (prefixWord ++ tailWord_287855) baseStart_287855 baseEnd_287855 := by
    simpa [prefixWord, tailWord_287855, baseEnd_287855] using wordTrace_append hprefix tailTrace_287855
  have hstable : (prefixWord ++ tailWord_287855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287855).length < 2 ^ (prefixWord ++ tailWord_287855).sum := by decide
  have hdescent : baseEnd_287855 < baseStart_287855 := by decide
  rcases family_descends (prefixWord ++ tailWord_287855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287891 : List Nat := [1, 1, 1, 2, 1, 2, 5, 10]
def baseStart_287891 : Nat := 118140960795 + 287891 * 2 ^ 59
def prefixEnd_287891 : Nat := 4983230072969 + 3 ^ 40 * 287891 * 2
def baseEnd_287891 : Nat := 5475054040875494771797

theorem tailTrace_287891 : CollatzResearch.WordTrace tailWord_287891 prefixEnd_287891 5475054040875494771797 := by
  unfold tailWord_287891
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500247400027549713455527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7000164933351699808970351 10500247400027549713455527)
  ·
    refine ⟨15750371100041324570183291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10500247400027549713455527 15750371100041324570183291)
    ·
      refine ⟨23625556650061986855274937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15750371100041324570183291 23625556650061986855274937)
      ·
        refine ⟨17719167487546490141456203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23625556650061986855274937 17719167487546490141456203)
        ·
          refine ⟨26578751231319735212184305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17719167487546490141456203 26578751231319735212184305)
          ·
            refine ⟨19934063423489801409138229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26578751231319735212184305 19934063423489801409138229)
            ·
              refine ⟨1868818445952168882106709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19934063423489801409138229 1868818445952168882106709)
              ·
                refine ⟨5475054040875494771797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1868818445952168882106709 5475054040875494771797)
                ·
                  rfl

theorem cell23_287891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 10].length) (baseStart_287891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287891 prefixEnd_287891 := by exact prefixLift 287891
  have htrace : WordTrace (prefixWord ++ tailWord_287891) baseStart_287891 baseEnd_287891 := by
    simpa [prefixWord, tailWord_287891, baseEnd_287891] using wordTrace_append hprefix tailTrace_287891
  have hstable : (prefixWord ++ tailWord_287891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287891).length < 2 ^ (prefixWord ++ tailWord_287891).sum := by decide
  have hdescent : baseEnd_287891 < baseStart_287891 := by decide
  rcases family_descends (prefixWord ++ tailWord_287891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287902 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_287902 : Nat := 118140960795 + 287902 * 2 ^ 59
def prefixEnd_287902 : Nat := 4983230072969 + 3 ^ 40 * 287902 * 2
def baseEnd_287902 : Nat := 147832107390837815800969

theorem tailTrace_287902 : CollatzResearch.WordTrace tailWord_287902 prefixEnd_287902 147832107390837815800969 := by
  unfold tailWord_287902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312581075373462324013245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7000432401991799061403973 1312581075373462324013245)
  ·
    refine ⟨492217903265048371504967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1312581075373462324013245 492217903265048371504967)
    ·
      refine ⟨738326854897572557257451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492217903265048371504967 738326854897572557257451)
      ·
        refine ⟨1107490282346358835886177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738326854897572557257451 1107490282346358835886177)
        ·
          refine ⟨830617711759769126914633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1107490282346358835886177 830617711759769126914633)
          ·
            refine ⟨622963283819826845185975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830617711759769126914633 622963283819826845185975)
            ·
              refine ⟨934444925729740267778963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622963283819826845185975 934444925729740267778963)
              ·
                refine ⟨1401667388594610401668445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934444925729740267778963 1401667388594610401668445)
                ·
                  refine ⟨525625270722978900625667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1401667388594610401668445 525625270722978900625667)
                  ·
                    refine ⟨788437906084468350938501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 525625270722978900625667 788437906084468350938501)
                    ·
                      refine ⟨147832107390837815800969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 788437906084468350938501 147832107390837815800969)
                      ·
                        rfl

theorem cell23_287902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_287902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287902 prefixEnd_287902 := by exact prefixLift 287902
  have htrace : WordTrace (prefixWord ++ tailWord_287902) baseStart_287902 baseEnd_287902 := by
    simpa [prefixWord, tailWord_287902, baseEnd_287902] using wordTrace_append hprefix tailTrace_287902
  have hstable : (prefixWord ++ tailWord_287902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287902).length < 2 ^ (prefixWord ++ tailWord_287902).sum := by decide
  have hdescent : baseEnd_287902 < baseStart_287902 := by decide
  rcases family_descends (prefixWord ++ tailWord_287902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287905 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_287905 : Nat := 118140960795 + 287905 * 2 ^ 59
def prefixEnd_287905 : Nat := 4983230072969 + 3 ^ 40 * 287905 * 2
def baseEnd_287905 : Nat := 147833647832801304063455

theorem tailTrace_287905 : CollatzResearch.WordTrace tailWord_287905 prefixEnd_287905 147833647832801304063455 := by
  unfold tailWord_287905
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500758021976830104465169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7000505347984553402976779 10500758021976830104465169)
  ·
    refine ⟨7875568516482622578348877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10500758021976830104465169 7875568516482622578348877)
    ·
      refine ⟨2953338193680983466880829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7875568516482622578348877 2953338193680983466880829)
      ·
        refine ⟨1107501822630368800080311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2953338193680983466880829 1107501822630368800080311)
        ·
          refine ⟨1661252733945553200120467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107501822630368800080311 1661252733945553200120467)
          ·
            refine ⟨2491879100918329800180701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661252733945553200120467 2491879100918329800180701)
            ·
              refine ⟨934454662844373675067763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2491879100918329800180701 934454662844373675067763)
              ·
                refine ⟨1401681994266560512601645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934454662844373675067763 1401681994266560512601645)
                ·
                  refine ⟨525630747849960192225617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1401681994266560512601645 525630747849960192225617)
                  ·
                    refine ⟨394223060887470144169213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 525630747849960192225617 394223060887470144169213)
                    ·
                      refine ⟨147833647832801304063455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 394223060887470144169213 147833647832801304063455)
                      ·
                        rfl

theorem cell23_287905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_287905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287905 prefixEnd_287905 := by exact prefixLift 287905
  have htrace : WordTrace (prefixWord ++ tailWord_287905) baseStart_287905 baseEnd_287905 := by
    simpa [prefixWord, tailWord_287905, baseEnd_287905] using wordTrace_append hprefix tailTrace_287905
  have hstable : (prefixWord ++ tailWord_287905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287905).length < 2 ^ (prefixWord ++ tailWord_287905).sum := by decide
  have hdescent : baseEnd_287905 < baseStart_287905 := by decide
  rcases family_descends (prefixWord ++ tailWord_287905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287908 : List Nat := [2, 3, 1, 2, 3, 1, 2, 9]
def baseStart_287908 : Nat := 118140960795 + 287908 * 2 ^ 59
def prefixEnd_287908 : Nat := 4983230072969 + 3 ^ 40 * 287908 * 2
def baseEnd_287908 : Nat := 5475377343509807123183

theorem tailTrace_287908 : CollatzResearch.WordTrace tailWord_287908 prefixEnd_287908 5475377343509807123183 := by
  unfold tailWord_287908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250433720482980808412189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7000578293977307744549585 5250433720482980808412189)
  ·
    refine ⟨1968912645181117803154571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5250433720482980808412189 1968912645181117803154571)
    ·
      refine ⟨2953368967771676704731857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1968912645181117803154571 2953368967771676704731857)
      ·
        refine ⟨2215026725828757528548893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2953368967771676704731857 2215026725828757528548893)
        ·
          refine ⟨830635022185784073205835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2215026725828757528548893 830635022185784073205835)
          ·
            refine ⟨1245952533278676109808753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830635022185784073205835 1245952533278676109808753)
            ·
              refine ⟨934464399959007082356565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245952533278676109808753 934464399959007082356565)
              ·
                refine ⟨5475377343509807123183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 934464399959007082356565 5475377343509807123183)
                ·
                  rfl

theorem cell23_287908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 9].length) (baseStart_287908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287908 prefixEnd_287908 := by exact prefixLift 287908
  have htrace : WordTrace (prefixWord ++ tailWord_287908) baseStart_287908 baseEnd_287908 := by
    simpa [prefixWord, tailWord_287908, baseEnd_287908] using wordTrace_append hprefix tailTrace_287908
  have hstable : (prefixWord ++ tailWord_287908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287908).length < 2 ^ (prefixWord ++ tailWord_287908).sum := by decide
  have hdescent : baseEnd_287908 < baseStart_287908 := by decide
  rcases family_descends (prefixWord ++ tailWord_287908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287935 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 3]
def baseStart_287935 : Nat := 118140960795 + 287935 * 2 ^ 59
def prefixEnd_287935 : Nat := 4983230072969 + 3 ^ 40 * 287935 * 2
def baseEnd_287935 : Nat := 147849052252436186688317

theorem tailTrace_287935 : CollatzResearch.WordTrace tailWord_287935 prefixEnd_287935 147849052252436186688317 := by
  unfold tailWord_287935
  simp only [CollatzResearch.WordTrace]
  refine ⟨10501852211868145228057259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7001234807912096818704839 10501852211868145228057259)
  ·
    refine ⟨15752778317802217842085889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10501852211868145228057259 15752778317802217842085889)
    ·
      refine ⟨11814583738351663381564417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15752778317802217842085889 11814583738351663381564417)
      ·
        refine ⟨8860937803763747536173313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11814583738351663381564417 8860937803763747536173313)
        ·
          refine ⟨6645703352822810652129985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8860937803763747536173313 6645703352822810652129985)
          ·
            refine ⟨4984277514617107989097489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6645703352822810652129985 4984277514617107989097489)
            ·
              refine ⟨3738208135962830991823117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4984277514617107989097489 3738208135962830991823117)
              ·
                refine ⟨1401828050986061621933669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3738208135962830991823117 1401828050986061621933669)
                ·
                  refine ⟨262842759559886554112563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401828050986061621933669 262842759559886554112563)
                  ·
                    refine ⟨394264139339829831168845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262842759559886554112563 394264139339829831168845)
                    ·
                      refine ⟨147849052252436186688317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 394264139339829831168845 147849052252436186688317)
                      ·
                        rfl

theorem cell23_287935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_287935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287935 prefixEnd_287935 := by exact prefixLift 287935
  have htrace : WordTrace (prefixWord ++ tailWord_287935) baseStart_287935 baseEnd_287935 := by
    simpa [prefixWord, tailWord_287935, baseEnd_287935] using wordTrace_append hprefix tailTrace_287935
  have hstable : (prefixWord ++ tailWord_287935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287935).length < 2 ^ (prefixWord ++ tailWord_287935).sum := by decide
  have hdescent : baseEnd_287935 < baseStart_287935 := by decide
  rcases family_descends (prefixWord ++ tailWord_287935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287936 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 1, 2, 2]
def baseStart_287936 : Nat := 118140960795 + 287936 * 2 ^ 59
def prefixEnd_287936 : Nat := 4983230072969 + 3 ^ 40 * 287936 * 2
def baseEnd_287936 : Nat := 147849565733090682775813

theorem tailTrace_287936 : CollatzResearch.WordTrace tailWord_287936 prefixEnd_287936 147849565733090682775813 := by
  unfold tailWord_287936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250944342432261199421831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7001259123243014932562441 5250944342432261199421831)
  ·
    refine ⟨7876416513648391799132747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5250944342432261199421831 7876416513648391799132747)
    ·
      refine ⟨11814624770472587698699121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7876416513648391799132747 11814624770472587698699121)
      ·
        refine ⟨8860968577854440774024341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11814624770472587698699121 8860968577854440774024341)
        ·
          refine ⟨415357902086926911282391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8860968577854440774024341 415357902086926911282391)
          ·
            refine ⟨623036853130390366923587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415357902086926911282391 623036853130390366923587)
            ·
              refine ⟨934555279695585550385381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623036853130390366923587 934555279695585550385381)
              ·
                refine ⟨175229114942922290697259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 934555279695585550385381 175229114942922290697259)
                ·
                  refine ⟨262843672414383436045889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175229114942922290697259 262843672414383436045889)
                  ·
                    refine ⟨197132754310787577034417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262843672414383436045889 197132754310787577034417)
                    ·
                      refine ⟨147849565733090682775813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197132754310787577034417 147849565733090682775813)
                      ·
                        rfl

theorem cell23_287936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_287936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287936 prefixEnd_287936 := by exact prefixLift 287936
  have htrace : WordTrace (prefixWord ++ tailWord_287936) baseStart_287936 baseEnd_287936 := by
    simpa [prefixWord, tailWord_287936, baseEnd_287936] using wordTrace_append hprefix tailTrace_287936
  have hstable : (prefixWord ++ tailWord_287936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287936).length < 2 ^ (prefixWord ++ tailWord_287936).sum := by decide
  have hdescent : baseEnd_287936 < baseStart_287936 := by decide
  rcases family_descends (prefixWord ++ tailWord_287936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287962 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2]
def baseStart_287962 : Nat := 118140960795 + 287962 * 2 ^ 59
def prefixEnd_287962 : Nat := 4983230072969 + 3 ^ 40 * 287962 * 2
def baseEnd_287962 : Nat := 147862916230107581050693

theorem tailTrace_287962 : CollatzResearch.WordTrace tailWord_287962 prefixEnd_287962 147862916230107581050693 := by
  unfold tailWord_287962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625709245692582209822535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7001891321846885892860093 2625709245692582209822535)
  ·
    refine ⟨3938563868538873314733803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2625709245692582209822535 3938563868538873314733803)
    ·
      refine ⟨5907845802808309972100705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3938563868538873314733803 5907845802808309972100705)
      ·
        refine ⟨4430884352106232479075529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5907845802808309972100705 4430884352106232479075529)
        ·
          refine ⟨3323163264079674359306647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4430884352106232479075529 3323163264079674359306647)
          ·
            refine ⟨4984744896119511538959971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323163264079674359306647 4984744896119511538959971)
            ·
              refine ⟨7477117344179267308439957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984744896119511538959971 7477117344179267308439957)
              ·
                refine ⟨350489875508403155083123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7477117344179267308439957 350489875508403155083123)
                ·
                  refine ⟨525734813262604732624685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350489875508403155083123 525734813262604732624685)
                  ·
                    refine ⟨197150554973476774734257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525734813262604732624685 197150554973476774734257)
                    ·
                      refine ⟨147862916230107581050693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197150554973476774734257 147862916230107581050693)
                      ·
                        rfl

theorem cell23_287962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_287962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287962 prefixEnd_287962 := by exact prefixLift 287962
  have htrace : WordTrace (prefixWord ++ tailWord_287962) baseStart_287962 baseEnd_287962 := by
    simpa [prefixWord, tailWord_287962, baseEnd_287962] using wordTrace_append hprefix tailTrace_287962
  have hstable : (prefixWord ++ tailWord_287962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287962).length < 2 ^ (prefixWord ++ tailWord_287962).sum := by decide
  have hdescent : baseEnd_287962 < baseStart_287962 := by decide
  rcases family_descends (prefixWord ++ tailWord_287962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287979 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 1, 3, 2]
def baseStart_287979 : Nat := 118140960795 + 287979 * 2 ^ 59
def prefixEnd_287979 : Nat := 4983230072969 + 3 ^ 40 * 287979 * 2
def baseEnd_287979 : Nat := 147871645401234014538115

theorem tailTrace_287979 : CollatzResearch.WordTrace tailWord_287979 prefixEnd_287979 147871645401234014538115 := by
  unfold tailWord_287979
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503457023708740742658991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7002304682472493828439327 10503457023708740742658991)
  ·
    refine ⟨15755185535563111113988487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10503457023708740742658991 15755185535563111113988487)
    ·
      refine ⟨23632778303344666670982731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15755185535563111113988487 23632778303344666670982731)
      ·
        refine ⟨35449167455017000006474097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23632778303344666670982731 35449167455017000006474097)
        ·
          refine ⟨26586875591262750004855573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35449167455017000006474097 26586875591262750004855573)
          ·
            refine ⟨1246259793340441406477605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26586875591262750004855573 1246259793340441406477605)
            ·
              refine ⟨233673711251332763714551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1246259793340441406477605 233673711251332763714551)
              ·
                refine ⟨350510566876999145571827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233673711251332763714551 350510566876999145571827)
                ·
                  refine ⟨525765850315498718357741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350510566876999145571827 525765850315498718357741)
                  ·
                    refine ⟨197162193868312019384153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525765850315498718357741 197162193868312019384153)
                    ·
                      refine ⟨147871645401234014538115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197162193868312019384153 147871645401234014538115)
                      ·
                        rfl

theorem cell23_287979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 3, 2].length) (baseStart_287979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287979 prefixEnd_287979 := by exact prefixLift 287979
  have htrace : WordTrace (prefixWord ++ tailWord_287979) baseStart_287979 baseEnd_287979 := by
    simpa [prefixWord, tailWord_287979, baseEnd_287979] using wordTrace_append hprefix tailTrace_287979
  have hstable : (prefixWord ++ tailWord_287979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287979).length < 2 ^ (prefixWord ++ tailWord_287979).sum := by decide
  have hdescent : baseEnd_287979 < baseStart_287979 := by decide
  rcases family_descends (prefixWord ++ tailWord_287979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287986 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_287986 : Nat := 118140960795 + 287986 * 2 ^ 59
def prefixEnd_287986 : Nat := 4983230072969 + 3 ^ 40 * 287986 * 2
def baseEnd_287986 : Nat := 147875239765815487150583

theorem tailTrace_287986 : CollatzResearch.WordTrace tailWord_287986 prefixEnd_287986 147875239765815487150583 := by
  unfold tailWord_287986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625928083670845234540953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7002474889788920625442541 2625928083670845234540953)
  ·
    refine ⟨1969446062753133925905715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2625928083670845234540953 1969446062753133925905715)
    ·
      refine ⟨2954169094129700888858573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1969446062753133925905715 2954169094129700888858573)
      ·
        refine ⟨1107813410298637833321965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2954169094129700888858573 1107813410298637833321965)
        ·
          refine ⟨415430028861989187495737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1107813410298637833321965 415430028861989187495737)
          ·
            refine ⟨311572521646491890621803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415430028861989187495737 311572521646491890621803)
            ·
              refine ⟨467358782469737835932705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311572521646491890621803 467358782469737835932705)
              ·
                refine ⟨350519086852303376949529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467358782469737835932705 350519086852303376949529)
                ·
                  refine ⟨262889315139227532712147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350519086852303376949529 262889315139227532712147)
                  ·
                    refine ⟨394333972708841299068221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262889315139227532712147 394333972708841299068221)
                    ·
                      refine ⟨147875239765815487150583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 394333972708841299068221 147875239765815487150583)
                      ·
                        rfl

theorem cell23_287986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_287986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_287986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_287986 prefixEnd_287986 := by exact prefixLift 287986
  have htrace : WordTrace (prefixWord ++ tailWord_287986) baseStart_287986 baseEnd_287986 := by
    simpa [prefixWord, tailWord_287986, baseEnd_287986] using wordTrace_append hprefix tailTrace_287986
  have hstable : (prefixWord ++ tailWord_287986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287986).length < 2 ^ (prefixWord ++ tailWord_287986).sum := by decide
  have hdescent : baseEnd_287986 < baseStart_287986 := by decide
  rcases family_descends (prefixWord ++ tailWord_287986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288049 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 5]
def baseStart_288049 : Nat := 118140960795 + 288049 * 2 ^ 59
def prefixEnd_288049 : Nat := 4983230072969 + 3 ^ 40 * 288049 * 2
def baseEnd_288049 : Nat := 16434176560783193406977

theorem tailTrace_288049 : CollatzResearch.WordTrace tailWord_288049 prefixEnd_288049 16434176560783193406977 := by
  unfold tailWord_288049
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506010133455142697707201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7004006755636761798471467 10506010133455142697707201)
  ·
    refine ⟨7879507600091357023280401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10506010133455142697707201 7879507600091357023280401)
    ·
      refine ⟨5909630700068517767460301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7879507600091357023280401 5909630700068517767460301)
      ·
        refine ⟨2216111512525694162797613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5909630700068517767460301 2216111512525694162797613)
        ·
          refine ⟨831041817197135311049105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2216111512525694162797613 831041817197135311049105)
          ·
            refine ⟨623281362897851483286829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831041817197135311049105 623281362897851483286829)
            ·
              refine ⟨233730511086694306232561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623281362897851483286829 233730511086694306232561)
              ·
                refine ⟨175297883315020729674421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233730511086694306232561 175297883315020729674421)
                ·
                  refine ⟨16434176560783193406977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175297883315020729674421 16434176560783193406977)
                  ·
                    rfl

theorem cell23_288049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 5].length) (baseStart_288049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288049 prefixEnd_288049 := by exact prefixLift 288049
  have htrace : WordTrace (prefixWord ++ tailWord_288049) baseStart_288049 baseEnd_288049 := by
    simpa [prefixWord, tailWord_288049, baseEnd_288049] using wordTrace_append hprefix tailTrace_288049
  have hstable : (prefixWord ++ tailWord_288049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288049).length < 2 ^ (prefixWord ++ tailWord_288049).sum := by decide
  have hdescent : baseEnd_288049 < baseStart_288049 := by decide
  rcases family_descends (prefixWord ++ tailWord_288049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288082 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_288082 : Nat := 118140960795 + 288082 * 2 ^ 59
def prefixEnd_288082 : Nat := 4983230072969 + 3 ^ 40 * 288082 * 2
def baseEnd_288082 : Nat := 147924533908647111550141

theorem tailTrace_288082 : CollatzResearch.WordTrace tailWord_288082 prefixEnd_288082 147924533908647111550141 := by
  unfold tailWord_288082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626803435583897333414625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7004809161557059555772333 2626803435583897333414625)
  ·
    refine ⟨1970102576687923000060969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2626803435583897333414625 1970102576687923000060969)
    ·
      refine ⟨1477576932515942250045727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1970102576687923000060969 1477576932515942250045727)
      ·
        refine ⟨2216365398773913375068591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477576932515942250045727 2216365398773913375068591)
        ·
          refine ⟨3324548098160870062602887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216365398773913375068591 3324548098160870062602887)
          ·
            refine ⟨4986822147241305093904331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324548098160870062602887 4986822147241305093904331)
            ·
              refine ⟨7480233220861957640856497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986822147241305093904331 7480233220861957640856497)
              ·
                refine ⟨5610174915646468230642373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7480233220861957640856497 5610174915646468230642373)
                ·
                  refine ⟨1051907796683712793245445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5610174915646468230642373 1051907796683712793245445)
                  ·
                    refine ⟨197232711878196148733521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1051907796683712793245445 197232711878196148733521)
                    ·
                      refine ⟨147924533908647111550141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197232711878196148733521 147924533908647111550141)
                      ·
                        rfl

theorem cell23_288082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_288082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288082 prefixEnd_288082 := by exact prefixLift 288082
  have htrace : WordTrace (prefixWord ++ tailWord_288082) baseStart_288082 baseEnd_288082 := by
    simpa [prefixWord, tailWord_288082, baseEnd_288082] using wordTrace_append hprefix tailTrace_288082
  have hstable : (prefixWord ++ tailWord_288082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288082).length < 2 ^ (prefixWord ++ tailWord_288082).sum := by decide
  have hdescent : baseEnd_288082 < baseStart_288082 := by decide
  rcases family_descends (prefixWord ++ tailWord_288082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288156 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 6]
def baseStart_288156 : Nat := 118140960795 + 288156 * 2 ^ 59
def prefixEnd_288156 : Nat := 4983230072969 + 3 ^ 40 * 288156 * 2
def baseEnd_288156 : Nat := 16440281275231091336089

theorem tailTrace_288156 : CollatzResearch.WordTrace tailWord_288156 prefixEnd_288156 16440281275231091336089 := by
  unfold tailWord_288156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254956372033749985926161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7006608496044999981234881 5254956372033749985926161)
  ·
    refine ⟨3941217279025312489444621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254956372033749985926161 3941217279025312489444621)
    ·
      refine ⟨1477956479634492183541733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3941217279025312489444621 1477956479634492183541733)
      ·
        refine ⟨277116839931467284414075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1477956479634492183541733 277116839931467284414075)
        ·
          refine ⟨415675259897200926621113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277116839931467284414075 415675259897200926621113)
          ·
            refine ⟨311756444922900694965835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415675259897200926621113 311756444922900694965835)
            ·
              refine ⟨467634667384351042448753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311756444922900694965835 467634667384351042448753)
              ·
                refine ⟨350726000538263281836565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467634667384351042448753 350726000538263281836565)
                ·
                  refine ⟨16440281275231091336089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 350726000538263281836565 16440281275231091336089)
                  ·
                    rfl

theorem cell23_288156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_288156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288156 prefixEnd_288156 := by exact prefixLift 288156
  have htrace : WordTrace (prefixWord ++ tailWord_288156) baseStart_288156 baseEnd_288156 := by
    simpa [prefixWord, tailWord_288156, baseEnd_288156] using wordTrace_append hprefix tailTrace_288156
  have hstable : (prefixWord ++ tailWord_288156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288156).length < 2 ^ (prefixWord ++ tailWord_288156).sum := by decide
  have hdescent : baseEnd_288156 < baseStart_288156 := by decide
  rcases family_descends (prefixWord ++ tailWord_288156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288189 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_288189 : Nat := 118140960795 + 288189 * 2 ^ 59
def prefixEnd_288189 : Nat := 4983230072969 + 3 ^ 40 * 288189 * 2
def baseEnd_288189 : Nat := 147979476338678192912149

theorem tailTrace_288189 : CollatzResearch.WordTrace tailWord_288189 prefixEnd_288189 147979476338678192912149 := by
  unfold tailWord_288189
  simp only [CollatzResearch.WordTrace]
  refine ⟨10511116352947946607803621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7007410901965297738535747 10511116352947946607803621)
  ·
    refine ⟨1970834316177739988963179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10511116352947946607803621 1970834316177739988963179)
    ·
      refine ⟨2956251474266609983444769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970834316177739988963179 2956251474266609983444769)
      ·
        refine ⟨2217188605699957487583577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2956251474266609983444769 2217188605699957487583577)
        ·
          refine ⟨1662891454274968115687683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2217188605699957487583577 1662891454274968115687683)
          ·
            refine ⟨2494337181412452173531525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662891454274968115687683 2494337181412452173531525)
            ·
              refine ⟨467688221514834782537161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2494337181412452173531525 467688221514834782537161)
              ·
                refine ⟨350766166136126086902871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467688221514834782537161 350766166136126086902871)
                ·
                  refine ⟨526149249204189130354307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350766166136126086902871 526149249204189130354307)
                  ·
                    refine ⟨789223873806283695531461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526149249204189130354307 789223873806283695531461)
                    ·
                      refine ⟨147979476338678192912149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 789223873806283695531461 147979476338678192912149)
                      ·
                        rfl

theorem cell23_288189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_288189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288189 prefixEnd_288189 := by exact prefixLift 288189
  have htrace : WordTrace (prefixWord ++ tailWord_288189) baseStart_288189 baseEnd_288189 := by
    simpa [prefixWord, tailWord_288189, baseEnd_288189] using wordTrace_append hprefix tailTrace_288189
  have hstable : (prefixWord ++ tailWord_288189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288189).length < 2 ^ (prefixWord ++ tailWord_288189).sum := by decide
  have hdescent : baseEnd_288189 < baseStart_288189 := by decide
  rcases family_descends (prefixWord ++ tailWord_288189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288192 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_288192 : Nat := 118140960795 + 288192 * 2 ^ 59
def prefixEnd_288192 : Nat := 4983230072969 + 3 ^ 40 * 288192 * 2
def baseEnd_288192 : Nat := 147981016780641681174635

theorem tailTrace_288192 : CollatzResearch.WordTrace tailWord_288192 prefixEnd_288192 147981016780641681174635 := by
  unfold tailWord_288192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255612885968539060081415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7007483847958052080108553 5255612885968539060081415)
  ·
    refine ⟨7883419328952808590122123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5255612885968539060081415 7883419328952808590122123)
    ·
      refine ⟨11825128993429212885183185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7883419328952808590122123 11825128993429212885183185)
      ·
        refine ⟨8868846745071909663887389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11825128993429212885183185 8868846745071909663887389)
        ·
          refine ⟨3325817529401966123957771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8868846745071909663887389 3325817529401966123957771)
          ·
            refine ⟨4988726294102949185936657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325817529401966123957771 4988726294102949185936657)
            ·
              refine ⟨3741544720577211889452493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4988726294102949185936657 3741544720577211889452493)
              ·
                refine ⟨1403079270216454458544685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3741544720577211889452493 1403079270216454458544685)
                ·
                  refine ⟨526154726331170421954257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1403079270216454458544685 526154726331170421954257)
                  ·
                    refine ⟨394616044748377816465693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 526154726331170421954257 394616044748377816465693)
                    ·
                      refine ⟨147981016780641681174635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 394616044748377816465693 147981016780641681174635)
                      ·
                        rfl

theorem cell23_288192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_288192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288192 prefixEnd_288192 := by exact prefixLift 288192
  have htrace : WordTrace (prefixWord ++ tailWord_288192) baseStart_288192 baseEnd_288192 := by
    simpa [prefixWord, tailWord_288192, baseEnd_288192] using wordTrace_append hprefix tailTrace_288192
  have hstable : (prefixWord ++ tailWord_288192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288192).length < 2 ^ (prefixWord ++ tailWord_288192).sum := by decide
  have hdescent : baseEnd_288192 < baseStart_288192 := by decide
  rcases family_descends (prefixWord ++ tailWord_288192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288194 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_288194 : Nat := 118140960795 + 288194 * 2 ^ 59
def prefixEnd_288194 : Nat := 4983230072969 + 3 ^ 40 * 288194 * 2
def baseEnd_288194 : Nat := 49327347913983557783209

theorem tailTrace_288194 : CollatzResearch.WordTrace tailWord_288194 prefixEnd_288194 49327347913983557783209 := by
  unfold tailWord_288194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627824679482458115433909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7007532478619888307823757 2627824679482458115433909)
  ·
    refine ⟨246358563701480448321929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2627824679482458115433909 246358563701480448321929)
    ·
      refine ⟨184768922776110336241447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246358563701480448321929 184768922776110336241447)
      ·
        refine ⟨277153384164165504362171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184768922776110336241447 277153384164165504362171)
        ·
          refine ⟨415730076246248256543257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277153384164165504362171 415730076246248256543257)
          ·
            refine ⟨311797557184686192407443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415730076246248256543257 311797557184686192407443)
            ·
              refine ⟨467696335777029288611165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311797557184686192407443 467696335777029288611165)
              ·
                refine ⟨175386125916385983229187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 467696335777029288611165 175386125916385983229187)
                ·
                  refine ⟨263079188874578974843781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175386125916385983229187 263079188874578974843781)
                  ·
                    refine ⟨49327347913983557783209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 263079188874578974843781 49327347913983557783209)
                    ·
                      rfl

theorem cell23_288194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_288194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288194 prefixEnd_288194 := by exact prefixLift 288194
  have htrace : WordTrace (prefixWord ++ tailWord_288194) baseStart_288194 baseEnd_288194 := by
    simpa [prefixWord, tailWord_288194, baseEnd_288194] using wordTrace_append hprefix tailTrace_288194
  have hstable : (prefixWord ++ tailWord_288194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288194).length < 2 ^ (prefixWord ++ tailWord_288194).sum := by decide
  have hdescent : baseEnd_288194 < baseStart_288194 := by decide
  rcases family_descends (prefixWord ++ tailWord_288194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288235 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_288235 : Nat := 118140960795 + 288235 * 2 ^ 59
def prefixEnd_288235 : Nat := 4983230072969 + 3 ^ 40 * 288235 * 2
def baseEnd_288235 : Nat := 148003096448785012936937

theorem tailTrace_288235 : CollatzResearch.WordTrace tailWord_288235 prefixEnd_288235 148003096448785012936937 := by
  unfold tailWord_288235
  simp only [CollatzResearch.WordTrace]
  refine ⟨10512794110781296463978159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7008529407187530975985439 10512794110781296463978159)
  ·
    refine ⟨15769191166171944695967239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10512794110781296463978159 15769191166171944695967239)
    ·
      refine ⟨23653786749257917043950859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15769191166171944695967239 23653786749257917043950859)
      ·
        refine ⟨35480680123886875565926289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23653786749257917043950859 35480680123886875565926289)
        ·
          refine ⟨26610510092915156674444717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35480680123886875565926289 26610510092915156674444717)
          ·
            refine ⟨9978941284843183752916769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26610510092915156674444717 9978941284843183752916769)
            ·
              refine ⟨7484205963632387814687577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9978941284843183752916769 7484205963632387814687577)
              ·
                refine ⟨5613154472724290861015683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7484205963632387814687577 5613154472724290861015683)
                ·
                  refine ⟨8419731709086436291523525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613154472724290861015683 8419731709086436291523525)
                  ·
                    refine ⟨1578699695453706804660661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8419731709086436291523525 1578699695453706804660661)
                    ·
                      refine ⟨148003096448785012936937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1578699695453706804660661 148003096448785012936937)
                      ·
                        rfl

theorem cell23_288235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_288235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288235 prefixEnd_288235 := by exact prefixLift 288235
  have htrace : WordTrace (prefixWord ++ tailWord_288235) baseStart_288235 baseEnd_288235 := by
    simpa [prefixWord, tailWord_288235, baseEnd_288235] using wordTrace_append hprefix tailTrace_288235
  have hstable : (prefixWord ++ tailWord_288235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288235).length < 2 ^ (prefixWord ++ tailWord_288235).sum := by decide
  have hdescent : baseEnd_288235 < baseStart_288235 := by decide
  rcases family_descends (prefixWord ++ tailWord_288235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288255 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 8]
def baseStart_288255 : Nat := 118140960795 + 288255 * 2 ^ 59
def prefixEnd_288255 : Nat := 4983230072969 + 3 ^ 40 * 288255 * 2
def baseEnd_288255 : Nat := 49337788687291644895615

theorem tailTrace_288255 : CollatzResearch.WordTrace tailWord_288255 prefixEnd_288255 49337788687291644895615 := by
  unfold tailWord_288255
  simp only [CollatzResearch.WordTrace]
  refine ⟨10513523570708839879706219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7009015713805893253137479 10513523570708839879706219)
  ·
    refine ⟨15770285356063259819559329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10513523570708839879706219 15770285356063259819559329)
    ·
      refine ⟨11827714017047444864669497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15770285356063259819559329 11827714017047444864669497)
      ·
        refine ⟨8870785512785583648502123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11827714017047444864669497 8870785512785583648502123)
        ·
          refine ⟨13306178269178375472753185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8870785512785583648502123 13306178269178375472753185)
          ·
            refine ⟨9979633701883781604564889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13306178269178375472753185 9979633701883781604564889)
            ·
              refine ⟨7484725276412836203423667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9979633701883781604564889 7484725276412836203423667)
              ·
                refine ⟨11227087914619254305135501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484725276412836203423667 11227087914619254305135501)
                ·
                  refine ⟨4210157967982220364425813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11227087914619254305135501 4210157967982220364425813)
                  ·
                    refine ⟨49337788687291644895615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4210157967982220364425813 49337788687291644895615)
                    ·
                      rfl

theorem cell23_288255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_288255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288255 prefixEnd_288255 := by exact prefixLift 288255
  have htrace : WordTrace (prefixWord ++ tailWord_288255) baseStart_288255 baseEnd_288255 := by
    simpa [prefixWord, tailWord_288255, baseEnd_288255] using wordTrace_append hprefix tailTrace_288255
  have hstable : (prefixWord ++ tailWord_288255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288255).length < 2 ^ (prefixWord ++ tailWord_288255).sum := by decide
  have hdescent : baseEnd_288255 < baseStart_288255 := by decide
  rcases family_descends (prefixWord ++ tailWord_288255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288317 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_288317 : Nat := 118140960795 + 288317 * 2 ^ 59
def prefixEnd_288317 : Nat := 4983230072969 + 3 ^ 40 * 288317 * 2
def baseEnd_288317 : Nat := 148045201862453692111561

theorem tailTrace_288317 : CollatzResearch.WordTrace tailWord_288317 prefixEnd_288317 148045201862453692111561 := by
  unfold tailWord_288317
  simp only [CollatzResearch.WordTrace]
  refine ⟨10515784896484224468463205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7010523264322816312308803 10515784896484224468463205)
  ·
    refine ⟨1971709668090792087836851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10515784896484224468463205 1971709668090792087836851)
    ·
      refine ⟨2957564502136188131755277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971709668090792087836851 2957564502136188131755277)
      ·
        refine ⟨1109086688301070549408229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2957564502136188131755277 1109086688301070549408229)
        ·
          refine ⟨207953754056450728014043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1109086688301070549408229 207953754056450728014043)
          ·
            refine ⟨311930631084676092021065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207953754056450728014043 311930631084676092021065)
            ·
              refine ⟨233947973313507069015799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311930631084676092021065 233947973313507069015799)
              ·
                refine ⟨350921959970260603523699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233947973313507069015799 350921959970260603523699)
                ·
                  refine ⟨526382939955390905285549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350921959970260603523699 526382939955390905285549)
                  ·
                    refine ⟨197393602483271589482081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526382939955390905285549 197393602483271589482081)
                    ·
                      refine ⟨148045201862453692111561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197393602483271589482081 148045201862453692111561)
                      ·
                        rfl

theorem cell23_288317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_288317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288317 prefixEnd_288317 := by exact prefixLift 288317
  have htrace : WordTrace (prefixWord ++ tailWord_288317) baseStart_288317 baseEnd_288317 := by
    simpa [prefixWord, tailWord_288317, baseEnd_288317] using wordTrace_append hprefix tailTrace_288317
  have hstable : (prefixWord ++ tailWord_288317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288317).length < 2 ^ (prefixWord ++ tailWord_288317).sum := by decide
  have hdescent : baseEnd_288317 < baseStart_288317 := by decide
  rcases family_descends (prefixWord ++ tailWord_288317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288319 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 5]
def baseStart_288319 : Nat := 118140960795 + 288319 * 2 ^ 59
def prefixEnd_288319 : Nat := 4983230072969 + 3 ^ 40 * 288319 * 2
def baseEnd_288319 : Nat := 16449580980418076031839

theorem tailTrace_288319 : CollatzResearch.WordTrace tailWord_288319 prefixEnd_288319 16449580980418076031839 := by
  unfold tailWord_288319
  simp only [CollatzResearch.WordTrace]
  refine ⟨10515857842476978810036011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7010571894984652540024007 10515857842476978810036011)
  ·
    refine ⟨15773786763715468215054017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10515857842476978810036011 15773786763715468215054017)
    ·
      refine ⟨11830340072786601161290513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15773786763715468215054017 11830340072786601161290513)
      ·
        refine ⟨8872755054589950870967885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11830340072786601161290513 8872755054589950870967885)
        ·
          refine ⟨3327283145471231576612957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8872755054589950870967885 3327283145471231576612957)
          ·
            refine ⟨1247731179551711841229859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3327283145471231576612957 1247731179551711841229859)
            ·
              refine ⟨1871596769327567761844789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247731179551711841229859 1871596769327567761844789)
              ·
                refine ⟨175462197124459477672949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1871596769327567761844789 175462197124459477672949)
                ·
                  refine ⟨16449580980418076031839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175462197124459477672949 16449580980418076031839)
                  ·
                    rfl

theorem cell23_288319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 5].length) (baseStart_288319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288319 prefixEnd_288319 := by exact prefixLift 288319
  have htrace : WordTrace (prefixWord ++ tailWord_288319) baseStart_288319 baseEnd_288319 := by
    simpa [prefixWord, tailWord_288319, baseEnd_288319] using wordTrace_append hprefix tailTrace_288319
  have hstable : (prefixWord ++ tailWord_288319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288319).length < 2 ^ (prefixWord ++ tailWord_288319).sum := by decide
  have hdescent : baseEnd_288319 < baseStart_288319 := by decide
  rcases family_descends (prefixWord ++ tailWord_288319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288369 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 6, 2]
def baseStart_288369 : Nat := 118140960795 + 288369 * 2 ^ 59
def prefixEnd_288369 : Nat := 4983230072969 + 3 ^ 40 * 288369 * 2
def baseEnd_288369 : Nat := 148071902856487488661321

theorem tailTrace_288369 : CollatzResearch.WordTrace tailWord_288369 prefixEnd_288369 148071902856487488661321 := by
  unfold tailWord_288369
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517681492295837349356161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7011787661530558232904107 10517681492295837349356161)
  ·
    refine ⟨7888261119221878012017121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10517681492295837349356161 7888261119221878012017121)
    ·
      refine ⟨5916195839416408509012841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7888261119221878012017121 5916195839416408509012841)
      ·
        refine ⟨4437146879562306381759631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5916195839416408509012841 4437146879562306381759631)
        ·
          refine ⟨6655720319343459572639447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4437146879562306381759631 6655720319343459572639447)
          ·
            refine ⟨9983580479015189358959171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655720319343459572639447 9983580479015189358959171)
            ·
              refine ⟨14975370718522784038438757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9983580479015189358959171 14975370718522784038438757)
              ·
                refine ⟨2807882009723022007207267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14975370718522784038438757 2807882009723022007207267)
                ·
                  refine ⟨4211823014584533010810901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807882009723022007207267 4211823014584533010810901)
                  ·
                    refine ⟨197429203808649984881761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4211823014584533010810901 197429203808649984881761)
                    ·
                      refine ⟨148071902856487488661321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197429203808649984881761 148071902856487488661321)
                      ·
                        rfl

theorem cell23_288369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_288369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288369 prefixEnd_288369 := by exact prefixLift 288369
  have htrace : WordTrace (prefixWord ++ tailWord_288369) baseStart_288369 baseEnd_288369 := by
    simpa [prefixWord, tailWord_288369, baseEnd_288369] using wordTrace_append hprefix tailTrace_288369
  have hstable : (prefixWord ++ tailWord_288369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288369).length < 2 ^ (prefixWord ++ tailWord_288369).sum := by decide
  have hdescent : baseEnd_288369 < baseStart_288369 := by decide
  rcases family_descends (prefixWord ++ tailWord_288369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288453 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 1, 1, 3]
def baseStart_288453 : Nat := 118140960795 + 288453 * 2 ^ 59
def prefixEnd_288453 : Nat := 4983230072969 + 3 ^ 40 * 288453 * 2
def baseEnd_288453 : Nat := 148115035231465160010935

theorem tailTrace_288453 : CollatzResearch.WordTrace tailWord_288453 prefixEnd_288453 148115035231465160010935 := by
  unfold tailWord_288453
  simp only [CollatzResearch.WordTrace]
  refine ⟨10520745223991519695414013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7013830149327679796942675 10520745223991519695414013)
  ·
    refine ⟨3945279458996819885780255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10520745223991519695414013 3945279458996819885780255)
    ·
      refine ⟨5917919188495229828670383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945279458996819885780255 5917919188495229828670383)
      ·
        refine ⟨8876878782742844743005575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5917919188495229828670383 8876878782742844743005575)
        ·
          refine ⟨13315318174114267114508363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876878782742844743005575 13315318174114267114508363)
          ·
            refine ⟨19972977261171400671762545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13315318174114267114508363 19972977261171400671762545)
            ·
              refine ⟨14979732945878550503821909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19972977261171400671762545 14979732945878550503821909)
              ·
                refine ⟨175543745459514263716663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 14979732945878550503821909 175543745459514263716663)
                ·
                  refine ⟨263315618189271395574995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175543745459514263716663 263315618189271395574995)
                  ·
                    refine ⟨394973427283907093362493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 263315618189271395574995 394973427283907093362493)
                    ·
                      refine ⟨148115035231465160010935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 394973427283907093362493 148115035231465160010935)
                      ·
                        rfl

theorem cell23_288453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_288453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288453 prefixEnd_288453 := by exact prefixLift 288453
  have htrace : WordTrace (prefixWord ++ tailWord_288453) baseStart_288453 baseEnd_288453 := by
    simpa [prefixWord, tailWord_288453, baseEnd_288453] using wordTrace_append hprefix tailTrace_288453
  have hstable : (prefixWord ++ tailWord_288453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288453).length < 2 ^ (prefixWord ++ tailWord_288453).sum := by decide
  have hdescent : baseEnd_288453 < baseStart_288453 := by decide
  rcases family_descends (prefixWord ++ tailWord_288453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288493 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_288493 : Nat := 118140960795 + 288493 * 2 ^ 59
def prefixEnd_288493 : Nat := 4983230072969 + 3 ^ 40 * 288493 * 2
def baseEnd_288493 : Nat := 148135574457645003510751

theorem tailTrace_288493 : CollatzResearch.WordTrace tailWord_288493 prefixEnd_288493 148135574457645003510751 := by
  unfold tailWord_288493
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522204143846606526870133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7014802762564404351246755 10522204143846606526870133)
  ·
    refine ⟨986456638485619361894075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10522204143846606526870133 986456638485619361894075)
    ·
      refine ⟨1479684957728429042841113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986456638485619361894075 1479684957728429042841113)
      ·
        refine ⟨1109763718296321782130835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479684957728429042841113 1109763718296321782130835)
        ·
          refine ⟨1664645577444482673196253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109763718296321782130835 1664645577444482673196253)
          ·
            refine ⟨624242091541681002448595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1664645577444482673196253 624242091541681002448595)
            ·
              refine ⟨936363137312521503672893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624242091541681002448595 936363137312521503672893)
              ·
                refine ⟨351136176492195563877335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 936363137312521503672893 351136176492195563877335)
                ·
                  refine ⟨526704264738293345816003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351136176492195563877335 526704264738293345816003)
                  ·
                    refine ⟨790056397107440018724005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526704264738293345816003 790056397107440018724005)
                    ·
                      refine ⟨148135574457645003510751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 790056397107440018724005 148135574457645003510751)
                      ·
                        rfl

theorem cell23_288493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_288493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288493 prefixEnd_288493 := by exact prefixLift 288493
  have htrace : WordTrace (prefixWord ++ tailWord_288493) baseStart_288493 baseEnd_288493 := by
    simpa [prefixWord, tailWord_288493, baseEnd_288493] using wordTrace_append hprefix tailTrace_288493
  have hstable : (prefixWord ++ tailWord_288493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288493).length < 2 ^ (prefixWord ++ tailWord_288493).sum := by decide
  have hdescent : baseEnd_288493 < baseStart_288493 := by decide
  rcases family_descends (prefixWord ++ tailWord_288493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288530 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_288530 : Nat := 118140960795 + 288530 * 2 ^ 59
def prefixEnd_288530 : Nat := 4983230072969 + 3 ^ 40 * 288530 * 2
def baseEnd_288530 : Nat := 148154573241861358748081

theorem tailTrace_288530 : CollatzResearch.WordTrace tailWord_288530 prefixEnd_288530 148154573241861358748081 := by
  unfold tailWord_288530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2630888411178140461491761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7015702429808374563978029 2630888411178140461491761)
  ·
    refine ⟨1973166308383605346118821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2630888411178140461491761 1973166308383605346118821)
    ·
      refine ⟨369968682821926002397279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1973166308383605346118821 369968682821926002397279)
      ·
        refine ⟨554953024232889003595919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369968682821926002397279 554953024232889003595919)
        ·
          refine ⟨832429536349333505393879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554953024232889003595919 832429536349333505393879)
          ·
            refine ⟨1248644304524000258090819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832429536349333505393879 1248644304524000258090819)
            ·
              refine ⟨1872966456786000387136229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248644304524000258090819 1872966456786000387136229)
              ·
                refine ⟨351181210647375072588043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1872966456786000387136229 351181210647375072588043)
                ·
                  refine ⟨526771815971062608882065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351181210647375072588043 526771815971062608882065)
                  ·
                    refine ⟨395078861978296956661549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 526771815971062608882065 395078861978296956661549)
                    ·
                      refine ⟨148154573241861358748081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 395078861978296956661549 148154573241861358748081)
                      ·
                        rfl

theorem cell23_288530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_288530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288530 prefixEnd_288530 := by exact prefixLift 288530
  have htrace : WordTrace (prefixWord ++ tailWord_288530) baseStart_288530 baseEnd_288530 := by
    simpa [prefixWord, tailWord_288530, baseEnd_288530] using wordTrace_append hprefix tailTrace_288530
  have hstable : (prefixWord ++ tailWord_288530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288530).length < 2 ^ (prefixWord ++ tailWord_288530).sum := by decide
  have hdescent : baseEnd_288530 < baseStart_288530 := by decide
  rcases family_descends (prefixWord ++ tailWord_288530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288604 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_288604 : Nat := 118140960795 + 288604 * 2 ^ 59
def prefixEnd_288604 : Nat := 4983230072969 + 3 ^ 40 * 288604 * 2
def baseEnd_288604 : Nat := 148192570810294069222741

theorem tailTrace_288604 : CollatzResearch.WordTrace tailWord_288604 prefixEnd_288604 148192570810294069222741 := by
  unfold tailWord_288604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5263126323222236242080433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7017501764296314989440577 5263126323222236242080433)
  ·
    refine ⟨3947344742416677181560325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5263126323222236242080433 3947344742416677181560325)
    ·
      refine ⟨740127139203126971542561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3947344742416677181560325 740127139203126971542561)
      ·
        refine ⟨555095354402345228656921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 740127139203126971542561 555095354402345228656921)
        ·
          refine ⟨416321515801758921492691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555095354402345228656921 416321515801758921492691)
          ·
            refine ⟨624482273702638382239037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416321515801758921492691 624482273702638382239037)
            ·
              refine ⟨234180852638489393339639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624482273702638382239037 234180852638489393339639)
              ·
                refine ⟨351271278957734090009459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234180852638489393339639 351271278957734090009459)
                ·
                  refine ⟨526906918436601135014189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351271278957734090009459 526906918436601135014189)
                  ·
                    refine ⟨197590094413725425630321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526906918436601135014189 197590094413725425630321)
                    ·
                      refine ⟨148192570810294069222741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197590094413725425630321 148192570810294069222741)
                      ·
                        rfl

theorem cell23_288604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_288604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288604 prefixEnd_288604 := by exact prefixLift 288604
  have htrace : WordTrace (prefixWord ++ tailWord_288604) baseStart_288604 baseEnd_288604 := by
    simpa [prefixWord, tailWord_288604, baseEnd_288604] using wordTrace_append hprefix tailTrace_288604
  have hstable : (prefixWord ++ tailWord_288604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288604).length < 2 ^ (prefixWord ++ tailWord_288604).sum := by decide
  have hdescent : baseEnd_288604 < baseStart_288604 := by decide
  rcases family_descends (prefixWord ++ tailWord_288604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288619 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 3, 7]
def baseStart_288619 : Nat := 118140960795 + 288619 * 2 ^ 59
def prefixEnd_288619 : Nat := 4983230072969 + 3 ^ 40 * 288619 * 2
def baseEnd_288619 : Nat := 49400091006703836845057

theorem tailTrace_288619 : CollatzResearch.WordTrace tailWord_288619 prefixEnd_288619 49400091006703836845057 := by
  unfold tailWord_288619
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526799741390130045956911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7017866494260086697304607 10526799741390130045956911)
  ·
    refine ⟨15790199612085195068935367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10526799741390130045956911 15790199612085195068935367)
    ·
      refine ⟨23685299418127792603403051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15790199612085195068935367 23685299418127792603403051)
      ·
        refine ⟨35527949127191688905104577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23685299418127792603403051 35527949127191688905104577)
        ·
          refine ⟨26645961845393766678828433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35527949127191688905104577 26645961845393766678828433)
          ·
            refine ⟨19984471384045325009121325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26645961845393766678828433 19984471384045325009121325)
            ·
              refine ⟨7494176769016996878420497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19984471384045325009121325 7494176769016996878420497)
              ·
                refine ⟨5620632576762747658815373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7494176769016996878420497 5620632576762747658815373)
                ·
                  refine ⟨2107737216286030372055765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5620632576762747658815373 2107737216286030372055765)
                  ·
                    refine ⟨49400091006703836845057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2107737216286030372055765 49400091006703836845057)
                    ·
                      rfl

theorem cell23_288619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_288619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288619 prefixEnd_288619 := by exact prefixLift 288619
  have htrace : WordTrace (prefixWord ++ tailWord_288619) baseStart_288619 baseEnd_288619 := by
    simpa [prefixWord, tailWord_288619, baseEnd_288619] using wordTrace_append hprefix tailTrace_288619
  have hstable : (prefixWord ++ tailWord_288619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288619).length < 2 ^ (prefixWord ++ tailWord_288619).sum := by decide
  have hdescent : baseEnd_288619 < baseStart_288619 := by decide
  rcases family_descends (prefixWord ++ tailWord_288619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288630 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_288630 : Nat := 118140960795 + 288630 * 2 ^ 59
def prefixEnd_288630 : Nat := 4983230072969 + 3 ^ 40 * 288630 * 2
def baseEnd_288630 : Nat := 148205921307310967497621

theorem tailTrace_288630 : CollatzResearch.WordTrace tailWord_288630 prefixEnd_288630 148205921307310967497621 := by
  unfold tailWord_288630
  simp only [CollatzResearch.WordTrace]
  refine ⟨657950059021892432787959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7018133962900185949738229 657950059021892432787959)
  ·
    refine ⟨986925088532838649181939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657950059021892432787959 986925088532838649181939)
    ·
      refine ⟨1480387632799257973772909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986925088532838649181939 1480387632799257973772909)
      ·
        refine ⟨555145362299721740164841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1480387632799257973772909 555145362299721740164841)
        ·
          refine ⟨416359021724791305123631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555145362299721740164841 416359021724791305123631)
          ·
            refine ⟨624538532587186957685447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416359021724791305123631 624538532587186957685447)
            ·
              refine ⟨936807798880780436528171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624538532587186957685447 936807798880780436528171)
              ·
                refine ⟨1405211698321170654792257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936807798880780436528171 1405211698321170654792257)
                ·
                  refine ⟨1053908773740877991094193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1405211698321170654792257 1053908773740877991094193)
                  ·
                    refine ⟨790431580305658493320645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1053908773740877991094193 790431580305658493320645)
                    ·
                      refine ⟨148205921307310967497621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 790431580305658493320645 148205921307310967497621)
                      ·
                        rfl

theorem cell23_288630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_288630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288630 prefixEnd_288630 := by exact prefixLift 288630
  have htrace : WordTrace (prefixWord ++ tailWord_288630) baseStart_288630 baseEnd_288630 := by
    simpa [prefixWord, tailWord_288630, baseEnd_288630] using wordTrace_append hprefix tailTrace_288630
  have hstable : (prefixWord ++ tailWord_288630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288630).length < 2 ^ (prefixWord ++ tailWord_288630).sum := by decide
  have hdescent : baseEnd_288630 < baseStart_288630 := by decide
  rcases family_descends (prefixWord ++ tailWord_288630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288693 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_288693 : Nat := 118140960795 + 288693 * 2 ^ 59
def prefixEnd_288693 : Nat := 4983230072969 + 3 ^ 40 * 288693 * 2
def baseEnd_288693 : Nat := 148238270588544221009831

theorem tailTrace_288693 : CollatzResearch.WordTrace tailWord_288693 prefixEnd_288693 148238270588544221009831 := by
  unfold tailWord_288693
  simp only [CollatzResearch.WordTrace]
  refine ⟨10529498743122040684150733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7019665828748027122767155 10529498743122040684150733)
  ·
    refine ⟨3948562028670765256556525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10529498743122040684150733 3948562028670765256556525)
    ·
      refine ⟨1480710760751536971208697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3948562028670765256556525 1480710760751536971208697)
      ·
        refine ⟨1110533070563652728406523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1480710760751536971208697 1110533070563652728406523)
        ·
          refine ⟨1665799605845479092609785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110533070563652728406523 1665799605845479092609785)
          ·
            refine ⟨1249349704384109319457339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1665799605845479092609785 1249349704384109319457339)
            ·
              refine ⟨1874024556576163979186009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249349704384109319457339 1874024556576163979186009)
              ·
                refine ⟨1405518417432122984389507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874024556576163979186009 1405518417432122984389507)
                ·
                  refine ⟨2108277626148184476584261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405518417432122984389507 2108277626148184476584261)
                  ·
                    refine ⟨395302054902784589359549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108277626148184476584261 395302054902784589359549)
                    ·
                      refine ⟨148238270588544221009831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 395302054902784589359549 148238270588544221009831)
                      ·
                        rfl

theorem cell23_288693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_288693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288693 prefixEnd_288693 := by exact prefixLift 288693
  have htrace : WordTrace (prefixWord ++ tailWord_288693) baseStart_288693 baseEnd_288693 := by
    simpa [prefixWord, tailWord_288693, baseEnd_288693] using wordTrace_append hprefix tailTrace_288693
  have hstable : (prefixWord ++ tailWord_288693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288693).length < 2 ^ (prefixWord ++ tailWord_288693).sum := by decide
  have hdescent : baseEnd_288693 < baseStart_288693 := by decide
  rcases family_descends (prefixWord ++ tailWord_288693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288763 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 6, 2]
def baseStart_288763 : Nat := 118140960795 + 288763 * 2 ^ 59
def prefixEnd_288763 : Nat := 4983230072969 + 3 ^ 40 * 288763 * 2
def baseEnd_288763 : Nat := 148274214234358947134509

theorem tailTrace_288763 : CollatzResearch.WordTrace tailWord_288763 prefixEnd_288763 148274214234358947134509 := by
  unfold tailWord_288763
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532051852868442639198943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7021367901912295092799295 10532051852868442639198943)
  ·
    refine ⟨15798077779302663958798415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10532051852868442639198943 15798077779302663958798415)
    ·
      refine ⟨23697116668953995938197623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15798077779302663958798415 23697116668953995938197623)
      ·
        refine ⟨35545675003430993907296435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23697116668953995938197623 35545675003430993907296435)
        ·
          refine ⟨53318512505146490860944653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35545675003430993907296435 53318512505146490860944653)
          ·
            refine ⟨19994442189429934072854245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53318512505146490860944653 19994442189429934072854245)
            ·
              refine ⟨3748957910518112638660171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19994442189429934072854245 3748957910518112638660171)
              ·
                refine ⟨5623436865777168957990257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3748957910518112638660171 5623436865777168957990257)
                ·
                  refine ⟨4217577649332876718492693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5623436865777168957990257 4217577649332876718492693)
                  ·
                    refine ⟨197698952312478596179345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4217577649332876718492693 197698952312478596179345)
                    ·
                      refine ⟨148274214234358947134509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197698952312478596179345 148274214234358947134509)
                      ·
                        rfl

theorem cell23_288763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6, 2].length) (baseStart_288763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288763 prefixEnd_288763 := by exact prefixLift 288763
  have htrace : WordTrace (prefixWord ++ tailWord_288763) baseStart_288763 baseEnd_288763 := by
    simpa [prefixWord, tailWord_288763, baseEnd_288763] using wordTrace_append hprefix tailTrace_288763
  have hstable : (prefixWord ++ tailWord_288763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288763).length < 2 ^ (prefixWord ++ tailWord_288763).sum := by decide
  have hdescent : baseEnd_288763 < baseStart_288763 := by decide
  rcases family_descends (prefixWord ++ tailWord_288763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288773 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_288773 : Nat := 118140960795 + 288773 * 2 ^ 59
def prefixEnd_288773 : Nat := 4983230072969 + 3 ^ 40 * 288773 * 2
def baseEnd_288773 : Nat := 49426449680301302669821

theorem tailTrace_288773 : CollatzResearch.WordTrace tailWord_288773 prefixEnd_288773 49426449680301302669821 := by
  unfold tailWord_288773
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532416582832214347062973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7021611055221476231375315 10532416582832214347062973)
  ·
    refine ⟨3949656218562080380148615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10532416582832214347062973 3949656218562080380148615)
    ·
      refine ⟨5924484327843120570222923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3949656218562080380148615 5924484327843120570222923)
      ·
        refine ⟨8886726491764680855334385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5924484327843120570222923 8886726491764680855334385)
        ·
          refine ⟨6665044868823510641500789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8886726491764680855334385 6665044868823510641500789)
          ·
            refine ⟨624847956452204122640699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6665044868823510641500789 624847956452204122640699)
            ·
              refine ⟨937271934678306183961049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624847956452204122640699 937271934678306183961049)
              ·
                refine ⟨702953951008729637970787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937271934678306183961049 702953951008729637970787)
                ·
                  refine ⟨1054430926513094456956181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702953951008729637970787 1054430926513094456956181)
                  ·
                    refine ⟨49426449680301302669821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1054430926513094456956181 49426449680301302669821)
                    ·
                      rfl

theorem cell23_288773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_288773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288773 prefixEnd_288773 := by exact prefixLift 288773
  have htrace : WordTrace (prefixWord ++ tailWord_288773) baseStart_288773 baseEnd_288773 := by
    simpa [prefixWord, tailWord_288773, baseEnd_288773] using wordTrace_append hprefix tailTrace_288773
  have hstable : (prefixWord ++ tailWord_288773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288773).length < 2 ^ (prefixWord ++ tailWord_288773).sum := by decide
  have hdescent : baseEnd_288773 < baseStart_288773 := by decide
  rcases family_descends (prefixWord ++ tailWord_288773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288807 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 1, 6]
def baseStart_288807 : Nat := 118140960795 + 288807 * 2 ^ 59
def prefixEnd_288807 : Nat := 4983230072969 + 3 ^ 40 * 288807 * 2
def baseEnd_288807 : Nat := 49432269127718924994769

theorem tailTrace_288807 : CollatzResearch.WordTrace tailWord_288807 prefixEnd_288807 49432269127718924994769 := by
  unfold tailWord_288807
  simp only [CollatzResearch.WordTrace]
  refine ⟨10533656664709038153800675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7022437776472692102533783 10533656664709038153800675)
  ·
    refine ⟨15800484997063557230701013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10533656664709038153800675 15800484997063557230701013)
    ·
      refine ⟨370323867118677122594555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15800484997063557230701013 370323867118677122594555)
      ·
        refine ⟨555485800678015683891833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370323867118677122594555 555485800678015683891833)
        ·
          refine ⟨416614350508511762918875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555485800678015683891833 416614350508511762918875)
          ·
            refine ⟨624921525762767644378313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416614350508511762918875 624921525762767644378313)
            ·
              refine ⟨468691144322075733283735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624921525762767644378313 468691144322075733283735)
              ·
                refine ⟨703036716483113599925603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468691144322075733283735 703036716483113599925603)
                ·
                  refine ⟨1054555074724670399888405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703036716483113599925603 1054555074724670399888405)
                  ·
                    refine ⟨49432269127718924994769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1054555074724670399888405 49432269127718924994769)
                    ·
                      rfl

theorem cell23_288807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_288807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288807 prefixEnd_288807 := by exact prefixLift 288807
  have htrace : WordTrace (prefixWord ++ tailWord_288807) baseStart_288807 baseEnd_288807 := by
    simpa [prefixWord, tailWord_288807, baseEnd_288807] using wordTrace_append hprefix tailTrace_288807
  have hstable : (prefixWord ++ tailWord_288807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288807).length < 2 ^ (prefixWord ++ tailWord_288807).sum := by decide
  have hdescent : baseEnd_288807 < baseStart_288807 := by decide
  rcases family_descends (prefixWord ++ tailWord_288807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288810 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_288810 : Nat := 118140960795 + 288810 * 2 ^ 59
def prefixEnd_288810 : Nat := 4983230072969 + 3 ^ 40 * 288810 * 2
def baseEnd_288810 : Nat := 148298347825120263246793

theorem tailTrace_288810 : CollatzResearch.WordTrace tailWord_288810 prefixEnd_288810 148298347825120263246793 := by
  unfold tailWord_288810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633441520924542416539971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7022510722465446444106589 2633441520924542416539971)
  ·
    refine ⟨3950162281386813624809957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2633441520924542416539971 3950162281386813624809957)
    ·
      refine ⟨740655427760027554651867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3950162281386813624809957 740655427760027554651867)
      ·
        refine ⟨1110983141640041331977801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740655427760027554651867 1110983141640041331977801)
        ·
          refine ⟨833237356230030998983351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110983141640041331977801 833237356230030998983351)
          ·
            refine ⟨1249856034345046498475027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833237356230030998983351 1249856034345046498475027)
            ·
              refine ⟨1874784051517569747712541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249856034345046498475027 1874784051517569747712541)
              ·
                refine ⟨703044019319088655392203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1874784051517569747712541 703044019319088655392203)
                ·
                  refine ⟨1054566028978632983088305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703044019319088655392203 1054566028978632983088305)
                  ·
                    refine ⟨790924521733974737316229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054566028978632983088305 790924521733974737316229)
                    ·
                      refine ⟨148298347825120263246793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 790924521733974737316229 148298347825120263246793)
                      ·
                        rfl

theorem cell23_288810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_288810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288810 prefixEnd_288810 := by exact prefixLift 288810
  have htrace : WordTrace (prefixWord ++ tailWord_288810) baseStart_288810 baseEnd_288810 := by
    simpa [prefixWord, tailWord_288810, baseEnd_288810] using wordTrace_append hprefix tailTrace_288810
  have hstable : (prefixWord ++ tailWord_288810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288810).length < 2 ^ (prefixWord ++ tailWord_288810).sum := by decide
  have hdescent : baseEnd_288810 < baseStart_288810 := by decide
  rcases family_descends (prefixWord ++ tailWord_288810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288814 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_288814 : Nat := 118140960795 + 288814 * 2 ^ 59
def prefixEnd_288814 : Nat := 4983230072969 + 3 ^ 40 * 288814 * 2
def baseEnd_288814 : Nat := 148300401747738247596775

theorem tailTrace_288814 : CollatzResearch.WordTrace tailWord_288814 prefixEnd_288814 148300401747738247596775 := by
  unfold tailWord_288814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316738996960459793663187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7022607983789118899536997 1316738996960459793663187)
  ·
    refine ⟨1975108495440689690494781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316738996960459793663187 1975108495440689690494781)
    ·
      refine ⟨740665685790258633935543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1975108495440689690494781 740665685790258633935543)
      ·
        refine ⟨1110998528685387950903315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740665685790258633935543 1110998528685387950903315)
        ·
          refine ⟨1666497793028081926354973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110998528685387950903315 1666497793028081926354973)
          ·
            refine ⟨624936672385530722383115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1666497793028081926354973 624936672385530722383115)
            ·
              refine ⟨937405008578296083574673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624936672385530722383115 937405008578296083574673)
              ·
                refine ⟨703053756433722062681005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937405008578296083574673 703053756433722062681005)
                ·
                  refine ⟨263645158662645773505377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703053756433722062681005 263645158662645773505377)
                  ·
                    refine ⟨197733868996984330129033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 263645158662645773505377 197733868996984330129033)
                    ·
                      refine ⟨148300401747738247596775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197733868996984330129033 148300401747738247596775)
                      ·
                        rfl

theorem cell23_288814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_288814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288814 prefixEnd_288814 := by exact prefixLift 288814
  have htrace : WordTrace (prefixWord ++ tailWord_288814) baseStart_288814 baseEnd_288814 := by
    simpa [prefixWord, tailWord_288814, baseEnd_288814] using wordTrace_append hprefix tailTrace_288814
  have hstable : (prefixWord ++ tailWord_288814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288814).length < 2 ^ (prefixWord ++ tailWord_288814).sum := by decide
  have hdescent : baseEnd_288814 < baseStart_288814 := by decide
  rcases family_descends (prefixWord ++ tailWord_288814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288840 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_288840 : Nat := 118140960795 + 288840 * 2 ^ 59
def prefixEnd_288840 : Nat := 4983230072969 + 3 ^ 40 * 288840 * 2
def baseEnd_288840 : Nat := 148313752244755145871655

theorem tailTrace_288840 : CollatzResearch.WordTrace tailWord_288840 prefixEnd_288840 148313752244755145871655 := by
  unfold tailWord_288840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267430136794742394875987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7023240182392989859834649 5267430136794742394875987)
  ·
    refine ⟨7901145205192113592313981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5267430136794742394875987 7901145205192113592313981)
    ·
      refine ⟨2962929451947042597117743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7901145205192113592313981 2962929451947042597117743)
      ·
        refine ⟨4444394177920563895676615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962929451947042597117743 4444394177920563895676615)
        ·
          refine ⟨6666591266880845843514923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444394177920563895676615 6666591266880845843514923)
          ·
            refine ⟨9999886900321268765272385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6666591266880845843514923 9999886900321268765272385)
            ·
              refine ⟨7499915175240951573954289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9999886900321268765272385 7499915175240951573954289)
              ·
                refine ⟨5624936381430713680465717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7499915175240951573954289 5624936381430713680465717)
                ·
                  refine ⟨527337785759129407543661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5624936381430713680465717 527337785759129407543661)
                  ·
                    refine ⟨197751669659673527828873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527337785759129407543661 197751669659673527828873)
                    ·
                      refine ⟨148313752244755145871655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197751669659673527828873 148313752244755145871655)
                      ·
                        rfl

theorem cell23_288840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_288840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288840 prefixEnd_288840 := by exact prefixLift 288840
  have htrace : WordTrace (prefixWord ++ tailWord_288840) baseStart_288840 baseEnd_288840 := by
    simpa [prefixWord, tailWord_288840, baseEnd_288840] using wordTrace_append hprefix tailTrace_288840
  have hstable : (prefixWord ++ tailWord_288840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288840).length < 2 ^ (prefixWord ++ tailWord_288840).sum := by decide
  have hdescent : baseEnd_288840 < baseStart_288840 := by decide
  rcases family_descends (prefixWord ++ tailWord_288840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288864 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 2, 1, 3]
def baseStart_288864 : Nat := 118140960795 + 288864 * 2 ^ 59
def prefixEnd_288864 : Nat := 4983230072969 + 3 ^ 40 * 288864 * 2
def baseEnd_288864 : Nat := 148326075780463051971545

theorem tailTrace_288864 : CollatzResearch.WordTrace tailWord_288864 prefixEnd_288864 148326075780463051971545 := by
  unfold tailWord_288864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267867812751268444312823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7023823750335024592417097 5267867812751268444312823)
  ·
    refine ⟨7901801719126902666469235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5267867812751268444312823 7901801719126902666469235)
    ·
      refine ⟨11852702578690353999703853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7901801719126902666469235 11852702578690353999703853)
      ·
        refine ⟨4444763467008882749888945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11852702578690353999703853 4444763467008882749888945)
        ·
          refine ⟨3333572600256662062416709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444763467008882749888945 3333572600256662062416709)
          ·
            refine ⟨625044862548124136703133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3333572600256662062416709 625044862548124136703133)
            ·
              refine ⟨234391823455546551263675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625044862548124136703133 234391823455546551263675)
              ·
                refine ⟨351587735183319826895513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234391823455546551263675 351587735183319826895513)
                ·
                  refine ⟨263690801387489870171635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351587735183319826895513 263690801387489870171635)
                  ·
                    refine ⟨395536202081234805257453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 263690801387489870171635 395536202081234805257453)
                    ·
                      refine ⟨148326075780463051971545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 395536202081234805257453 148326075780463051971545)
                      ·
                        rfl

theorem cell23_288864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_288864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288864 prefixEnd_288864 := by exact prefixLift 288864
  have htrace : WordTrace (prefixWord ++ tailWord_288864) baseStart_288864 baseEnd_288864 := by
    simpa [prefixWord, tailWord_288864, baseEnd_288864] using wordTrace_append hprefix tailTrace_288864
  have hstable : (prefixWord ++ tailWord_288864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288864).length < 2 ^ (prefixWord ++ tailWord_288864).sum := by decide
  have hdescent : baseEnd_288864 < baseStart_288864 := by decide
  rcases family_descends (prefixWord ++ tailWord_288864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288873 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_288873 : Nat := 118140960795 + 288873 * 2 ^ 59
def prefixEnd_288873 : Nat := 4983230072969 + 3 ^ 40 * 288873 * 2
def baseEnd_288873 : Nat := 148330697106353516759003

theorem tailTrace_288873 : CollatzResearch.WordTrace tailWord_288873 prefixEnd_288873 148330697106353516759003 := by
  unfold tailWord_288873
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536063882469931425703273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024042588313287617135515 10536063882469931425703273)
  ·
    refine ⟨7902047911852448569277455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10536063882469931425703273 7902047911852448569277455)
    ·
      refine ⟨11853071867778672853916183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902047911852448569277455 11853071867778672853916183)
      ·
        refine ⟨17779607801668009280874275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853071867778672853916183 17779607801668009280874275)
        ·
          refine ⟨26669411702502013921311413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17779607801668009280874275 26669411702502013921311413)
          ·
            refine ⟨2500257347109563805122945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26669411702502013921311413 2500257347109563805122945)
            ·
              refine ⟨1875193010332172853842209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500257347109563805122945 1875193010332172853842209)
              ·
                refine ⟨1406394757749129640381657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875193010332172853842209 1406394757749129640381657)
                ·
                  refine ⟨1054796068311847230286243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1406394757749129640381657 1054796068311847230286243)
                  ·
                    refine ⟨1582194102467770845429365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054796068311847230286243 1582194102467770845429365)
                    ·
                      refine ⟨148330697106353516759003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1582194102467770845429365 148330697106353516759003)
                      ·
                        rfl

theorem cell23_288873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_288873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288873 prefixEnd_288873 := by exact prefixLift 288873
  have htrace : WordTrace (prefixWord ++ tailWord_288873) baseStart_288873 baseEnd_288873 := by
    simpa [prefixWord, tailWord_288873, baseEnd_288873] using wordTrace_append hprefix tailTrace_288873
  have hstable : (prefixWord ++ tailWord_288873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288873).length < 2 ^ (prefixWord ++ tailWord_288873).sum := by decide
  have hdescent : baseEnd_288873 < baseStart_288873 := by decide
  rcases family_descends (prefixWord ++ tailWord_288873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288887 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 4, 2, 2]
def baseStart_288887 : Nat := 118140960795 + 288887 * 2 ^ 59
def prefixEnd_288887 : Nat := 4983230072969 + 3 ^ 40 * 288887 * 2
def baseEnd_288887 : Nat := 148337885835516461983939

theorem tailTrace_288887 : CollatzResearch.WordTrace tailWord_288887 prefixEnd_288887 148337885835516461983939 := by
  unfold tailWord_288887
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536574504419211816712915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024383002946141211141943 10536574504419211816712915)
  ·
    refine ⟨15804861756628817725069373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10536574504419211816712915 15804861756628817725069373)
    ·
      refine ⟨5926823158735806646901015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15804861756628817725069373 5926823158735806646901015)
      ·
        refine ⟨8890234738103709970351523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926823158735806646901015 8890234738103709970351523)
        ·
          refine ⟨13335352107155564955527285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890234738103709970351523 13335352107155564955527285)
          ·
            refine ⟨1250189260045834214580683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13335352107155564955527285 1250189260045834214580683)
            ·
              refine ⟨1875283890068751321871025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250189260045834214580683 1875283890068751321871025)
              ·
                refine ⟨1406462917551563491403269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875283890068751321871025 1406462917551563491403269)
                ·
                  refine ⟨263711797040918154638113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406462917551563491403269 263711797040918154638113)
                  ·
                    refine ⟨197783847780688615978585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 263711797040918154638113 197783847780688615978585)
                    ·
                      refine ⟨148337885835516461983939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197783847780688615978585 148337885835516461983939)
                      ·
                        rfl

theorem cell23_288887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_288887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288887 prefixEnd_288887 := by exact prefixLift 288887
  have htrace : WordTrace (prefixWord ++ tailWord_288887) baseStart_288887 baseEnd_288887 := by
    simpa [prefixWord, tailWord_288887, baseEnd_288887] using wordTrace_append hprefix tailTrace_288887
  have hstable : (prefixWord ++ tailWord_288887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288887).length < 2 ^ (prefixWord ++ tailWord_288887).sum := by decide
  have hdescent : baseEnd_288887 < baseStart_288887 := by decide
  rcases family_descends (prefixWord ++ tailWord_288887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288904 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_288904 : Nat := 118140960795 + 288904 * 2 ^ 59
def prefixEnd_288904 : Nat := 4983230072969 + 3 ^ 40 * 288904 * 2
def baseEnd_288904 : Nat := 148346615006642895471361

theorem tailTrace_288904 : CollatzResearch.WordTrace tailWord_288904 prefixEnd_288904 148346615006642895471361 := by
  unfold tailWord_288904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268597272678811860040883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7024796363571749146721177 5268597272678811860040883)
  ·
    refine ⟨7902895909018217790061325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5268597272678811860040883 7902895909018217790061325)
    ·
      refine ⟨2963585965881831671272997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7902895909018217790061325 2963585965881831671272997)
      ·
        refine ⟨555672368602843438363687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2963585965881831671272997 555672368602843438363687)
        ·
          refine ⟨833508552904265157545531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555672368602843438363687 833508552904265157545531)
          ·
            refine ⟨1250262829356397736318297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833508552904265157545531 1250262829356397736318297)
            ·
              refine ⟨937697122017298302238723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250262829356397736318297 937697122017298302238723)
              ·
                refine ⟨1406545683025947453358085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937697122017298302238723 1406545683025947453358085)
                ·
                  refine ⟨263727315567365147504641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406545683025947453358085 263727315567365147504641)
                  ·
                    refine ⟨197795486675523860628481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 263727315567365147504641 197795486675523860628481)
                    ·
                      refine ⟨148346615006642895471361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197795486675523860628481 148346615006642895471361)
                      ·
                        rfl

theorem cell23_288904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_288904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288904 prefixEnd_288904 := by exact prefixLift 288904
  have htrace : WordTrace (prefixWord ++ tailWord_288904) baseStart_288904 baseEnd_288904 := by
    simpa [prefixWord, tailWord_288904, baseEnd_288904] using wordTrace_append hprefix tailTrace_288904
  have hstable : (prefixWord ++ tailWord_288904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288904).length < 2 ^ (prefixWord ++ tailWord_288904).sum := by decide
  have hdescent : baseEnd_288904 < baseStart_288904 := by decide
  rcases family_descends (prefixWord ++ tailWord_288904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288923 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 4, 5]
def baseStart_288923 : Nat := 118140960795 + 288923 * 2 ^ 59
def prefixEnd_288923 : Nat := 4983230072969 + 3 ^ 40 * 288923 * 2
def baseEnd_288923 : Nat := 49452123713026107044591

theorem tailTrace_288923 : CollatzResearch.WordTrace tailWord_288923 prefixEnd_288923 49452123713026107044591 := by
  unfold tailWord_288923
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537887532288789965023423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7025258354859193310015615 10537887532288789965023423)
  ·
    refine ⟨15806831298433184947535135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10537887532288789965023423 15806831298433184947535135)
    ·
      refine ⟨23710246947649777421302703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15806831298433184947535135 23710246947649777421302703)
      ·
        refine ⟨35565370421474666131954055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23710246947649777421302703 35565370421474666131954055)
        ·
          refine ⟨53348055632211999197931083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35565370421474666131954055 53348055632211999197931083)
          ·
            refine ⟨80022083448317998796896625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53348055632211999197931083 80022083448317998796896625)
            ·
              refine ⟨60016562586238499097672469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80022083448317998796896625 60016562586238499097672469)
              ·
                refine ⟨2813276371229929645203397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60016562586238499097672469 2813276371229929645203397)
                ·
                  refine ⟨527489319605611808475637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2813276371229929645203397 527489319605611808475637)
                  ·
                    refine ⟨49452123713026107044591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 527489319605611808475637 49452123713026107044591)
                    ·
                      rfl

theorem cell23_288923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 5].length) (baseStart_288923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288923 prefixEnd_288923 := by exact prefixLift 288923
  have htrace : WordTrace (prefixWord ++ tailWord_288923) baseStart_288923 baseEnd_288923 := by
    simpa [prefixWord, tailWord_288923, baseEnd_288923] using wordTrace_append hprefix tailTrace_288923
  have hstable : (prefixWord ++ tailWord_288923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288923).length < 2 ^ (prefixWord ++ tailWord_288923).sum := by decide
  have hdescent : baseEnd_288923 < baseStart_288923 := by decide
  rcases family_descends (prefixWord ++ tailWord_288923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288933 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_288933 : Nat := 118140960795 + 288933 * 2 ^ 59
def prefixEnd_288933 : Nat := 4983230072969 + 3 ^ 40 * 288933 * 2
def baseEnd_288933 : Nat := 148361505945623282008727

theorem tailTrace_288933 : CollatzResearch.WordTrace tailWord_288933 prefixEnd_288933 148361505945623282008727 := by
  unfold tailWord_288933
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538252262252561672887453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7025501508168374448591635 10538252262252561672887453)
  ·
    refine ⟨3951844598344710627332795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10538252262252561672887453 3951844598344710627332795)
    ·
      refine ⟨5927766897517065940999193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3951844598344710627332795 5927766897517065940999193)
      ·
        refine ⟨4445825173137799455749395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5927766897517065940999193 4445825173137799455749395)
        ·
          refine ⟨6668737759706699183624093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445825173137799455749395 6668737759706699183624093)
          ·
            refine ⟨2500776659890012193859035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6668737759706699183624093 2500776659890012193859035)
            ·
              refine ⟨3751164989835018290788553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500776659890012193859035 3751164989835018290788553)
              ·
                refine ⟨2813373742376263718091415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3751164989835018290788553 2813373742376263718091415)
                ·
                  refine ⟨4220060613564395577137123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813373742376263718091415 4220060613564395577137123)
                  ·
                    refine ⟨6330090920346593365705685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4220060613564395577137123 6330090920346593365705685)
                    ·
                      refine ⟨148361505945623282008727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6330090920346593365705685 148361505945623282008727)
                      ·
                        rfl

theorem cell23_288933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_288933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288933 prefixEnd_288933 := by exact prefixLift 288933
  have htrace : WordTrace (prefixWord ++ tailWord_288933) baseStart_288933 baseEnd_288933 := by
    simpa [prefixWord, tailWord_288933, baseEnd_288933] using wordTrace_append hprefix tailTrace_288933
  have hstable : (prefixWord ++ tailWord_288933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288933).length < 2 ^ (prefixWord ++ tailWord_288933).sum := by decide
  have hdescent : baseEnd_288933 < baseStart_288933 := by decide
  rcases family_descends (prefixWord ++ tailWord_288933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288983 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 10]
def baseStart_288983 : Nat := 118140960795 + 288983 * 2 ^ 59
def prefixEnd_288983 : Nat := 4983230072969 + 3 ^ 40 * 288983 * 2
def baseEnd_288983 : Nat := 16487464442038676264833

theorem tailTrace_288983 : CollatzResearch.WordTrace tailWord_288983 prefixEnd_288983 16487464442038676264833 := by
  unfold tailWord_288983
  simp only [CollatzResearch.WordTrace]
  refine ⟨10540075912071420212207603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7026717274714280141471735 10540075912071420212207603)
  ·
    refine ⟨15810113868107130318311405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10540075912071420212207603 15810113868107130318311405)
    ·
      refine ⟨5928792700540173869366777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15810113868107130318311405 5928792700540173869366777)
      ·
        refine ⟨4446594525405130402025083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5928792700540173869366777 4446594525405130402025083)
        ·
          refine ⟨6669891788107695603037625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446594525405130402025083 6669891788107695603037625)
          ·
            refine ⟨5002418841080771702278219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6669891788107695603037625 5002418841080771702278219)
            ·
              refine ⟨7503628261621157553417329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002418841080771702278219 7503628261621157553417329)
              ·
                refine ⟨5627721196215868165062997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7503628261621157553417329 5627721196215868165062997)
                ·
                  refine ⟨16487464442038676264833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5627721196215868165062997 16487464442038676264833)
                  ·
                    rfl

theorem cell23_288983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 10].length) (baseStart_288983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288983 prefixEnd_288983 := by exact prefixLift 288983
  have htrace : WordTrace (prefixWord ++ tailWord_288983) baseStart_288983 baseEnd_288983 := by
    simpa [prefixWord, tailWord_288983, baseEnd_288983] using wordTrace_append hprefix tailTrace_288983
  have hstable : (prefixWord ++ tailWord_288983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288983).length < 2 ^ (prefixWord ++ tailWord_288983).sum := by decide
  have hdescent : baseEnd_288983 < baseStart_288983 := by decide
  rcases family_descends (prefixWord ++ tailWord_288983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288997 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_288997 : Nat := 118140960795 + 288997 * 2 ^ 59
def prefixEnd_288997 : Nat := 4983230072969 + 3 ^ 40 * 288997 * 2
def baseEnd_288997 : Nat := 148394368707511031608433

theorem tailTrace_288997 : CollatzResearch.WordTrace tailWord_288997 prefixEnd_288997 148394368707511031608433 := by
  unfold tailWord_288997
  simp only [CollatzResearch.WordTrace]
  refine ⟨10540586534020700603217245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7027057689347133735478163 10540586534020700603217245)
  ·
    refine ⟨3952719950257762726206467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10540586534020700603217245 3952719950257762726206467)
    ·
      refine ⟨5929079925386644089309701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3952719950257762726206467 5929079925386644089309701)
      ·
        refine ⟨1111702486009995766745569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5929079925386644089309701 1111702486009995766745569)
        ·
          refine ⟨833776864507496825059177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111702486009995766745569 833776864507496825059177)
          ·
            refine ⟨625332648380622618794383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833776864507496825059177 625332648380622618794383)
            ·
              refine ⟨937998972570933928191575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625332648380622618794383 937998972570933928191575)
              ·
                refine ⟨1406998458856400892287363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937998972570933928191575 1406998458856400892287363)
                ·
                  refine ⟨2110497688284601338431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406998458856400892287363 2110497688284601338431045)
                  ·
                    refine ⟨395718316553362750955821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2110497688284601338431045 395718316553362750955821)
                    ·
                      refine ⟨148394368707511031608433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 395718316553362750955821 148394368707511031608433)
                      ·
                        rfl

theorem cell23_288997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_288997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_288997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_288997 prefixEnd_288997 := by exact prefixLift 288997
  have htrace : WordTrace (prefixWord ++ tailWord_288997) baseStart_288997 baseEnd_288997 := by
    simpa [prefixWord, tailWord_288997, baseEnd_288997] using wordTrace_append hprefix tailTrace_288997
  have hstable : (prefixWord ++ tailWord_288997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288997).length < 2 ^ (prefixWord ++ tailWord_288997).sum := by decide
  have hdescent : baseEnd_288997 < baseStart_288997 := by decide
  rcases family_descends (prefixWord ++ tailWord_288997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289004 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_289004 : Nat := 118140960795 + 289004 * 2 ^ 59
def prefixEnd_289004 : Nat := 4983230072969 + 3 ^ 40 * 289004 * 2
def baseEnd_289004 : Nat := 49465987690697501406967

theorem tailTrace_289004 : CollatzResearch.WordTrace tailWord_289004 prefixEnd_289004 49465987690697501406967 := by
  unfold tailWord_289004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270420922497670399361033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7027227896663560532481377 5270420922497670399361033)
  ·
    refine ⟨3952815691873252799520775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5270420922497670399361033 3952815691873252799520775)
    ·
      refine ⟨5929223537809879199281163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3952815691873252799520775 5929223537809879199281163)
      ·
        refine ⟨8893835306714818798921745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5929223537809879199281163 8893835306714818798921745)
        ·
          refine ⟨6670376480036114099191309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8893835306714818798921745 6670376480036114099191309)
          ·
            refine ⟨2501391180013542787196741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6670376480036114099191309 2501391180013542787196741)
            ·
              refine ⟨469010846252539272599389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2501391180013542787196741 469010846252539272599389)
              ·
                refine ⟨175879067344702227224771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469010846252539272599389 175879067344702227224771)
                ·
                  refine ⟨263818601017053340837157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175879067344702227224771 263818601017053340837157)
                  ·
                    refine ⟨49465987690697501406967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 263818601017053340837157 49465987690697501406967)
                    ·
                      rfl

theorem cell23_289004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_289004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289004 prefixEnd_289004 := by exact prefixLift 289004
  have htrace : WordTrace (prefixWord ++ tailWord_289004) baseStart_289004 baseEnd_289004 := by
    simpa [prefixWord, tailWord_289004, baseEnd_289004] using wordTrace_append hprefix tailTrace_289004
  have hstable : (prefixWord ++ tailWord_289004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289004).length < 2 ^ (prefixWord ++ tailWord_289004).sum := by decide
  have hdescent : baseEnd_289004 < baseStart_289004 := by decide
  rcases family_descends (prefixWord ++ tailWord_289004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289020 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_289020 : Nat := 118140960795 + 289020 * 2 ^ 59
def prefixEnd_289020 : Nat := 4983230072969 + 3 ^ 40 * 289020 * 2
def baseEnd_289020 : Nat := 148406178762564441620827

theorem tailTrace_289020 : CollatzResearch.WordTrace tailWord_289020 prefixEnd_289020 148406178762564441620827 := by
  unfold tailWord_289020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270712706468687765652257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7027616941958250354203009 5270712706468687765652257)
  ·
    refine ⟨3953034529851515824239193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5270712706468687765652257 3953034529851515824239193)
    ·
      refine ⟨2964775897388636868179395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3953034529851515824239193 2964775897388636868179395)
      ·
        refine ⟨4447163846082955302269093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964775897388636868179395 4447163846082955302269093)
        ·
          refine ⟨833843221140554119175455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4447163846082955302269093 833843221140554119175455)
          ·
            refine ⟨1250764831710831178763183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833843221140554119175455 1250764831710831178763183)
            ·
              refine ⟨1876147247566246768144775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250764831710831178763183 1876147247566246768144775)
              ·
                refine ⟨2814220871349370152217163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876147247566246768144775 2814220871349370152217163)
                ·
                  refine ⟨4221331307024055228325745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814220871349370152217163 4221331307024055228325745)
                  ·
                    refine ⟨3165998480268041421244309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221331307024055228325745 3165998480268041421244309)
                    ·
                      refine ⟨148406178762564441620827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3165998480268041421244309 148406178762564441620827)
                      ·
                        rfl

theorem cell23_289020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_289020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289020 prefixEnd_289020 := by exact prefixLift 289020
  have htrace : WordTrace (prefixWord ++ tailWord_289020) baseStart_289020 baseEnd_289020 := by
    simpa [prefixWord, tailWord_289020, baseEnd_289020] using wordTrace_append hprefix tailTrace_289020
  have hstable : (prefixWord ++ tailWord_289020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289020).length < 2 ^ (prefixWord ++ tailWord_289020).sum := by decide
  have hdescent : baseEnd_289020 < baseStart_289020 := by decide
  rcases family_descends (prefixWord ++ tailWord_289020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289047 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 1, 5]
def baseStart_289047 : Nat := 118140960795 + 289047 * 2 ^ 59
def prefixEnd_289047 : Nat := 4983230072969 + 3 ^ 40 * 289047 * 2
def baseEnd_289047 : Nat := 49473347580078611994401

theorem tailTrace_289047 : CollatzResearch.WordTrace tailWord_289047 prefixEnd_289047 49473347580078611994401 := by
  unfold tailWord_289047
  simp only [CollatzResearch.WordTrace]
  refine ⟨10542410183839559142537395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7028273455893039428358263 10542410183839559142537395)
  ·
    refine ⟨15813615275759338713806093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10542410183839559142537395 15813615275759338713806093)
    ·
      refine ⟨5930105728409752017677285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15813615275759338713806093 5930105728409752017677285)
      ·
        refine ⟨1111894824076828503314491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5930105728409752017677285 1111894824076828503314491)
        ·
          refine ⟨1667842236115242754971737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111894824076828503314491 1667842236115242754971737)
          ·
            refine ⟨1250881677086432066228803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667842236115242754971737 1250881677086432066228803)
            ·
              refine ⟨1876322515629648099343205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250881677086432066228803 1876322515629648099343205)
              ·
                refine ⟨351810471680559018626851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1876322515629648099343205 351810471680559018626851)
                ·
                  refine ⟨527715707520838527940277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351810471680559018626851 527715707520838527940277)
                  ·
                    refine ⟨49473347580078611994401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 527715707520838527940277 49473347580078611994401)
                    ·
                      rfl

theorem cell23_289047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_289047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289047 prefixEnd_289047 := by exact prefixLift 289047
  have htrace : WordTrace (prefixWord ++ tailWord_289047) baseStart_289047 baseEnd_289047 := by
    simpa [prefixWord, tailWord_289047, baseEnd_289047] using wordTrace_append hprefix tailTrace_289047
  have hstable : (prefixWord ++ tailWord_289047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289047).length < 2 ^ (prefixWord ++ tailWord_289047).sum := by decide
  have hdescent : baseEnd_289047 < baseStart_289047 := by decide
  rcases family_descends (prefixWord ++ tailWord_289047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289077 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_289077 : Nat := 118140960795 + 289077 * 2 ^ 59
def prefixEnd_289077 : Nat := 4983230072969 + 3 ^ 40 * 289077 * 2
def baseEnd_289077 : Nat := 49478482386623572869355

theorem tailTrace_289077 : CollatzResearch.WordTrace tailWord_289077 prefixEnd_289077 49478482386623572869355 := by
  unfold tailWord_289077
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543504373730874266129485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7029002915820582844086323 10543504373730874266129485)
  ·
    refine ⟨3953814140149077849798557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10543504373730874266129485 3953814140149077849798557)
    ·
      refine ⟨1482680302555904193674459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3953814140149077849798557 1482680302555904193674459)
      ·
        refine ⟨2224020453833856290511689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482680302555904193674459 2224020453833856290511689)
        ·
          refine ⟨1668015340375392217883767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224020453833856290511689 1668015340375392217883767)
          ·
            refine ⟨2502023010563088326825651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668015340375392217883767 2502023010563088326825651)
            ·
              refine ⟨3753034515844632490238477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502023010563088326825651 3753034515844632490238477)
              ·
                refine ⟨1407387943441737183839429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3753034515844632490238477 1407387943441737183839429)
                ·
                  refine ⟨263885239395325721969893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407387943441737183839429 263885239395325721969893)
                  ·
                    refine ⟨49478482386623572869355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 263885239395325721969893 49478482386623572869355)
                    ·
                      rfl

theorem cell23_289077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_289077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289077 prefixEnd_289077 := by exact prefixLift 289077
  have htrace : WordTrace (prefixWord ++ tailWord_289077) baseStart_289077 baseEnd_289077 := by
    simpa [prefixWord, tailWord_289077, baseEnd_289077] using wordTrace_append hprefix tailTrace_289077
  have hstable : (prefixWord ++ tailWord_289077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289077).length < 2 ^ (prefixWord ++ tailWord_289077).sum := by decide
  have hdescent : baseEnd_289077 < baseStart_289077 := by decide
  rcases family_descends (prefixWord ++ tailWord_289077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289080 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_289080 : Nat := 118140960795 + 289080 * 2 ^ 59
def prefixEnd_289080 : Nat := 4983230072969 + 3 ^ 40 * 289080 * 2
def baseEnd_289080 : Nat := 148436987601834206870551

theorem tailTrace_289080 : CollatzResearch.WordTrace tailWord_289080 prefixEnd_289080 148436987601834206870551 := by
  unfold tailWord_289080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271806896360002889244347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7029075861813337185659129 5271806896360002889244347)
  ·
    refine ⟨7907710344540004333866521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5271806896360002889244347 7907710344540004333866521)
    ·
      refine ⟨5930782758405003250399891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7907710344540004333866521 5930782758405003250399891)
      ·
        refine ⟨8896174137607504875599837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930782758405003250399891 8896174137607504875599837)
        ·
          refine ⟨3336065301602814328349939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8896174137607504875599837 3336065301602814328349939)
          ·
            refine ⟨5004097952404221492524909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336065301602814328349939 5004097952404221492524909)
            ·
              refine ⟨1876536732151583059696841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5004097952404221492524909 1876536732151583059696841)
              ·
                refine ⟨1407402549113687294772631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1876536732151583059696841 1407402549113687294772631)
                ·
                  refine ⟨2111103823670530942158947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407402549113687294772631 2111103823670530942158947)
                  ·
                    refine ⟨3166655735505796413238421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2111103823670530942158947 3166655735505796413238421)
                    ·
                      refine ⟨148436987601834206870551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3166655735505796413238421 148436987601834206870551)
                      ·
                        rfl

theorem cell23_289080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_289080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289080 prefixEnd_289080 := by exact prefixLift 289080
  have htrace : WordTrace (prefixWord ++ tailWord_289080) baseStart_289080 baseEnd_289080 := by
    simpa [prefixWord, tailWord_289080, baseEnd_289080] using wordTrace_append hprefix tailTrace_289080
  have hstable : (prefixWord ++ tailWord_289080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289080).length < 2 ^ (prefixWord ++ tailWord_289080).sum := by decide
  have hdescent : baseEnd_289080 < baseStart_289080 := by decide
  rcases family_descends (prefixWord ++ tailWord_289080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289087 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_289087 : Nat := 118140960795 + 289087 * 2 ^ 59
def prefixEnd_289087 : Nat := 4983230072969 + 3 ^ 40 * 289087 * 2
def baseEnd_289087 : Nat := 148440581966415679483019

theorem tailTrace_289087 : CollatzResearch.WordTrace tailWord_289087 prefixEnd_289087 148440581966415679483019 := by
  unfold tailWord_289087
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543869103694645973993515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7029246069129763982662343 10543869103694645973993515)
  ·
    refine ⟨15815803655541968960990273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10543869103694645973993515 15815803655541968960990273)
    ·
      refine ⟨11861852741656476720742705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15815803655541968960990273 11861852741656476720742705)
      ·
        refine ⟨8896389556242357540557029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11861852741656476720742705 8896389556242357540557029)
        ·
          refine ⟨1668073041795442038854443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8896389556242357540557029 1668073041795442038854443)
          ·
            refine ⟨2502109562693163058281665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668073041795442038854443 2502109562693163058281665)
            ·
              refine ⟨1876582172019872293711249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2502109562693163058281665 1876582172019872293711249)
              ·
                refine ⟨1407436629014904220283437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1876582172019872293711249 1407436629014904220283437)
                ·
                  refine ⟨527788735880589082606289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1407436629014904220283437 527788735880589082606289)
                  ·
                    refine ⟨395841551910441811954717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 527788735880589082606289 395841551910441811954717)
                    ·
                      refine ⟨148440581966415679483019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 395841551910441811954717 148440581966415679483019)
                      ·
                        rfl

theorem cell23_289087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_289087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289087 prefixEnd_289087 := by exact prefixLift 289087
  have htrace : WordTrace (prefixWord ++ tailWord_289087) baseStart_289087 baseEnd_289087 := by
    simpa [prefixWord, tailWord_289087, baseEnd_289087] using wordTrace_append hprefix tailTrace_289087
  have hstable : (prefixWord ++ tailWord_289087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289087).length < 2 ^ (prefixWord ++ tailWord_289087).sum := by decide
  have hdescent : baseEnd_289087 < baseStart_289087 := by decide
  rcases family_descends (prefixWord ++ tailWord_289087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289104 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3]
def baseStart_289104 : Nat := 118140960795 + 289104 * 2 ^ 59
def prefixEnd_289104 : Nat := 4983230072969 + 3 ^ 40 * 289104 * 2
def baseEnd_289104 : Nat := 148449311137542112970441

theorem tailTrace_289104 : CollatzResearch.WordTrace tailWord_289104 prefixEnd_289104 148449311137542112970441 := by
  unfold tailWord_289104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272244572316528938681183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7029659429755371918241577 5272244572316528938681183)
  ·
    refine ⟨7908366858474793408021775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5272244572316528938681183 7908366858474793408021775)
    ·
      refine ⟨11862550287712190112032663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7908366858474793408021775 11862550287712190112032663)
      ·
        refine ⟨17793825431568285168048995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11862550287712190112032663 17793825431568285168048995)
        ·
          refine ⟨26690738147352427752073493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17793825431568285168048995 26690738147352427752073493)
          ·
            refine ⟨1251128350657145050878445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26690738147352427752073493 1251128350657145050878445)
            ·
              refine ⟨469173131496429394079417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251128350657145050878445 469173131496429394079417)
              ·
                refine ⟨351879848622322045559563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469173131496429394079417 351879848622322045559563)
                ·
                  refine ⟨527819772933483068339345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351879848622322045559563 527819772933483068339345)
                  ·
                    refine ⟨395864829700112301254509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 527819772933483068339345 395864829700112301254509)
                    ·
                      refine ⟨148449311137542112970441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 395864829700112301254509 148449311137542112970441)
                      ·
                        rfl

theorem cell23_289104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_289104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289104 prefixEnd_289104 := by exact prefixLift 289104
  have htrace : WordTrace (prefixWord ++ tailWord_289104) baseStart_289104 baseEnd_289104 := by
    simpa [prefixWord, tailWord_289104, baseEnd_289104] using wordTrace_append hprefix tailTrace_289104
  have hstable : (prefixWord ++ tailWord_289104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289104).length < 2 ^ (prefixWord ++ tailWord_289104).sum := by decide
  have hdescent : baseEnd_289104 < baseStart_289104 := by decide
  rcases family_descends (prefixWord ++ tailWord_289104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289178 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2]
def baseStart_289178 : Nat := 118140960795 + 289178 * 2 ^ 59
def prefixEnd_289178 : Nat := 4983230072969 + 3 ^ 40 * 289178 * 2
def baseEnd_289178 : Nat := 148487308705974823445101

theorem tailTrace_289178 : CollatzResearch.WordTrace tailWord_289178 prefixEnd_289178 148487308705974823445101 := by
  unfold tailWord_289178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636797036591242128889047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7031458764243312343704125 2636797036591242128889047)
  ·
    refine ⟨3955195554886863193333571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2636797036591242128889047 3955195554886863193333571)
    ·
      refine ⟨5932793332330294790000357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3955195554886863193333571 5932793332330294790000357)
      ·
        refine ⟨1112398749811930273125067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5932793332330294790000357 1112398749811930273125067)
        ·
          refine ⟨1668598124717895409687601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112398749811930273125067 1668598124717895409687601)
          ·
            refine ⟨1251448593538421557265701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1668598124717895409687601 1251448593538421557265701)
            ·
              refine ⟨234646611288454041987319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1251448593538421557265701 234646611288454041987319)
              ·
                refine ⟨351969916932681062980979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234646611288454041987319 351969916932681062980979)
                ·
                  refine ⟨527954875399021594471469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351969916932681062980979 527954875399021594471469)
                  ·
                    refine ⟨197983078274633097926801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 527954875399021594471469 197983078274633097926801)
                    ·
                      refine ⟨148487308705974823445101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 197983078274633097926801 148487308705974823445101)
                      ·
                        rfl

theorem cell23_289178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_289178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289178 prefixEnd_289178 := by exact prefixLift 289178
  have htrace : WordTrace (prefixWord ++ tailWord_289178) baseStart_289178 baseEnd_289178 := by
    simpa [prefixWord, tailWord_289178, baseEnd_289178] using wordTrace_append hprefix tailTrace_289178
  have hstable : (prefixWord ++ tailWord_289178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289178).length < 2 ^ (prefixWord ++ tailWord_289178).sum := by decide
  have hdescent : baseEnd_289178 < baseStart_289178 := by decide
  rcases family_descends (prefixWord ++ tailWord_289178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289185 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_289185 : Nat := 118140960795 + 289185 * 2 ^ 59
def prefixEnd_289185 : Nat := 4983230072969 + 3 ^ 40 * 289185 * 2
def baseEnd_289185 : Nat := 148490903070556296057569

theorem tailTrace_289185 : CollatzResearch.WordTrace tailWord_289185 prefixEnd_289185 148490903070556296057569 := by
  unfold tailWord_289185
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547443457339608711061009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7031628971559739140707339 10547443457339608711061009)
  ·
    refine ⟨7910582593004706533295757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10547443457339608711061009 7910582593004706533295757)
    ·
      refine ⟨2966468472376764949985909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7910582593004706533295757 2966468472376764949985909)
      ·
        refine ⟨278106419285321714061179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2966468472376764949985909 278106419285321714061179)
        ·
          refine ⟨417159628927982571091769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278106419285321714061179 417159628927982571091769)
          ·
            refine ⟨312869721695986928318827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417159628927982571091769 312869721695986928318827)
            ·
              refine ⟨469304582543980392478241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312869721695986928318827 469304582543980392478241)
              ·
                refine ⟨351978436907985294358681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469304582543980392478241 351978436907985294358681)
                ·
                  refine ⟨263983827680988970769011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351978436907985294358681 263983827680988970769011)
                  ·
                    refine ⟨395975741521483456153517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 263983827680988970769011 395975741521483456153517)
                    ·
                      refine ⟨148490903070556296057569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 395975741521483456153517 148490903070556296057569)
                      ·
                        rfl

theorem cell23_289185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_289185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289185 prefixEnd_289185 := by exact prefixLift 289185
  have htrace : WordTrace (prefixWord ++ tailWord_289185) baseStart_289185 baseEnd_289185 := by
    simpa [prefixWord, tailWord_289185, baseEnd_289185] using wordTrace_append hprefix tailTrace_289185
  have hstable : (prefixWord ++ tailWord_289185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289185).length < 2 ^ (prefixWord ++ tailWord_289185).sum := by decide
  have hdescent : baseEnd_289185 < baseStart_289185 := by decide
  rcases family_descends (prefixWord ++ tailWord_289185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289187 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4]
def baseStart_289187 : Nat := 118140960795 + 289187 * 2 ^ 59
def prefixEnd_289187 : Nat := 4983230072969 + 3 ^ 40 * 289187 * 2
def baseEnd_289187 : Nat := 148491930031865288232559

theorem tailTrace_289187 : CollatzResearch.WordTrace tailWord_289187 prefixEnd_289187 148491930031865288232559 := by
  unfold tailWord_289187
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547516403332363052633815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7031677602221575368422543 10547516403332363052633815)
  ·
    refine ⟨15821274604998544578950723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10547516403332363052633815 15821274604998544578950723)
    ·
      refine ⟨23731911907497816868426085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15821274604998544578950723 23731911907497816868426085)
      ·
        refine ⟨4449733482655840662829891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23731911907497816868426085 4449733482655840662829891)
        ·
          refine ⟨6674600223983760994244837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449733482655840662829891 6674600223983760994244837)
          ·
            refine ⟨1251487541996955186420907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6674600223983760994244837 1251487541996955186420907)
            ·
              refine ⟨1877231312995432779631361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251487541996955186420907 1877231312995432779631361)
              ·
                refine ⟨1407923484746574584723521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877231312995432779631361 1407923484746574584723521)
                ·
                  refine ⟨1055942613559930938542641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1407923484746574584723521 1055942613559930938542641)
                  ·
                    refine ⟨791956960169948203906981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1055942613559930938542641 791956960169948203906981)
                    ·
                      refine ⟨148491930031865288232559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 791956960169948203906981 148491930031865288232559)
                      ·
                        rfl

theorem cell23_289187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_289187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289187 prefixEnd_289187 := by exact prefixLift 289187
  have htrace : WordTrace (prefixWord ++ tailWord_289187) baseStart_289187 baseEnd_289187 := by
    simpa [prefixWord, tailWord_289187, baseEnd_289187] using wordTrace_append hprefix tailTrace_289187
  have hstable : (prefixWord ++ tailWord_289187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289187).length < 2 ^ (prefixWord ++ tailWord_289187).sum := by decide
  have hdescent : baseEnd_289187 < baseStart_289187 := by decide
  rcases family_descends (prefixWord ++ tailWord_289187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289227 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 2, 5]
def baseStart_289227 : Nat := 118140960795 + 289227 * 2 ^ 59
def prefixEnd_289227 : Nat := 4983230072969 + 3 ^ 40 * 289227 * 2
def baseEnd_289227 : Nat := 49504156419348377244125

theorem tailTrace_289227 : CollatzResearch.WordTrace tailWord_289227 prefixEnd_289227 49504156419348377244125 := by
  unfold tailWord_289227
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548975323187449884089935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7032650215458299922726623 10548975323187449884089935)
  ·
    refine ⟨15823462984781174826134903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10548975323187449884089935 15823462984781174826134903)
    ·
      refine ⟨23735194477171762239202355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15823462984781174826134903 23735194477171762239202355)
      ·
        refine ⟨35602791715757643358803533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23735194477171762239202355 35602791715757643358803533)
        ·
          refine ⟨13351046893409116259551325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35602791715757643358803533 13351046893409116259551325)
          ·
            refine ⟨5006642585028418597331747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13351046893409116259551325 5006642585028418597331747)
            ·
              refine ⟨7509963877542627895997621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006642585028418597331747 7509963877542627895997621)
              ·
                refine ⟨704059113519621365249777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7509963877542627895997621 704059113519621365249777)
                ·
                  refine ⟨528044335139716023937333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704059113519621365249777 528044335139716023937333)
                  ·
                    refine ⟨49504156419348377244125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 528044335139716023937333 49504156419348377244125)
                    ·
                      rfl

theorem cell23_289227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 5].length) (baseStart_289227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289227 prefixEnd_289227 := by exact prefixLift 289227
  have htrace : WordTrace (prefixWord ++ tailWord_289227) baseStart_289227 baseEnd_289227 := by
    simpa [prefixWord, tailWord_289227, baseEnd_289227] using wordTrace_append hprefix tailTrace_289227
  have hstable : (prefixWord ++ tailWord_289227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289227).length < 2 ^ (prefixWord ++ tailWord_289227).sum := by decide
  have hdescent : baseEnd_289227 < baseStart_289227 := by decide
  rcases family_descends (prefixWord ++ tailWord_289227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289264 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 6, 2]
def baseStart_289264 : Nat := 118140960795 + 289264 * 2 ^ 59
def prefixEnd_289264 : Nat := 4983230072969 + 3 ^ 40 * 289264 * 2
def baseEnd_289264 : Nat := 148531468042261486969705

theorem tailTrace_289264 : CollatzResearch.WordTrace tailWord_289264 prefixEnd_289264 148531468042261486969705 := by
  unfold tailWord_289264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275162412026702601593423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7033549882702270135457897 5275162412026702601593423)
  ·
    refine ⟨7912743618040053902390135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5275162412026702601593423 7912743618040053902390135)
    ·
      refine ⟨11869115427060080853585203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7912743618040053902390135 11869115427060080853585203)
      ·
        refine ⟨17803673140590121280377805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11869115427060080853585203 17803673140590121280377805)
        ·
          refine ⟨6676377427721295480141677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17803673140590121280377805 6676377427721295480141677)
          ·
            refine ⟨2503641535395485805053129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6676377427721295480141677 2503641535395485805053129)
            ·
              refine ⟨1877731151546614353789847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503641535395485805053129 1877731151546614353789847)
              ·
                refine ⟨2816596727319921530684771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877731151546614353789847 2816596727319921530684771)
                ·
                  refine ⟨4224895090979882296027157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816596727319921530684771 4224895090979882296027157)
                  ·
                    refine ⟨198041957389681982626273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4224895090979882296027157 198041957389681982626273)
                    ·
                      refine ⟨148531468042261486969705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198041957389681982626273 148531468042261486969705)
                      ·
                        rfl

theorem cell23_289264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 6, 2].length) (baseStart_289264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289264 prefixEnd_289264 := by exact prefixLift 289264
  have htrace : WordTrace (prefixWord ++ tailWord_289264) baseStart_289264 baseEnd_289264 := by
    simpa [prefixWord, tailWord_289264, baseEnd_289264] using wordTrace_append hprefix tailTrace_289264
  have hstable : (prefixWord ++ tailWord_289264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289264).length < 2 ^ (prefixWord ++ tailWord_289264).sum := by decide
  have hdescent : baseEnd_289264 < baseStart_289264 := by decide
  rcases family_descends (prefixWord ++ tailWord_289264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289281 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_289281 : Nat := 118140960795 + 289281 * 2 ^ 59
def prefixEnd_289281 : Nat := 4983230072969 + 3 ^ 40 * 289281 * 2
def baseEnd_289281 : Nat := 148540197213387920457127

theorem tailTrace_289281 : CollatzResearch.WordTrace tailWord_289281 prefixEnd_289281 148540197213387920457127 := by
  unfold tailWord_289281
  simp only [CollatzResearch.WordTrace]
  refine ⟨10550944864991817106555697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7033963243327878071037131 10550944864991817106555697)
  ·
    refine ⟨7913208648743862829916773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10550944864991817106555697 7913208648743862829916773)
    ·
      refine ⟨1483726621639474280609395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7913208648743862829916773 1483726621639474280609395)
      ·
        refine ⟨2225589932459211420914093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483726621639474280609395 2225589932459211420914093)
        ·
          refine ⟨834596224672204282842785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2225589932459211420914093 834596224672204282842785)
          ·
            refine ⟨625947168504153212132089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834596224672204282842785 625947168504153212132089)
            ·
              refine ⟨469460376378114909099067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625947168504153212132089 469460376378114909099067)
              ·
                refine ⟨704190564567172363648601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469460376378114909099067 704190564567172363648601)
                ·
                  refine ⟨528142923425379272736451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704190564567172363648601 528142923425379272736451)
                  ·
                    refine ⟨792214385138068909104677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 528142923425379272736451 792214385138068909104677)
                    ·
                      refine ⟨148540197213387920457127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 792214385138068909104677 148540197213387920457127)
                      ·
                        rfl

theorem cell23_289281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_289281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289281 prefixEnd_289281 := by exact prefixLift 289281
  have htrace : WordTrace (prefixWord ++ tailWord_289281) baseStart_289281 baseEnd_289281 := by
    simpa [prefixWord, tailWord_289281, baseEnd_289281] using wordTrace_append hprefix tailTrace_289281
  have hstable : (prefixWord ++ tailWord_289281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289281).length < 2 ^ (prefixWord ++ tailWord_289281).sum := by decide
  have hdescent : baseEnd_289281 < baseStart_289281 := by decide
  rcases family_descends (prefixWord ++ tailWord_289281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289304 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 6]
def baseStart_289304 : Nat := 118140960795 + 289304 * 2 ^ 59
def prefixEnd_289304 : Nat := 4983230072969 + 3 ^ 40 * 289304 * 2
def baseEnd_289304 : Nat := 16505778585382370052169

theorem tailTrace_289304 : CollatzResearch.WordTrace tailWord_289304 prefixEnd_289304 16505778585382370052169 := by
  unfold tailWord_289304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275891871954246017321483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7034522495938994689761977 5275891871954246017321483)
  ·
    refine ⟨7913837807931369025982225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5275891871954246017321483 7913837807931369025982225)
    ·
      refine ⟨5935378355948526769486669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7913837807931369025982225 5935378355948526769486669)
      ·
        refine ⟨2225766883480697538557501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5935378355948526769486669 2225766883480697538557501)
        ·
          refine ⟨834662581305261576959063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2225766883480697538557501 834662581305261576959063)
          ·
            refine ⟨1251993871957892365438595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834662581305261576959063 1251993871957892365438595)
            ·
              refine ⟨1877990807936838548157893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251993871957892365438595 1877990807936838548157893)
              ·
                refine ⟨352123276488157227779605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1877990807936838548157893 352123276488157227779605)
                ·
                  refine ⟨16505778585382370052169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 352123276488157227779605 16505778585382370052169)
                  ·
                    rfl

theorem cell23_289304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 6].length) (baseStart_289304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289304 prefixEnd_289304 := by exact prefixLift 289304
  have htrace : WordTrace (prefixWord ++ tailWord_289304) baseStart_289304 baseEnd_289304 := by
    simpa [prefixWord, tailWord_289304, baseEnd_289304] using wordTrace_append hprefix tailTrace_289304
  have hstable : (prefixWord ++ tailWord_289304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289304).length < 2 ^ (prefixWord ++ tailWord_289304).sum := by decide
  have hdescent : baseEnd_289304 < baseStart_289304 := by decide
  rcases family_descends (prefixWord ++ tailWord_289304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289308 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_289308 : Nat := 118140960795 + 289308 * 2 ^ 59
def prefixEnd_289308 : Nat := 4983230072969 + 3 ^ 40 * 289308 * 2
def baseEnd_289308 : Nat := 49518020397019771606501

theorem tailTrace_289308 : CollatzResearch.WordTrace tailWord_289308 prefixEnd_289308 49518020397019771606501 := by
  unfold tailWord_289308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275964817947000358894289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7034619757262667145192385 5275964817947000358894289)
  ·
    refine ⟨3956973613460250269170717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5275964817947000358894289 3956973613460250269170717)
    ·
      refine ⟨1483865105047593850939019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3956973613460250269170717 1483865105047593850939019)
      ·
        refine ⟨2225797657571390776408529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483865105047593850939019 2225797657571390776408529)
        ·
          refine ⟨1669348243178543082306397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2225797657571390776408529 1669348243178543082306397)
          ·
            refine ⟨626005591191953655864899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1669348243178543082306397 626005591191953655864899)
            ·
              refine ⟨939008386787930483797349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626005591191953655864899 939008386787930483797349)
              ·
                refine ⟨176064072522736965712003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 939008386787930483797349 176064072522736965712003)
                ·
                  refine ⟨264096108784105448568005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176064072522736965712003 264096108784105448568005)
                  ·
                    refine ⟨49518020397019771606501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264096108784105448568005 49518020397019771606501)
                    ·
                      rfl

theorem cell23_289308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_289308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289308 prefixEnd_289308 := by exact prefixLift 289308
  have htrace : WordTrace (prefixWord ++ tailWord_289308) baseStart_289308 baseEnd_289308 := by
    simpa [prefixWord, tailWord_289308, baseEnd_289308] using wordTrace_append hprefix tailTrace_289308
  have hstable : (prefixWord ++ tailWord_289308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289308).length < 2 ^ (prefixWord ++ tailWord_289308).sum := by decide
  have hdescent : baseEnd_289308 < baseStart_289308 := by decide
  rcases family_descends (prefixWord ++ tailWord_289308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289314 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_289314 : Nat := 118140960795 + 289314 * 2 ^ 59
def prefixEnd_289314 : Nat := 4983230072969 + 3 ^ 40 * 289314 * 2
def baseEnd_289314 : Nat := 148557142074986291344475

theorem tailTrace_289314 : CollatzResearch.WordTrace tailWord_289314 prefixEnd_289314 148557142074986291344475 := by
  unfold tailWord_289314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638037118468065935626749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7034765649248175828337997 2638037118468065935626749)
  ·
    refine ⟨989263919425524725860031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2638037118468065935626749 989263919425524725860031)
    ·
      refine ⟨1483895879138287088790047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989263919425524725860031 1483895879138287088790047)
      ·
        refine ⟨2225843818707430633185071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483895879138287088790047 2225843818707430633185071)
        ·
          refine ⟨3338765728061145949777607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225843818707430633185071 3338765728061145949777607)
          ·
            refine ⟨5008148592091718924666411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338765728061145949777607 5008148592091718924666411)
            ·
              refine ⟨7512222888137578386999617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008148592091718924666411 7512222888137578386999617)
              ·
                refine ⟨5634167166103183790249713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7512222888137578386999617 5634167166103183790249713)
                ·
                  refine ⟨4225625374577387842687285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634167166103183790249713 4225625374577387842687285)
                  ·
                    refine ⟨396152378866630110251933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4225625374577387842687285 396152378866630110251933)
                    ·
                      refine ⟨148557142074986291344475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 396152378866630110251933 148557142074986291344475)
                      ·
                        rfl

theorem cell23_289314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_289314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289314 prefixEnd_289314 := by exact prefixLift 289314
  have htrace : WordTrace (prefixWord ++ tailWord_289314) baseStart_289314 baseEnd_289314 := by
    simpa [prefixWord, tailWord_289314, baseEnd_289314] using wordTrace_append hprefix tailTrace_289314
  have hstable : (prefixWord ++ tailWord_289314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289314).length < 2 ^ (prefixWord ++ tailWord_289314).sum := by decide
  have hdescent : baseEnd_289314 < baseStart_289314 := by decide
  rcases family_descends (prefixWord ++ tailWord_289314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289331 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 3]
def baseStart_289331 : Nat := 118140960795 + 289331 * 2 ^ 59
def prefixEnd_289331 : Nat := 4983230072969 + 3 ^ 40 * 289331 * 2
def baseEnd_289331 : Nat := 148565871246112724831897

theorem tailTrace_289331 : CollatzResearch.WordTrace tailWord_289331 prefixEnd_289331 148565871246112724831897 := by
  unfold tailWord_289331
  simp only [CollatzResearch.WordTrace]
  refine ⟨10552768514810675645875847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7035179009873783763917231 10552768514810675645875847)
  ·
    refine ⟨15829152772216013468813771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10552768514810675645875847 15829152772216013468813771)
    ·
      refine ⟨23743729158324020203220657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15829152772216013468813771 23743729158324020203220657)
      ·
        refine ⟨17807796868743015152415493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23743729158324020203220657 17807796868743015152415493)
        ·
          refine ⟨3338961912889315341077905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17807796868743015152415493 3338961912889315341077905)
          ·
            refine ⟨2504221434666986505808429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3338961912889315341077905 2504221434666986505808429)
            ·
              refine ⟨939083038000119939678161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2504221434666986505808429 939083038000119939678161)
              ·
                refine ⟨704312278500089954758621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939083038000119939678161 704312278500089954758621)
                ·
                  refine ⟨264117104437533733034483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704312278500089954758621 264117104437533733034483)
                  ·
                    refine ⟨396175656656300599551725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 264117104437533733034483 396175656656300599551725)
                    ·
                      refine ⟨148565871246112724831897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 396175656656300599551725 148565871246112724831897)
                      ·
                        rfl

theorem cell23_289331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_289331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289331 prefixEnd_289331 := by exact prefixLift 289331
  have htrace : WordTrace (prefixWord ++ tailWord_289331) baseStart_289331 baseEnd_289331 := by
    simpa [prefixWord, tailWord_289331, baseEnd_289331] using wordTrace_append hprefix tailTrace_289331
  have hstable : (prefixWord ++ tailWord_289331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289331).length < 2 ^ (prefixWord ++ tailWord_289331).sum := by decide
  have hdescent : baseEnd_289331 < baseStart_289331 := by decide
  rcases family_descends (prefixWord ++ tailWord_289331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289332 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_289332 : Nat := 118140960795 + 289332 * 2 ^ 59
def prefixEnd_289332 : Nat := 4983230072969 + 3 ^ 40 * 289332 * 2
def baseEnd_289332 : Nat := 148566384726767220919393

theorem tailTrace_289332 : CollatzResearch.WordTrace tailWord_289332 prefixEnd_289332 148566384726767220919393 := by
  unfold tailWord_289332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276402493903526408331125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7035203325204701877774833 5276402493903526408331125)
  ·
    refine ⟨494662733803455600781043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5276402493903526408331125 494662733803455600781043)
    ·
      refine ⟨741994100705183401171565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494662733803455600781043 741994100705183401171565)
      ·
        refine ⟨278247787764443775439337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 741994100705183401171565 278247787764443775439337)
        ·
          refine ⟨208685840823332831579503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278247787764443775439337 208685840823332831579503)
          ·
            refine ⟨313028761234999247369255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208685840823332831579503 313028761234999247369255)
            ·
              refine ⟨469543141852498871053883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313028761234999247369255 469543141852498871053883)
              ·
                refine ⟨704314712778748306580825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469543141852498871053883 704314712778748306580825)
                ·
                  refine ⟨528236034584061229935619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704314712778748306580825 528236034584061229935619)
                  ·
                    refine ⟨792354051876091844903429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 528236034584061229935619 792354051876091844903429)
                    ·
                      refine ⟨148566384726767220919393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 792354051876091844903429 148566384726767220919393)
                      ·
                        rfl

theorem cell23_289332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_289332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289332 prefixEnd_289332 := by exact prefixLift 289332
  have htrace : WordTrace (prefixWord ++ tailWord_289332) baseStart_289332 baseEnd_289332 := by
    simpa [prefixWord, tailWord_289332, baseEnd_289332] using wordTrace_append hprefix tailTrace_289332
  have hstable : (prefixWord ++ tailWord_289332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289332).length < 2 ^ (prefixWord ++ tailWord_289332).sum := by decide
  have hdescent : baseEnd_289332 < baseStart_289332 := by decide
  rcases family_descends (prefixWord ++ tailWord_289332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289342 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_289342 : Nat := 118140960795 + 289342 * 2 ^ 59
def prefixEnd_289342 : Nat := 4983230072969 + 3 ^ 40 * 289342 * 2
def baseEnd_289342 : Nat := 49523839844437393931449

theorem tailTrace_289342 : CollatzResearch.WordTrace tailWord_289342 prefixEnd_289342 49523839844437393931449 := by
  unfold tailWord_289342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319146214721353065565785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7035446478513883016350853 1319146214721353065565785)
  ·
    refine ⟨989359661041014799174339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1319146214721353065565785 989359661041014799174339)
    ·
      refine ⟨1484039491561522198761509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989359661041014799174339 1484039491561522198761509)
      ·
        refine ⟨278257404667785412267783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1484039491561522198761509 278257404667785412267783)
        ·
          refine ⟨417386107001678118401675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278257404667785412267783 417386107001678118401675)
          ·
            refine ⟨626079160502517177602513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417386107001678118401675 626079160502517177602513)
            ·
              refine ⟨469559370376887883201885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626079160502517177602513 469559370376887883201885)
              ·
                refine ⟨176084763891332956200707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469559370376887883201885 176084763891332956200707)
                ·
                  refine ⟨264127145836999434301061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176084763891332956200707 264127145836999434301061)
                  ·
                    refine ⟨49523839844437393931449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264127145836999434301061 49523839844437393931449)
                    ·
                      rfl

theorem cell23_289342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_289342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289342 prefixEnd_289342 := by exact prefixLift 289342
  have htrace : WordTrace (prefixWord ++ tailWord_289342) baseStart_289342 baseEnd_289342 := by
    simpa [prefixWord, tailWord_289342, baseEnd_289342] using wordTrace_append hprefix tailTrace_289342
  have hstable : (prefixWord ++ tailWord_289342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289342).length < 2 ^ (prefixWord ++ tailWord_289342).sum := by decide
  have hdescent : baseEnd_289342 < baseStart_289342 := by decide
  rcases family_descends (prefixWord ++ tailWord_289342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289351 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 1, 5]
def baseStart_289351 : Nat := 118140960795 + 289351 * 2 ^ 59
def prefixEnd_289351 : Nat := 4983230072969 + 3 ^ 40 * 289351 * 2
def baseEnd_289351 : Nat := 49525380286400882193935

theorem tailTrace_289351 : CollatzResearch.WordTrace tailWord_289351 prefixEnd_289351 49525380286400882193935 := by
  unfold tailWord_289351
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553497974738219061603907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7035665316492146041069271 10553497974738219061603907)
  ·
    refine ⟨15830246962107328592405861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10553497974738219061603907 15830246962107328592405861)
    ·
      refine ⟨2968171305395124111076099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15830246962107328592405861 2968171305395124111076099)
      ·
        refine ⟨4452256958092686166614149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968171305395124111076099 4452256958092686166614149)
        ·
          refine ⟨834798179642378656240153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4452256958092686166614149 834798179642378656240153)
          ·
            refine ⟨626098634731783992180115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834798179642378656240153 626098634731783992180115)
            ·
              refine ⟨939147952097675988270173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626098634731783992180115 939147952097675988270173)
              ·
                refine ⟨352180482036628495601315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939147952097675988270173 352180482036628495601315)
                ·
                  refine ⟨528270723054942743401973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352180482036628495601315 528270723054942743401973)
                  ·
                    refine ⟨49525380286400882193935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 528270723054942743401973 49525380286400882193935)
                    ·
                      rfl

theorem cell23_289351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_289351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289351 prefixEnd_289351 := by exact prefixLift 289351
  have htrace : WordTrace (prefixWord ++ tailWord_289351) baseStart_289351 baseEnd_289351 := by
    simpa [prefixWord, tailWord_289351, baseEnd_289351] using wordTrace_append hprefix tailTrace_289351
  have hstable : (prefixWord ++ tailWord_289351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289351).length < 2 ^ (prefixWord ++ tailWord_289351).sum := by decide
  have hdescent : baseEnd_289351 < baseStart_289351 := by decide
  rcases family_descends (prefixWord ++ tailWord_289351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289388 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 3, 2, 2]
def baseStart_289388 : Nat := 118140960795 + 289388 * 2 ^ 59
def prefixEnd_289388 : Nat := 4983230072969 + 3 ^ 40 * 289388 * 2
def baseEnd_289388 : Nat := 148595139643419001819135

theorem tailTrace_289388 : CollatzResearch.WordTrace tailWord_289388 prefixEnd_289388 148595139643419001819135 := by
  unfold tailWord_289388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277423737802087190350409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7036564983736116253800545 5277423737802087190350409)
  ·
    refine ⟨3958067803351565392762807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5277423737802087190350409 3958067803351565392762807)
    ·
      refine ⟨5937101705027348089144211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3958067803351565392762807 5937101705027348089144211)
      ·
        refine ⟨8905652557541022133716317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937101705027348089144211 8905652557541022133716317)
        ·
          refine ⟨3339619709077883300143619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8905652557541022133716317 3339619709077883300143619)
          ·
            refine ⟨5009429563616824950215429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339619709077883300143619 5009429563616824950215429)
            ·
              refine ⟨939268043178154678165393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5009429563616824950215429 939268043178154678165393)
              ·
                refine ⟨704451032383616008624045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939268043178154678165393 704451032383616008624045)
                ·
                  refine ⟨264169137143856003234017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704451032383616008624045 264169137143856003234017)
                  ·
                    refine ⟨198126852857892002425513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264169137143856003234017 198126852857892002425513)
                    ·
                      refine ⟨148595139643419001819135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198126852857892002425513 148595139643419001819135)
                      ·
                        rfl

theorem cell23_289388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_289388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289388 prefixEnd_289388 := by exact prefixLift 289388
  have htrace : WordTrace (prefixWord ++ tailWord_289388) baseStart_289388 baseEnd_289388 := by
    simpa [prefixWord, tailWord_289388, baseEnd_289388] using wordTrace_append hprefix tailTrace_289388
  have hstable : (prefixWord ++ tailWord_289388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289388).length < 2 ^ (prefixWord ++ tailWord_289388).sum := by decide
  have hdescent : baseEnd_289388 < baseStart_289388 := by decide
  rcases family_descends (prefixWord ++ tailWord_289388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289391 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 3]
def baseStart_289391 : Nat := 118140960795 + 289391 * 2 ^ 59
def prefixEnd_289391 : Nat := 4983230072969 + 3 ^ 40 * 289391 * 2
def baseEnd_289391 : Nat := 148596680085382490081621

theorem tailTrace_289391 : CollatzResearch.WordTrace tailWord_289391 prefixEnd_289391 148596680085382490081621 := by
  unfold tailWord_289391
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554956894593305893060027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7036637929728870595373351 10554956894593305893060027)
  ·
    refine ⟨15832435341889958839590041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10554956894593305893060027 15832435341889958839590041)
    ·
      refine ⟨11874326506417469129692531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15832435341889958839590041 11874326506417469129692531)
      ·
        refine ⟨17811489759626203694538797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11874326506417469129692531 17811489759626203694538797)
        ·
          refine ⟨6679308659859826385452049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17811489759626203694538797 6679308659859826385452049)
          ·
            refine ⟨5009481494894869789089037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679308659859826385452049 5009481494894869789089037)
            ·
              refine ⟨1878555560585576170908389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5009481494894869789089037 1878555560585576170908389)
              ·
                refine ⟨352229167609795532045323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1878555560585576170908389 352229167609795532045323)
                ·
                  refine ⟨528343751414693298067985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352229167609795532045323 528343751414693298067985)
                  ·
                    refine ⟨396257813561019973550989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 528343751414693298067985 396257813561019973550989)
                    ·
                      refine ⟨148596680085382490081621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 396257813561019973550989 148596680085382490081621)
                      ·
                        rfl

theorem cell23_289391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_289391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289391 prefixEnd_289391 := by exact prefixLift 289391
  have htrace : WordTrace (prefixWord ++ tailWord_289391) baseStart_289391 baseEnd_289391 := by
    simpa [prefixWord, tailWord_289391, baseEnd_289391] using wordTrace_append hprefix tailTrace_289391
  have hstable : (prefixWord ++ tailWord_289391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289391).length < 2 ^ (prefixWord ++ tailWord_289391).sum := by decide
  have hdescent : baseEnd_289391 < baseStart_289391 := by decide
  rcases family_descends (prefixWord ++ tailWord_289391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289438 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_289438 : Nat := 118140960795 + 289438 * 2 ^ 59
def prefixEnd_289438 : Nat := 4983230072969 + 3 ^ 40 * 289438 * 2
def baseEnd_289438 : Nat := 148620813676143806193905

theorem tailTrace_289438 : CollatzResearch.WordTrace tailWord_289438 prefixEnd_289438 148620813676143806193905 := by
  unfold tailWord_289438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319583890677879115002621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7037780750282021946680645 1319583890677879115002621)
  ·
    refine ⟨494843959004204668125983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1319583890677879115002621 494843959004204668125983)
    ·
      refine ⟨742265938506307002188975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494843959004204668125983 742265938506307002188975)
      ·
        refine ⟨1113398907759460503283463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742265938506307002188975 1113398907759460503283463)
        ·
          refine ⟨1670098361639190754925195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113398907759460503283463 1670098361639190754925195)
          ·
            refine ⟨2505147542458786132387793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670098361639190754925195 2505147542458786132387793)
            ·
              refine ⟨1878860656844089599290845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505147542458786132387793 1878860656844089599290845)
              ·
                refine ⟨704572746316533599734067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1878860656844089599290845 704572746316533599734067)
                ·
                  refine ⟨1056859119474800399601101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704572746316533599734067 1056859119474800399601101)
                  ·
                    refine ⟨396322169803050149850413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056859119474800399601101 396322169803050149850413)
                    ·
                      refine ⟨148620813676143806193905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 396322169803050149850413 148620813676143806193905)
                      ·
                        rfl

theorem cell23_289438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_289438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289438 prefixEnd_289438 := by exact prefixLift 289438
  have htrace : WordTrace (prefixWord ++ tailWord_289438) baseStart_289438 baseEnd_289438 := by
    simpa [prefixWord, tailWord_289438, baseEnd_289438] using wordTrace_append hprefix tailTrace_289438
  have hstable : (prefixWord ++ tailWord_289438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289438).length < 2 ^ (prefixWord ++ tailWord_289438).sum := by decide
  have hdescent : baseEnd_289438 < baseStart_289438 := by decide
  rcases family_descends (prefixWord ++ tailWord_289438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289473 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_289473 : Nat := 118140960795 + 289473 * 2 ^ 59
def prefixEnd_289473 : Nat := 4983230072969 + 3 ^ 40 * 289473 * 2
def baseEnd_289473 : Nat := 148638785499051169256245

theorem tailTrace_289473 : CollatzResearch.WordTrace tailWord_289473 prefixEnd_289473 148638785499051169256245 := by
  unfold tailWord_289473
  simp only [CollatzResearch.WordTrace]
  refine ⟨10557947680296233897545073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7038631786864155931696715 10557947680296233897545073)
  ·
    refine ⟨7918460760222175423158805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10557947680296233897545073 7918460760222175423158805)
    ·
      refine ⟨371177848135414472960569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7918460760222175423158805 371177848135414472960569)
      ·
        refine ⟨278383386101560854720427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371177848135414472960569 278383386101560854720427)
        ·
          refine ⟨417575079152341282080641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278383386101560854720427 417575079152341282080641)
          ·
            refine ⟨313181309364255961560481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417575079152341282080641 313181309364255961560481)
            ·
              refine ⟨234885982023191971170361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313181309364255961560481 234885982023191971170361)
              ·
                refine ⟨176164486517393978377771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234885982023191971170361 176164486517393978377771)
                ·
                  refine ⟨264246729776090967566657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176164486517393978377771 264246729776090967566657)
                  ·
                    refine ⟨198185047332068225674993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264246729776090967566657 198185047332068225674993)
                    ·
                      refine ⟨148638785499051169256245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198185047332068225674993 148638785499051169256245)
                      ·
                        rfl

theorem cell23_289473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_289473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289473 prefixEnd_289473 := by exact prefixLift 289473
  have htrace : WordTrace (prefixWord ++ tailWord_289473) baseStart_289473 baseEnd_289473 := by
    simpa [prefixWord, tailWord_289473, baseEnd_289473] using wordTrace_append hprefix tailTrace_289473
  have hstable : (prefixWord ++ tailWord_289473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289473).length < 2 ^ (prefixWord ++ tailWord_289473).sum := by decide
  have hdescent : baseEnd_289473 < baseStart_289473 := by decide
  rcases family_descends (prefixWord ++ tailWord_289473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289495 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 2, 2, 2]
def baseStart_289495 : Nat := 118140960795 + 289495 * 2 ^ 59
def prefixEnd_289495 : Nat := 4983230072969 + 3 ^ 40 * 289495 * 2
def baseEnd_289495 : Nat := 148650082073450083181143

theorem tailTrace_289495 : CollatzResearch.WordTrace tailWord_289495 prefixEnd_289495 148650082073450083181143 := by
  unfold tailWord_289495
  simp only [CollatzResearch.WordTrace]
  refine ⟨10558750086216531654845939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7039166724144354436563959 10558750086216531654845939)
  ·
    refine ⟨15838125129324797482268909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10558750086216531654845939 15838125129324797482268909)
    ·
      refine ⟨5939296923496799055850841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15838125129324797482268909 5939296923496799055850841)
      ·
        refine ⟨4454472692622599291888131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5939296923496799055850841 4454472692622599291888131)
        ·
          refine ⟨6681709038933898937832197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454472692622599291888131 6681709038933898937832197)
          ·
            refine ⟨1252820444800106050843537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6681709038933898937832197 1252820444800106050843537)
            ·
              refine ⟨939615333600079538132653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252820444800106050843537 939615333600079538132653)
              ·
                refine ⟨352355750100029826799745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939615333600079538132653 352355750100029826799745)
                ·
                  refine ⟨264266812575022370099809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352355750100029826799745 264266812575022370099809)
                  ·
                    refine ⟨198200109431266777574857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264266812575022370099809 198200109431266777574857)
                    ·
                      refine ⟨148650082073450083181143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198200109431266777574857 148650082073450083181143)
                      ·
                        rfl

theorem cell23_289495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_289495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289495 prefixEnd_289495 := by exact prefixLift 289495
  have htrace : WordTrace (prefixWord ++ tailWord_289495) baseStart_289495 baseEnd_289495 := by
    simpa [prefixWord, tailWord_289495, baseEnd_289495] using wordTrace_append hprefix tailTrace_289495
  have hstable : (prefixWord ++ tailWord_289495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289495).length < 2 ^ (prefixWord ++ tailWord_289495).sum := by decide
  have hdescent : baseEnd_289495 < baseStart_289495 := by decide
  rcases family_descends (prefixWord ++ tailWord_289495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289518 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_289518 : Nat := 118140960795 + 289518 * 2 ^ 59
def prefixEnd_289518 : Nat := 4983230072969 + 3 ^ 40 * 289518 * 2
def baseEnd_289518 : Nat := 16517988014278165910393

theorem tailTrace_289518 : CollatzResearch.WordTrace tailWord_289518 prefixEnd_289518 16517988014278165910393 := by
  unfold tailWord_289518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319948620641650822866651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7039725976755471055288805 1319948620641650822866651)
  ·
    refine ⟨1979922930962476234299977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1319948620641650822866651 1979922930962476234299977)
    ·
      refine ⟨1484942198221857175724983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1979922930962476234299977 1484942198221857175724983)
      ·
        refine ⟨2227413297332785763587475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484942198221857175724983 2227413297332785763587475)
        ·
          refine ⟨3341119945999178645381213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227413297332785763587475 3341119945999178645381213)
          ·
            refine ⟨1252919979749691992017955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3341119945999178645381213 1252919979749691992017955)
            ·
              refine ⟨1879379969624537988026933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252919979749691992017955 1879379969624537988026933)
              ·
                refine ⟨176191872152300436377525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1879379969624537988026933 176191872152300436377525)
                ·
                  refine ⟨16517988014278165910393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176191872152300436377525 16517988014278165910393)
                  ·
                    rfl

theorem cell23_289518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_289518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289518 prefixEnd_289518 := by exact prefixLift 289518
  have htrace : WordTrace (prefixWord ++ tailWord_289518) baseStart_289518 baseEnd_289518 := by
    simpa [prefixWord, tailWord_289518, baseEnd_289518] using wordTrace_append hprefix tailTrace_289518
  have hstable : (prefixWord ++ tailWord_289518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289518).length < 2 ^ (prefixWord ++ tailWord_289518).sum := by decide
  have hdescent : baseEnd_289518 < baseStart_289518 := by decide
  rcases family_descends (prefixWord ++ tailWord_289518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289561 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 5, 4]
def baseStart_289561 : Nat := 118140960795 + 289561 * 2 ^ 59
def prefixEnd_289561 : Nat := 4983230072969 + 3 ^ 40 * 289561 * 2
def baseEnd_289561 : Nat := 49561323932215608318613

theorem tailTrace_289561 : CollatzResearch.WordTrace tailWord_289561 prefixEnd_289561 49561323932215608318613 := by
  unfold tailWord_289561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561157303977424926748537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7040771535984949951165691 10561157303977424926748537)
  ·
    refine ⟨7920867977983068695061403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10561157303977424926748537 7920867977983068695061403)
    ·
      refine ⟨11881301966974603042592105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7920867977983068695061403 11881301966974603042592105)
      ·
        refine ⟨8910976475230952281944079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11881301966974603042592105 8910976475230952281944079)
        ·
          refine ⟨13366464712846428422916119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8910976475230952281944079 13366464712846428422916119)
          ·
            refine ⟨20049697069269642634374179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13366464712846428422916119 20049697069269642634374179)
            ·
              refine ⟨30074545603904463951561269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20049697069269642634374179 30074545603904463951561269)
              ·
                refine ⟨2819488650366043495458869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30074545603904463951561269 2819488650366043495458869)
                ·
                  refine ⟨264327060971816577699269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819488650366043495458869 264327060971816577699269)
                  ·
                    refine ⟨49561323932215608318613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264327060971816577699269 49561323932215608318613)
                    ·
                      rfl

theorem cell23_289561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_289561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289561 prefixEnd_289561 := by exact prefixLift 289561
  have htrace : WordTrace (prefixWord ++ tailWord_289561) baseStart_289561 baseEnd_289561 := by
    simpa [prefixWord, tailWord_289561, baseEnd_289561] using wordTrace_append hprefix tailTrace_289561
  have hstable : (prefixWord ++ tailWord_289561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289561).length < 2 ^ (prefixWord ++ tailWord_289561).sum := by decide
  have hdescent : baseEnd_289561 < baseStart_289561 := by decide
  rcases family_descends (prefixWord ++ tailWord_289561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289591 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 6]
def baseStart_289591 : Nat := 118140960795 + 289591 * 2 ^ 59
def prefixEnd_289591 : Nat := 4983230072969 + 3 ^ 40 * 289591 * 2
def baseEnd_289591 : Nat := 16522152912920189731189

theorem tailTrace_289591 : CollatzResearch.WordTrace tailWord_289591 prefixEnd_289591 16522152912920189731189 := by
  unfold tailWord_289591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10562251493868740050340627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7041500995912493366893751 10562251493868740050340627)
  ·
    refine ⟨15843377240803110075510941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10562251493868740050340627 15843377240803110075510941)
    ·
      refine ⟨5941266465301166278316603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15843377240803110075510941 5941266465301166278316603)
      ·
        refine ⟨8911899697951749417474905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941266465301166278316603 8911899697951749417474905)
        ·
          refine ⟨6683924773463812063106179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8911899697951749417474905 6683924773463812063106179)
          ·
            refine ⟨10025887160195718094659269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6683924773463812063106179 10025887160195718094659269)
            ·
              refine ⟨1879853842536697142748613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10025887160195718094659269 1879853842536697142748613)
              ·
                refine ⟨352472595475630714265365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1879853842536697142748613 352472595475630714265365)
                ·
                  refine ⟨16522152912920189731189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 352472595475630714265365 16522152912920189731189)
                  ·
                    rfl

theorem cell23_289591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 6].length) (baseStart_289591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289591 prefixEnd_289591 := by exact prefixLift 289591
  have htrace : WordTrace (prefixWord ++ tailWord_289591) baseStart_289591 baseEnd_289591 := by
    simpa [prefixWord, tailWord_289591, baseEnd_289591] using wordTrace_append hprefix tailTrace_289591
  have hstable : (prefixWord ++ tailWord_289591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289591).length < 2 ^ (prefixWord ++ tailWord_289591).sum := by decide
  have hdescent : baseEnd_289591 < baseStart_289591 := by decide
  rcases family_descends (prefixWord ++ tailWord_289591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289646 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_289646 : Nat := 118140960795 + 289646 * 2 ^ 59
def prefixEnd_289646 : Nat := 4983230072969 + 3 ^ 40 * 289646 * 2
def baseEnd_289646 : Nat := 49575872550759664130983

theorem tailTrace_289646 : CollatzResearch.WordTrace tailWord_289646 prefixEnd_289646 49575872550759664130983 := by
  unfold tailWord_289646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320532188583685555449099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7042838339112989629061861 1320532188583685555449099)
  ·
    refine ⟨1980798282875528333173649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320532188583685555449099 1980798282875528333173649)
    ·
      refine ⟨1485598712156646249880237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1980798282875528333173649 1485598712156646249880237)
      ·
        refine ⟨557099517058742343705089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1485598712156646249880237 557099517058742343705089)
        ·
          refine ⟨417824637794056757778817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557099517058742343705089 417824637794056757778817)
          ·
            refine ⟨313368478345542568334113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417824637794056757778817 313368478345542568334113)
            ·
              refine ⟨235026358759156926250585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313368478345542568334113 235026358759156926250585)
              ·
                refine ⟨176269769069367694687939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235026358759156926250585 176269769069367694687939)
                ·
                  refine ⟨264404653604051542031909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176269769069367694687939 264404653604051542031909)
                  ·
                    refine ⟨49575872550759664130983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264404653604051542031909 49575872550759664130983)
                    ·
                      rfl

theorem cell23_289646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_289646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289646 prefixEnd_289646 := by exact prefixLift 289646
  have htrace : WordTrace (prefixWord ++ tailWord_289646) baseStart_289646 baseEnd_289646 := by
    simpa [prefixWord, tailWord_289646, baseEnd_289646] using wordTrace_append hprefix tailTrace_289646
  have hstable : (prefixWord ++ tailWord_289646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289646).length < 2 ^ (prefixWord ++ tailWord_289646).sum := by decide
  have hdescent : baseEnd_289646 < baseStart_289646 := by decide
  rcases family_descends (prefixWord ++ tailWord_289646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289658 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2]
def baseStart_289658 : Nat := 118140960795 + 289658 * 2 ^ 59
def prefixEnd_289658 : Nat := 4983230072969 + 3 ^ 40 * 289658 * 2
def baseEnd_289658 : Nat := 148733779420132945442893

theorem tailTrace_289658 : CollatzResearch.WordTrace tailWord_289658 prefixEnd_289658 148733779420132945442893 := by
  unfold tailWord_289658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641173796156502623257407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7043130123084006995353085 2641173796156502623257407)
  ·
    refine ⟨3961760694234753934886111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2641173796156502623257407 3961760694234753934886111)
    ·
      refine ⟨5942641041352130902329167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3961760694234753934886111 5942641041352130902329167)
      ·
        refine ⟨8913961562028196353493751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5942641041352130902329167 8913961562028196353493751)
        ·
          refine ⟨13370942343042294530240627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8913961562028196353493751 13370942343042294530240627)
          ·
            refine ⟨20056413514563441795360941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13370942343042294530240627 20056413514563441795360941)
            ·
              refine ⟨7521155067961290673260353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20056413514563441795360941 7521155067961290673260353)
              ·
                refine ⟨5640866300970968004945265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7521155067961290673260353 5640866300970968004945265)
                ·
                  refine ⟨4230649725728226003708949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5640866300970968004945265 4230649725728226003708949)
                  ·
                    refine ⟨198311705893510593923857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4230649725728226003708949 198311705893510593923857)
                    ·
                      refine ⟨148733779420132945442893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198311705893510593923857 148733779420132945442893)
                      ·
                        rfl

theorem cell23_289658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_289658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289658 prefixEnd_289658 := by exact prefixLift 289658
  have htrace : WordTrace (prefixWord ++ tailWord_289658) baseStart_289658 baseEnd_289658 := by
    simpa [prefixWord, tailWord_289658, baseEnd_289658] using wordTrace_append hprefix tailTrace_289658
  have hstable : (prefixWord ++ tailWord_289658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289658).length < 2 ^ (prefixWord ++ tailWord_289658).sum := by decide
  have hdescent : baseEnd_289658 < baseStart_289658 := by decide
  rcases family_descends (prefixWord ++ tailWord_289658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289668 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_289668 : Nat := 118140960795 + 289668 * 2 ^ 59
def prefixEnd_289668 : Nat := 4983230072969 + 3 ^ 40 * 289668 * 2
def baseEnd_289668 : Nat := 49579638075559302105949

theorem tailTrace_289668 : CollatzResearch.WordTrace tailWord_289668 prefixEnd_289668 49579638075559302105949 := by
  unfold tailWord_289668
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282529957294891100446829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7043373276393188133929105 5282529957294891100446829)
  ·
    refine ⟨1980948733985584162667561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5282529957294891100446829 1980948733985584162667561)
    ·
      refine ⟨1485711550489188122000671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1980948733985584162667561 1485711550489188122000671)
      ·
        refine ⟨2228567325733782183001007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485711550489188122000671 2228567325733782183001007)
        ·
          refine ⟨3342850988600673274501511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228567325733782183001007 3342850988600673274501511)
          ·
            refine ⟨5014276482901009911752267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342850988600673274501511 5014276482901009911752267)
            ·
              refine ⟨7521414724351514867628401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014276482901009911752267 7521414724351514867628401)
              ·
                refine ⟨5641061043263636150721301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7521414724351514867628401 5641061043263636150721301)
                ·
                  refine ⟨264424736402982944565061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5641061043263636150721301 264424736402982944565061)
                  ·
                    refine ⟨49579638075559302105949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264424736402982944565061 49579638075559302105949)
                    ·
                      rfl

theorem cell23_289668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_289668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289668 prefixEnd_289668 := by exact prefixLift 289668
  have htrace : WordTrace (prefixWord ++ tailWord_289668) baseStart_289668 baseEnd_289668 := by
    simpa [prefixWord, tailWord_289668, baseEnd_289668] using wordTrace_append hprefix tailTrace_289668
  have hstable : (prefixWord ++ tailWord_289668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289668).length < 2 ^ (prefixWord ++ tailWord_289668).sum := by decide
  have hdescent : baseEnd_289668 < baseStart_289668 := by decide
  rcases family_descends (prefixWord ++ tailWord_289668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289675 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 5, 2, 2]
def baseStart_289675 : Nat := 118140960795 + 289675 * 2 ^ 59
def prefixEnd_289675 : Nat := 4983230072969 + 3 ^ 40 * 289675 * 2
def baseEnd_289675 : Nat := 148742508591259378930315

theorem tailTrace_289675 : CollatzResearch.WordTrace tailWord_289675 prefixEnd_289675 148742508591259378930315 := by
  unfold tailWord_289675
  simp only [CollatzResearch.WordTrace]
  refine ⟨10565315225564422396398479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7043543483709614930932319 10565315225564422396398479)
  ·
    refine ⟨15847972838346633594597719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10565315225564422396398479 15847972838346633594597719)
    ·
      refine ⟨23771959257519950391896579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15847972838346633594597719 23771959257519950391896579)
      ·
        refine ⟨35657938886279925587844869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23771959257519950391896579 35657938886279925587844869)
        ·
          refine ⟨6685863541177486047720913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35657938886279925587844869 6685863541177486047720913)
          ·
            refine ⟨5014397655883114535790685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6685863541177486047720913 5014397655883114535790685)
            ·
              refine ⟨1880399120956167950921507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5014397655883114535790685 1880399120956167950921507)
              ·
                refine ⟨2820598681434251926382261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880399120956167950921507 2820598681434251926382261)
                ·
                  refine ⟨264431126384461118098337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820598681434251926382261 264431126384461118098337)
                  ·
                    refine ⟨198323344788345838573753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264431126384461118098337 198323344788345838573753)
                    ·
                      refine ⟨148742508591259378930315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198323344788345838573753 148742508591259378930315)
                      ·
                        rfl

theorem cell23_289675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 2, 2].length) (baseStart_289675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289675 prefixEnd_289675 := by exact prefixLift 289675
  have htrace : WordTrace (prefixWord ++ tailWord_289675) baseStart_289675 baseEnd_289675 := by
    simpa [prefixWord, tailWord_289675, baseEnd_289675] using wordTrace_append hprefix tailTrace_289675
  have hstable : (prefixWord ++ tailWord_289675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289675).length < 2 ^ (prefixWord ++ tailWord_289675).sum := by decide
  have hdescent : baseEnd_289675 < baseStart_289675 := by decide
  rcases family_descends (prefixWord ++ tailWord_289675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289692 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_289692 : Nat := 118140960795 + 289692 * 2 ^ 59
def prefixEnd_289692 : Nat := 4983230072969 + 3 ^ 40 * 289692 * 2
def baseEnd_289692 : Nat := 148751237762385812417737

theorem tailTrace_289692 : CollatzResearch.WordTrace tailWord_289692 prefixEnd_289692 148751237762385812417737 := by
  unfold tailWord_289692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282967633251417149883665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7043956844335222866511553 5282967633251417149883665)
  ·
    refine ⟨3962225724938562862412749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5282967633251417149883665 3962225724938562862412749)
    ·
      refine ⟨1485834646851961073404781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3962225724938562862412749 1485834646851961073404781)
      ·
        refine ⟨557187992569485402526793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1485834646851961073404781 557187992569485402526793)
        ·
          refine ⟨417890994427114051895095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557187992569485402526793 417890994427114051895095)
          ·
            refine ⟨626836491640671077842643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417890994427114051895095 626836491640671077842643)
            ·
              refine ⟨940254737461006616763965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626836491640671077842643 940254737461006616763965)
              ·
                refine ⟨352595526547877481286487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940254737461006616763965 352595526547877481286487)
                ·
                  refine ⟨528893289821816221929731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352595526547877481286487 528893289821816221929731)
                  ·
                    refine ⟨793339934732724332894597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 528893289821816221929731 793339934732724332894597)
                    ·
                      refine ⟨148751237762385812417737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 793339934732724332894597 148751237762385812417737)
                      ·
                        rfl

theorem cell23_289692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_289692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289692 prefixEnd_289692 := by exact prefixLift 289692
  have htrace : WordTrace (prefixWord ++ tailWord_289692) baseStart_289692 baseEnd_289692 := by
    simpa [prefixWord, tailWord_289692, baseEnd_289692] using wordTrace_append hprefix tailTrace_289692
  have hstable : (prefixWord ++ tailWord_289692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289692).length < 2 ^ (prefixWord ++ tailWord_289692).sum := by decide
  have hdescent : baseEnd_289692 < baseStart_289692 := by decide
  rcases family_descends (prefixWord ++ tailWord_289692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289698 : List Nat := [3, 3, 1, 2, 2, 2, 10]
def baseStart_289698 : Nat := 118140960795 + 289698 * 2 ^ 59
def prefixEnd_289698 : Nat := 4983230072969 + 3 ^ 40 * 289698 * 2
def baseEnd_289698 : Nat := 1836473069707565295589

theorem tailTrace_289698 : CollatzResearch.WordTrace tailWord_289698 prefixEnd_289698 1836473069707565295589 := by
  unfold tailWord_289698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641538526120274331121437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7044102736320731549657165 2641538526120274331121437)
  ·
    refine ⟨990576947295102874170539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2641538526120274331121437 990576947295102874170539)
    ·
      refine ⟨1485865420942654311255809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990576947295102874170539 1485865420942654311255809)
      ·
        refine ⟨1114399065706990733441857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1485865420942654311255809 1114399065706990733441857)
        ·
          refine ⟨835799299280243050081393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114399065706990733441857 835799299280243050081393)
          ·
            refine ⟨626849474460182287561045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835799299280243050081393 626849474460182287561045)
            ·
              refine ⟨1836473069707565295589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 626849474460182287561045 1836473069707565295589)
              ·
                rfl

theorem cell23_289698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 10].length) (baseStart_289698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289698 prefixEnd_289698 := by exact prefixLift 289698
  have htrace : WordTrace (prefixWord ++ tailWord_289698) baseStart_289698 baseEnd_289698 := by
    simpa [prefixWord, tailWord_289698, baseEnd_289698] using wordTrace_append hprefix tailTrace_289698
  have hstable : (prefixWord ++ tailWord_289698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289698).length < 2 ^ (prefixWord ++ tailWord_289698).sum := by decide
  have hdescent : baseEnd_289698 < baseStart_289698 := by decide
  rcases family_descends (prefixWord ++ tailWord_289698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289701 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_289701 : Nat := 118140960795 + 289701 * 2 ^ 59
def prefixEnd_289701 : Nat := 4983230072969 + 3 ^ 40 * 289701 * 2
def baseEnd_289701 : Nat := 148755859088276277205195

theorem tailTrace_289701 : CollatzResearch.WordTrace tailWord_289701 prefixEnd_289701 148755859088276277205195 := by
  unfold tailWord_289701
  simp only [CollatzResearch.WordTrace]
  refine ⟨10566263523470228836844957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7044175682313485891229971 10566263523470228836844957)
  ·
    refine ⟨3962348821301335813816859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10566263523470228836844957 3962348821301335813816859)
    ·
      refine ⟨5943523231952003720725289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962348821301335813816859 5943523231952003720725289)
      ·
        refine ⟨4457642423964002790543967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5943523231952003720725289 4457642423964002790543967)
        ·
          refine ⟨6686463635946004185815951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457642423964002790543967 6686463635946004185815951)
          ·
            refine ⟨10029695453919006278723927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686463635946004185815951 10029695453919006278723927)
            ·
              refine ⟨15044543180878509418085891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10029695453919006278723927 15044543180878509418085891)
              ·
                refine ⟨22566814771317764127128837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15044543180878509418085891 22566814771317764127128837)
                ·
                  refine ⟨4231277769622080773836657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22566814771317764127128837 4231277769622080773836657)
                  ·
                    refine ⟨3173458327216560580377493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4231277769622080773836657 3173458327216560580377493)
                    ·
                      refine ⟨148755859088276277205195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3173458327216560580377493 148755859088276277205195)
                      ·
                        rfl

theorem cell23_289701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_289701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289701 prefixEnd_289701 := by exact prefixLift 289701
  have htrace : WordTrace (prefixWord ++ tailWord_289701) baseStart_289701 baseEnd_289701 := by
    simpa [prefixWord, tailWord_289701, baseEnd_289701] using wordTrace_append hprefix tailTrace_289701
  have hstable : (prefixWord ++ tailWord_289701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289701).length < 2 ^ (prefixWord ++ tailWord_289701).sum := by decide
  have hdescent : baseEnd_289701 < baseStart_289701 := by decide
  rcases family_descends (prefixWord ++ tailWord_289701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289711 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 2, 7]
def baseStart_289711 : Nat := 118140960795 + 289711 * 2 ^ 59
def prefixEnd_289711 : Nat := 4983230072969 + 3 ^ 40 * 289711 * 2
def baseEnd_289711 : Nat := 49586997964940412693383

theorem tailTrace_289711 : CollatzResearch.WordTrace tailWord_289711 prefixEnd_289711 49586997964940412693383 := by
  unfold tailWord_289711
  simp only [CollatzResearch.WordTrace]
  refine ⟨10566628253434000544708987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7044418835622667029805991 10566628253434000544708987)
  ·
    refine ⟨15849942380151000817063481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10566628253434000544708987 15849942380151000817063481)
    ·
      refine ⟨11887456785113250612797611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15849942380151000817063481 11887456785113250612797611)
      ·
        refine ⟨17831185177669875919196417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11887456785113250612797611 17831185177669875919196417)
        ·
          refine ⟨13373388883252406939397313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17831185177669875919196417 13373388883252406939397313)
          ·
            refine ⟨10030041662439305204547985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13373388883252406939397313 10030041662439305204547985)
            ·
              refine ⟨7522531246829478903410989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10030041662439305204547985 7522531246829478903410989)
              ·
                refine ⟨2820949217561054588779121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7522531246829478903410989 2820949217561054588779121)
                ·
                  refine ⟨2115711913170790941584341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820949217561054588779121 2115711913170790941584341)
                  ·
                    refine ⟨49586997964940412693383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2115711913170790941584341 49586997964940412693383)
                    ·
                      rfl

theorem cell23_289711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_289711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289711 prefixEnd_289711 := by exact prefixLift 289711
  have htrace : WordTrace (prefixWord ++ tailWord_289711) baseStart_289711 baseEnd_289711 := by
    simpa [prefixWord, tailWord_289711, baseEnd_289711] using wordTrace_append hprefix tailTrace_289711
  have hstable : (prefixWord ++ tailWord_289711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289711).length < 2 ^ (prefixWord ++ tailWord_289711).sum := by decide
  have hdescent : baseEnd_289711 < baseStart_289711 := by decide
  rcases family_descends (prefixWord ++ tailWord_289711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289735 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_289735 : Nat := 118140960795 + 289735 * 2 ^ 59
def prefixEnd_289735 : Nat := 4983230072969 + 3 ^ 40 * 289735 * 2
def baseEnd_289735 : Nat := 148773317430529144180039

theorem tailTrace_289735 : CollatzResearch.WordTrace tailWord_289735 prefixEnd_289735 148773317430529144180039 := by
  unfold tailWord_289735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10567503605347052643582659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7045002403564701762388439 10567503605347052643582659)
  ·
    refine ⟨15851255408020578965373989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10567503605347052643582659 15851255408020578965373989)
    ·
      refine ⟨2972110389003858556007623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15851255408020578965373989 2972110389003858556007623)
      ·
        refine ⟨4458165583505787834011435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972110389003858556007623 4458165583505787834011435)
        ·
          refine ⟨6687248375258681751017153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458165583505787834011435 6687248375258681751017153)
          ·
            refine ⟨5015436281444011313262865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6687248375258681751017153 5015436281444011313262865)
            ·
              refine ⟨3761577211083008484947149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5015436281444011313262865 3761577211083008484947149)
              ·
                refine ⟨1410591454156128181855181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3761577211083008484947149 1410591454156128181855181)
                ·
                  refine ⟨528971795308548068195693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1410591454156128181855181 528971795308548068195693)
                  ·
                    refine ⟨198364423240705525573385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 528971795308548068195693 198364423240705525573385)
                    ·
                      refine ⟨148773317430529144180039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198364423240705525573385 148773317430529144180039)
                      ·
                        rfl

theorem cell23_289735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_289735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289735 prefixEnd_289735 := by exact prefixLift 289735
  have htrace : WordTrace (prefixWord ++ tailWord_289735) baseStart_289735 baseEnd_289735 := by
    simpa [prefixWord, tailWord_289735, baseEnd_289735] using wordTrace_append hprefix tailTrace_289735
  have hstable : (prefixWord ++ tailWord_289735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289735).length < 2 ^ (prefixWord ++ tailWord_289735).sum := by decide
  have hdescent : baseEnd_289735 < baseStart_289735 := by decide
  rcases family_descends (prefixWord ++ tailWord_289735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289752 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 1, 3, 2]
def baseStart_289752 : Nat := 118140960795 + 289752 * 2 ^ 59
def prefixEnd_289752 : Nat := 4983230072969 + 3 ^ 40 * 289752 * 2
def baseEnd_289752 : Nat := 148782046601655577667461

theorem tailTrace_289752 : CollatzResearch.WordTrace tailWord_289752 prefixEnd_289752 148782046601655577667461 := by
  unfold tailWord_289752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284061823142732273475755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7045415764190309697967673 5284061823142732273475755)
  ·
    refine ⟨7926092734714098410213633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5284061823142732273475755 7926092734714098410213633)
    ·
      refine ⟨5944569551035573807660225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7926092734714098410213633 5944569551035573807660225)
      ·
        refine ⟨4458427163276680355745169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5944569551035573807660225 4458427163276680355745169)
        ·
          refine ⟨3343820372457510266808877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4458427163276680355745169 3343820372457510266808877)
          ·
            refine ⟨1253932639671566350053329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3343820372457510266808877 1253932639671566350053329)
            ·
              refine ⟨940449479753674762539997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253932639671566350053329 940449479753674762539997)
              ·
                refine ⟨352668554907628035952499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940449479753674762539997 352668554907628035952499)
                ·
                  refine ⟨529002832361442053928749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352668554907628035952499 529002832361442053928749)
                  ·
                    refine ⟨198376062135540770223281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 529002832361442053928749 198376062135540770223281)
                    ·
                      refine ⟨148782046601655577667461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198376062135540770223281 148782046601655577667461)
                      ·
                        rfl

theorem cell23_289752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_289752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289752 prefixEnd_289752 := by exact prefixLift 289752
  have htrace : WordTrace (prefixWord ++ tailWord_289752) baseStart_289752 baseEnd_289752 := by
    simpa [prefixWord, tailWord_289752, baseEnd_289752] using wordTrace_append hprefix tailTrace_289752
  have hstable : (prefixWord ++ tailWord_289752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289752).length < 2 ^ (prefixWord ++ tailWord_289752).sum := by decide
  have hdescent : baseEnd_289752 < baseStart_289752 := by decide
  rcases family_descends (prefixWord ++ tailWord_289752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289780 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_289780 : Nat := 118140960795 + 289780 * 2 ^ 59
def prefixEnd_289780 : Nat := 4983230072969 + 3 ^ 40 * 289780 * 2
def baseEnd_289780 : Nat := 148796424059981468117333

theorem tailTrace_289780 : CollatzResearch.WordTrace tailWord_289780 prefixEnd_289780 148796424059981468117333 := by
  unfold tailWord_289780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284572445092012664485397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7046096593456016885980529 5284572445092012664485397)
  ·
    refine ⟨247714333363688093647753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5284572445092012664485397 247714333363688093647753)
    ·
      refine ⟨185785750022766070235815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247714333363688093647753 185785750022766070235815)
      ·
        refine ⟨278678625034149105353723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185785750022766070235815 278678625034149105353723)
        ·
          refine ⟨418017937551223658030585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278678625034149105353723 418017937551223658030585)
          ·
            refine ⟨313513453163417743522939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418017937551223658030585 313513453163417743522939)
            ·
              refine ⟨470270179745126615284409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313513453163417743522939 470270179745126615284409)
              ·
                refine ⟨352702634808844961463307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470270179745126615284409 352702634808844961463307)
                ·
                  refine ⟨529053952213267442194961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352702634808844961463307 529053952213267442194961)
                  ·
                    refine ⟨396790464159950581646221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 529053952213267442194961 396790464159950581646221)
                    ·
                      refine ⟨148796424059981468117333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 396790464159950581646221 148796424059981468117333)
                      ·
                        rfl

theorem cell23_289780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_289780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289780 prefixEnd_289780 := by exact prefixLift 289780
  have htrace : WordTrace (prefixWord ++ tailWord_289780) baseStart_289780 baseEnd_289780 := by
    simpa [prefixWord, tailWord_289780, baseEnd_289780] using wordTrace_append hprefix tailTrace_289780
  have hstable : (prefixWord ++ tailWord_289780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289780).length < 2 ^ (prefixWord ++ tailWord_289780).sum := by decide
  have hdescent : baseEnd_289780 < baseStart_289780 := by decide
  rcases family_descends (prefixWord ++ tailWord_289780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289852 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_289852 : Nat := 118140960795 + 289852 * 2 ^ 59
def prefixEnd_289852 : Nat := 4983230072969 + 3 ^ 40 * 289852 * 2
def baseEnd_289852 : Nat := 49611131555701728805667

theorem tailTrace_289852 : CollatzResearch.WordTrace tailWord_289852 prefixEnd_289852 49611131555701728805667 := by
  unfold tailWord_289852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285885472961590812795905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7047847297282121083727873 5285885472961590812795905)
  ·
    refine ⟨3964414104721193109596929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5285885472961590812795905 3964414104721193109596929)
    ·
      refine ⟨2973310578540894832197697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3964414104721193109596929 2973310578540894832197697)
      ·
        refine ⟨2229982933905671124148273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2973310578540894832197697 2229982933905671124148273)
        ·
          refine ⟨1672487200429253343111205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229982933905671124148273 1672487200429253343111205)
          ·
            refine ⟨313591350080485001833351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1672487200429253343111205 313591350080485001833351)
            ·
              refine ⟨470387025120727502750027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313591350080485001833351 470387025120727502750027)
              ·
                refine ⟨705580537681091254125041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470387025120727502750027 705580537681091254125041)
                ·
                  refine ⟨529185403260818440593781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705580537681091254125041 529185403260818440593781)
                  ·
                    refine ⟨49611131555701728805667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 529185403260818440593781 49611131555701728805667)
                    ·
                      rfl

theorem cell23_289852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_289852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289852 prefixEnd_289852 := by exact prefixLift 289852
  have htrace : WordTrace (prefixWord ++ tailWord_289852) baseStart_289852 baseEnd_289852 := by
    simpa [prefixWord, tailWord_289852, baseEnd_289852] using wordTrace_append hprefix tailTrace_289852
  have hstable : (prefixWord ++ tailWord_289852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289852).length < 2 ^ (prefixWord ++ tailWord_289852).sum := by decide
  have hdescent : baseEnd_289852 < baseStart_289852 := by decide
  rcases family_descends (prefixWord ++ tailWord_289852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289855 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 6, 2]
def baseStart_289855 : Nat := 118140960795 + 289855 * 2 ^ 59
def prefixEnd_289855 : Nat := 4983230072969 + 3 ^ 40 * 289855 * 2
def baseEnd_289855 : Nat := 148834935109068674679487

theorem tailTrace_289855 : CollatzResearch.WordTrace tailWord_289855 prefixEnd_289855 148834935109068674679487 := by
  unfold tailWord_289855
  simp only [CollatzResearch.WordTrace]
  refine ⟨10571880364912313137951019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7047920243274875425300679 10571880364912313137951019)
  ·
    refine ⟨15857820547368469706926529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10571880364912313137951019 15857820547368469706926529)
    ·
      refine ⟨11893365410526352280194897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15857820547368469706926529 11893365410526352280194897)
      ·
        refine ⟨8920024057894764210146173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11893365410526352280194897 8920024057894764210146173)
        ·
          refine ⟨3345009021710536578804815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8920024057894764210146173 3345009021710536578804815)
          ·
            refine ⟨5017513532565804868207223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345009021710536578804815 5017513532565804868207223)
            ·
              refine ⟨7526270298848707302310835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017513532565804868207223 7526270298848707302310835)
              ·
                refine ⟨11289405448273060953466253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526270298848707302310835 11289405448273060953466253)
                ·
                  refine ⟨4233527043102397857549845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11289405448273060953466253 4233527043102397857549845)
                  ·
                    refine ⟨198446580145424899572649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4233527043102397857549845 198446580145424899572649)
                    ·
                      refine ⟨148834935109068674679487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198446580145424899572649 148834935109068674679487)
                      ·
                        rfl

theorem cell23_289855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_289855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289855 prefixEnd_289855 := by exact prefixLift 289855
  have htrace : WordTrace (prefixWord ++ tailWord_289855) baseStart_289855 baseEnd_289855 := by
    simpa [prefixWord, tailWord_289855, baseEnd_289855] using wordTrace_append hprefix tailTrace_289855
  have hstable : (prefixWord ++ tailWord_289855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289855).length < 2 ^ (prefixWord ++ tailWord_289855).sum := by decide
  have hdescent : baseEnd_289855 < baseStart_289855 := by decide
  rcases family_descends (prefixWord ++ tailWord_289855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289939 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 1, 1, 3]
def baseStart_289939 : Nat := 118140960795 + 289939 * 2 ^ 59
def prefixEnd_289939 : Nat := 4983230072969 + 3 ^ 40 * 289939 * 2
def baseEnd_289939 : Nat := 148878067484046346029101

theorem tailTrace_289939 : CollatzResearch.WordTrace tailWord_289939 prefixEnd_289939 148878067484046346029101 := by
  unfold tailWord_289939
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574944096607995484008871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7049962731071996989339247 10574944096607995484008871)
  ·
    refine ⟨15862416144911993226013307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10574944096607995484008871 15862416144911993226013307)
    ·
      refine ⟨23793624217367989839019961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15862416144911993226013307 23793624217367989839019961)
      ·
        refine ⟨17845218163025992379264971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23793624217367989839019961 17845218163025992379264971)
        ·
          refine ⟨26767827244538988568897457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17845218163025992379264971 26767827244538988568897457)
          ·
            refine ⟨20075870433404241426673093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26767827244538988568897457 20075870433404241426673093)
            ·
              refine ⟨3764225706263295267501205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20075870433404241426673093 3764225706263295267501205)
              ·
                refine ⟨176448079981091965664119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3764225706263295267501205 176448079981091965664119)
                ·
                  refine ⟨264672119971637948496179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176448079981091965664119 264672119971637948496179)
                  ·
                    refine ⟨397008179957456922744269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 264672119971637948496179 397008179957456922744269)
                    ·
                      refine ⟨148878067484046346029101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397008179957456922744269 148878067484046346029101)
                      ·
                        rfl

theorem cell23_289939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 1, 3].length) (baseStart_289939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289939 prefixEnd_289939 := by exact prefixLift 289939
  have htrace : WordTrace (prefixWord ++ tailWord_289939) baseStart_289939 baseEnd_289939 := by
    simpa [prefixWord, tailWord_289939, baseEnd_289939] using wordTrace_append hprefix tailTrace_289939
  have hstable : (prefixWord ++ tailWord_289939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289939).length < 2 ^ (prefixWord ++ tailWord_289939).sum := by decide
  have hdescent : baseEnd_289939 < baseStart_289939 := by decide
  rcases family_descends (prefixWord ++ tailWord_289939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289959 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 1, 5]
def baseStart_289959 : Nat := 118140960795 + 289959 * 2 ^ 59
def prefixEnd_289959 : Nat := 4983230072969 + 3 ^ 40 * 289959 * 2
def baseEnd_289959 : Nat := 49629445699045422593003

theorem tailTrace_289959 : CollatzResearch.WordTrace tailWord_289959 prefixEnd_289959 49629445699045422593003 := by
  unfold tailWord_289959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10575673556535538899736931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7050449037690359266491287 10575673556535538899736931)
  ·
    refine ⟨15863510334803308349605397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10575673556535538899736931 15863510334803308349605397)
    ·
      refine ⟨743602046943905078887753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15863510334803308349605397 743602046943905078887753)
      ·
        refine ⟨557701535207928809165815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743602046943905078887753 557701535207928809165815)
        ·
          refine ⟨836552302811893213748723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557701535207928809165815 836552302811893213748723)
          ·
            refine ⟨1254828454217839820623085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836552302811893213748723 1254828454217839820623085)
            ·
              refine ⟨470560670331689932733657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1254828454217839820623085 470560670331689932733657)
              ·
                refine ⟨352920502748767449550243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470560670331689932733657 352920502748767449550243)
                ·
                  refine ⟨529380754123151174325365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352920502748767449550243 529380754123151174325365)
                  ·
                    refine ⟨49629445699045422593003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 529380754123151174325365 49629445699045422593003)
                    ·
                      rfl

theorem cell23_289959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_289959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289959 prefixEnd_289959 := by exact prefixLift 289959
  have htrace : WordTrace (prefixWord ++ tailWord_289959) baseStart_289959 baseEnd_289959 := by
    simpa [prefixWord, tailWord_289959, baseEnd_289959] using wordTrace_append hprefix tailTrace_289959
  have hstable : (prefixWord ++ tailWord_289959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289959).length < 2 ^ (prefixWord ++ tailWord_289959).sum := by decide
  have hdescent : baseEnd_289959 < baseStart_289959 := by decide
  rcases family_descends (prefixWord ++ tailWord_289959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290006 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_290006 : Nat := 118140960795 + 290006 * 2 ^ 59
def prefixEnd_290006 : Nat := 4983230072969 + 3 ^ 40 * 290006 * 2
def baseEnd_290006 : Nat := 49637490229299194630431

theorem tailTrace_290006 : CollatzResearch.WordTrace tailWord_290006 prefixEnd_290006 49637490229299194630431 := by
  unfold tailWord_290006
  simp only [CollatzResearch.WordTrace]
  refine ⟨661086736710329120418617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7051591858243510617798581 661086736710329120418617)
  ·
    refine ⟨495815052532746840313963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 661086736710329120418617 495815052532746840313963)
    ·
      refine ⟨743722578799120260470945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495815052532746840313963 743722578799120260470945)
      ·
        refine ⟨557791934099340195353209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743722578799120260470945 557791934099340195353209)
        ·
          refine ⟨418343950574505146514907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557791934099340195353209 418343950574505146514907)
          ·
            refine ⟨627515925861757719772361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418343950574505146514907 627515925861757719772361)
            ·
              refine ⟨470636944396318289829271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627515925861757719772361 470636944396318289829271)
              ·
                refine ⟨705955416594477434743907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470636944396318289829271 705955416594477434743907)
                ·
                  refine ⟨1058933124891716152115861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705955416594477434743907 1058933124891716152115861)
                  ·
                    refine ⟨49637490229299194630431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1058933124891716152115861 49637490229299194630431)
                    ·
                      rfl

theorem cell23_290006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_290006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290006 prefixEnd_290006 := by exact prefixLift 290006
  have htrace : WordTrace (prefixWord ++ tailWord_290006) baseStart_290006 baseEnd_290006 := by
    simpa [prefixWord, tailWord_290006, baseEnd_290006] using wordTrace_append hprefix tailTrace_290006
  have hstable : (prefixWord ++ tailWord_290006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290006).length < 2 ^ (prefixWord ++ tailWord_290006).sum := by decide
  have hdescent : baseEnd_290006 < baseStart_290006 := by decide
  rcases family_descends (prefixWord ++ tailWord_290006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
