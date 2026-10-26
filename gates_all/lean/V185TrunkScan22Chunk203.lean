import V185TrunkScan22Chunk202

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1809790 : List Nat := [4, 2, 3, 2, 1, 1, 1, 8]
def baseStart_1809790 : Nat := 118140960795 + 1809790 * 2 ^ 59
def prefixEnd_1809790 : Nat := 4983230072969 + 3 ^ 40 * 1809790 * 2
def baseEnd_1809790 : Nat := 68836455829672549777921

theorem tailTrace_1809790 : CollatzResearch.WordTrace tailWord_1809790 prefixEnd_1809790 68836455829672549777921 := by
  unfold tailWord_1809790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251058014180924046174353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44005642742298261579596549 8251058014180924046174353)
  ·
    refine ⟨6188293510635693034630765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8251058014180924046174353 6188293510635693034630765)
    ·
      refine ⟨2320610066488384887986537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6188293510635693034630765 2320610066488384887986537)
      ·
        refine ⟨1740457549866288665989903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2320610066488384887986537 1740457549866288665989903)
        ·
          refine ⟨2610686324799432998984855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740457549866288665989903 2610686324799432998984855)
          ·
            refine ⟨3916029487199149498477283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610686324799432998984855 3916029487199149498477283)
            ·
              refine ⟨5874044230798724247715925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916029487199149498477283 5874044230798724247715925)
              ·
                refine ⟨68836455829672549777921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5874044230798724247715925 68836455829672549777921)
                ·
                  rfl

theorem cell22_1809790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_1809790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809790 prefixEnd_1809790 := by exact prefixLift 1809790
  have htrace : WordTrace (prefixWord ++ tailWord_1809790) baseStart_1809790 baseEnd_1809790 := by
    simpa [prefixWord, tailWord_1809790, baseEnd_1809790] using wordTrace_append hprefix tailTrace_1809790
  have hstable : (prefixWord ++ tailWord_1809790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809790).length < 2 ^ (prefixWord ++ tailWord_1809790).sum := by decide
  have hdescent : baseEnd_1809790 < baseStart_1809790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809848 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_1809848 : Nat := 118140960795 + 1809848 * 2 ^ 59
def prefixEnd_1809848 : Nat := 4983230072969 + 3 ^ 40 * 1809848 * 2
def baseEnd_1809848 : Nat := 619547957052360130051111

theorem tailTrace_1809848 : CollatzResearch.WordTrace tailWord_1809848 prefixEnd_1809848 619547957052360130051111 := by
  unfold tailWord_1809848
  simp only [CollatzResearch.WordTrace]
  refine ⟨33005289773618634137503099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44007053031491512183337465 33005289773618634137503099)
  ·
    refine ⟨49507934660427951206254649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33005289773618634137503099 49507934660427951206254649)
    ·
      refine ⟨37130950995320963404690987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49507934660427951206254649 37130950995320963404690987)
      ·
        refine ⟨55696426492981445107036481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37130950995320963404690987 55696426492981445107036481)
        ·
          refine ⟨41772319869736083830277361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55696426492981445107036481 41772319869736083830277361)
          ·
            refine ⟨31329239902302062872708021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41772319869736083830277361 31329239902302062872708021)
            ·
              refine ⟨2937116240840818394316377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31329239902302062872708021 2937116240840818394316377)
              ·
                refine ⟨2202837180630613795737283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937116240840818394316377 2202837180630613795737283)
                ·
                  refine ⟨3304255770945920693605925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202837180630613795737283 3304255770945920693605925)
                  ·
                    refine ⟨619547957052360130051111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304255770945920693605925 619547957052360130051111)
                    ·
                      rfl

theorem cell22_1809848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_1809848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809848 prefixEnd_1809848 := by exact prefixLift 1809848
  have htrace : WordTrace (prefixWord ++ tailWord_1809848) baseStart_1809848 baseEnd_1809848 := by
    simpa [prefixWord, tailWord_1809848, baseEnd_1809848] using wordTrace_append hprefix tailTrace_1809848
  have hstable : (prefixWord ++ tailWord_1809848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809848).length < 2 ^ (prefixWord ++ tailWord_1809848).sum := by decide
  have hdescent : baseEnd_1809848 < baseStart_1809848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809863 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 4]
def baseStart_1809863 : Nat := 118140960795 + 1809863 * 2 ^ 59
def prefixEnd_1809863 : Nat := 4983230072969 + 3 ^ 40 * 1809863 * 2
def baseEnd_1809863 : Nat := 206517697286301696975355

theorem tailTrace_1809863 : CollatzResearch.WordTrace tailWord_1809863 prefixEnd_1809863 206517697286301696975355 := by
  unfold tailWord_1809863
  simp only [CollatzResearch.WordTrace]
  refine ⟨66011126642182925836802243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44007417761455283891201495 66011126642182925836802243)
  ·
    refine ⟨99016689963274388755203365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66011126642182925836802243 99016689963274388755203365)
    ·
      refine ⟨18565629368113947891600631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99016689963274388755203365 18565629368113947891600631)
      ·
        refine ⟨27848444052170921837400947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18565629368113947891600631 27848444052170921837400947)
        ·
          refine ⟨41772666078256382756101421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27848444052170921837400947 41772666078256382756101421)
          ·
            refine ⟨15664749779346143533538033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41772666078256382756101421 15664749779346143533538033)
            ·
              refine ⟨11748562334509607650153525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15664749779346143533538033 11748562334509607650153525)
              ·
                refine ⟨1101427718860275717201893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11748562334509607650153525 1101427718860275717201893)
                ·
                  refine ⟨206517697286301696975355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101427718860275717201893 206517697286301696975355)
                  ·
                    rfl

theorem cell22_1809863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 4].length) (baseStart_1809863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809863 prefixEnd_1809863 := by exact prefixLift 1809863
  have htrace : WordTrace (prefixWord ++ tailWord_1809863) baseStart_1809863 baseEnd_1809863 := by
    simpa [prefixWord, tailWord_1809863, baseEnd_1809863] using wordTrace_append hprefix tailTrace_1809863
  have hstable : (prefixWord ++ tailWord_1809863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809863).length < 2 ^ (prefixWord ++ tailWord_1809863).sum := by decide
  have hdescent : baseEnd_1809863 < baseStart_1809863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809880 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 4]
def baseStart_1809880 : Nat := 118140960795 + 1809880 * 2 ^ 59
def prefixEnd_1809880 : Nat := 4983230072969 + 3 ^ 40 * 1809880 * 2
def baseEnd_1809880 : Nat := 206519637102107571083671

theorem tailTrace_1809880 : CollatzResearch.WordTrace tailWord_1809880 prefixEnd_1809880 206519637102107571083671 := by
  unfold tailWord_1809880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33005873341560668870085547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44007831122080891826780729 33005873341560668870085547)
  ·
    refine ⟨49508810012341003305128321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33005873341560668870085547 49508810012341003305128321)
    ·
      refine ⟨37131607509255752478846241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49508810012341003305128321 37131607509255752478846241)
      ·
        refine ⟨27848705631941814359134681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37131607509255752478846241 27848705631941814359134681)
        ·
          refine ⟨20886529223956360769351011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27848705631941814359134681 20886529223956360769351011)
          ·
            refine ⟨31329793835934541154026517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20886529223956360769351011 31329793835934541154026517)
            ·
              refine ⟨1468584086059431616594993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31329793835934541154026517 1468584086059431616594993)
              ·
                refine ⟨1101438064544573712446245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468584086059431616594993 1101438064544573712446245)
                ·
                  refine ⟨206519637102107571083671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101438064544573712446245 206519637102107571083671)
                  ·
                    rfl

theorem cell22_1809880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_1809880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809880 prefixEnd_1809880 := by exact prefixLift 1809880
  have htrace : WordTrace (prefixWord ++ tailWord_1809880) baseStart_1809880 baseEnd_1809880 := by
    simpa [prefixWord, tailWord_1809880, baseEnd_1809880] using wordTrace_append hprefix tailTrace_1809880
  have hstable : (prefixWord ++ tailWord_1809880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809880).length < 2 ^ (prefixWord ++ tailWord_1809880).sum := by decide
  have hdescent : baseEnd_1809880 < baseStart_1809880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809895 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1809895 : Nat := 118140960795 + 1809895 * 2 ^ 59
def prefixEnd_1809895 : Nat := 4983230072969 + 3 ^ 40 * 1809895 * 2
def baseEnd_1809895 : Nat := 619564046112867674125967

theorem tailTrace_1809895 : CollatzResearch.WordTrace tailWord_1809895 prefixEnd_1809895 619564046112867674125967 := by
  unfold tailWord_1809895
  simp only [CollatzResearch.WordTrace]
  refine ⟨66012293778066995301967139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44008195852044663534644759 66012293778066995301967139)
  ·
    refine ⟨99018440667100492952950709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66012293778066995301967139 99018440667100492952950709)
    ·
      refine ⟨9282978812540671214339129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99018440667100492952950709 9282978812540671214339129)
      ·
        refine ⟨6962234109405503410754347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9282978812540671214339129 6962234109405503410754347)
        ·
          refine ⟨10443351164108255116131521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962234109405503410754347 10443351164108255116131521)
          ·
            refine ⟨7832513373081191337098641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10443351164108255116131521 7832513373081191337098641)
            ·
              refine ⟨5874385029810893502823981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832513373081191337098641 5874385029810893502823981)
              ·
                refine ⟨2202894386179085063558993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5874385029810893502823981 2202894386179085063558993)
                ·
                  refine ⟨1652170789634313797669245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202894386179085063558993 1652170789634313797669245)
                  ·
                    refine ⟨619564046112867674125967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652170789634313797669245 619564046112867674125967)
                    ·
                      rfl

theorem cell22_1809895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1809895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809895 prefixEnd_1809895 := by exact prefixLift 1809895
  have htrace : WordTrace (prefixWord ++ tailWord_1809895) baseStart_1809895 baseEnd_1809895 := by
    simpa [prefixWord, tailWord_1809895, baseEnd_1809895] using wordTrace_append hprefix tailTrace_1809895
  have hstable : (prefixWord ++ tailWord_1809895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809895).length < 2 ^ (prefixWord ++ tailWord_1809895).sum := by decide
  have hdescent : baseEnd_1809895 < baseStart_1809895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809910 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1809910 : Nat := 118140960795 + 1809910 * 2 ^ 59
def prefixEnd_1809910 : Nat := 4983230072969 + 3 ^ 40 * 1809910 * 2
def baseEnd_1809910 : Nat := 619569180919412635000921

theorem tailTrace_1809910 : CollatzResearch.WordTrace tailWord_1809910 prefixEnd_1809910 619569180919412635000921 := by
  unfold tailWord_1809910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125802554563290803985199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44008560582008435242508789 4125802554563290803985199)
  ·
    refine ⟨6188703831844936205977799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4125802554563290803985199 6188703831844936205977799)
    ·
      refine ⟨9283055747767404308966699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188703831844936205977799 9283055747767404308966699)
      ·
        refine ⟨13924583621651106463450049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9283055747767404308966699 13924583621651106463450049)
        ·
          refine ⟨10443437716238329847587537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13924583621651106463450049 10443437716238329847587537)
          ·
            refine ⟨7832578287178747385690653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10443437716238329847587537 7832578287178747385690653)
            ·
              refine ⟨2937216857692030269633995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7832578287178747385690653 2937216857692030269633995)
              ·
                refine ⟨4405825286538045404450993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937216857692030269633995 4405825286538045404450993)
                ·
                  refine ⟨3304368964903534053338245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4405825286538045404450993 3304368964903534053338245)
                  ·
                    refine ⟨619569180919412635000921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304368964903534053338245 619569180919412635000921)
                    ·
                      rfl

theorem cell22_1809910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1809910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1809910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1809910 prefixEnd_1809910 := by exact prefixLift 1809910
  have htrace : WordTrace (prefixWord ++ tailWord_1809910) baseStart_1809910 baseEnd_1809910 := by
    simpa [prefixWord, tailWord_1809910, baseEnd_1809910] using wordTrace_append hprefix tailTrace_1809910
  have hstable : (prefixWord ++ tailWord_1809910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809910).length < 2 ^ (prefixWord ++ tailWord_1809910).sum := by decide
  have hdescent : baseEnd_1809910 < baseStart_1809910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810045 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1810045 : Nat := 118140960795 + 1810045 * 2 ^ 59
def prefixEnd_1810045 : Nat := 4983230072969 + 3 ^ 40 * 1810045 * 2
def baseEnd_1810045 : Nat := 619615394178317282875507

theorem tailTrace_1810045 : CollatzResearch.WordTrace tailWord_1810045 prefixEnd_1810045 619615394178317282875507 := by
  unfold tailWord_1810045
  simp only [CollatzResearch.WordTrace]
  refine ⟨66017764727523570919927589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44011843151682380613285059 66017764727523570919927589)
  ·
    refine ⟨12378330886410669547486423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66017764727523570919927589 12378330886410669547486423)
    ·
      refine ⟨18567496329616004321229635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12378330886410669547486423 18567496329616004321229635)
      ·
        refine ⟨27851244494424006481844453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18567496329616004321229635 27851244494424006481844453)
        ·
          refine ⟨5222108342704501215345835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27851244494424006481844453 5222108342704501215345835)
          ·
            refine ⟨7833162514056751823018753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222108342704501215345835 7833162514056751823018753)
            ·
              refine ⟨5874871885542563867264065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7833162514056751823018753 5874871885542563867264065)
              ·
                refine ⟨4406153914156922900448049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5874871885542563867264065 4406153914156922900448049)
                ·
                  refine ⟨3304615435617692175336037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406153914156922900448049 3304615435617692175336037)
                  ·
                    refine ⟨619615394178317282875507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304615435617692175336037 619615394178317282875507)
                    ·
                      rfl

theorem cell22_1810045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1810045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810045 prefixEnd_1810045 := by exact prefixLift 1810045
  have htrace : WordTrace (prefixWord ++ tailWord_1810045) baseStart_1810045 baseEnd_1810045 := by
    simpa [prefixWord, tailWord_1810045, baseEnd_1810045] using wordTrace_append hprefix tailTrace_1810045
  have hstable : (prefixWord ++ tailWord_1810045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810045).length < 2 ^ (prefixWord ++ tailWord_1810045).sum := by decide
  have hdescent : baseEnd_1810045 < baseStart_1810045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810049 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 4]
def baseStart_1810049 : Nat := 118140960795 + 1810049 * 2 ^ 59
def prefixEnd_1810049 : Nat := 4983230072969 + 3 ^ 40 * 1810049 * 2
def baseEnd_1810049 : Nat := 206538921153354201925165

theorem tailTrace_1810049 : CollatzResearch.WordTrace tailWord_1810049 prefixEnd_1810049 206538921153354201925165 := by
  unfold tailWord_1810049
  simp only [CollatzResearch.WordTrace]
  refine ⟨66017910619509079603073201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44011940413006053068715467 66017910619509079603073201)
  ·
    refine ⟨49513432964631809702304901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66017910619509079603073201 49513432964631809702304901)
    ·
      refine ⟨9283768680868464319182169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49513432964631809702304901 9283768680868464319182169)
      ·
        refine ⟨6962826510651348239386627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283768680868464319182169 6962826510651348239386627)
        ·
          refine ⟨10444239765977022359079941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962826510651348239386627 10444239765977022359079941)
          ·
            refine ⟨1958294956120691692327489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10444239765977022359079941 1958294956120691692327489)
            ·
              refine ⟨1468721217090518769245617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958294956120691692327489 1468721217090518769245617)
              ·
                refine ⟨1101540912817889076934213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468721217090518769245617 1101540912817889076934213)
                ·
                  refine ⟨206538921153354201925165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101540912817889076934213 206538921153354201925165)
                  ·
                    rfl

theorem cell22_1810049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_1810049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810049 prefixEnd_1810049 := by exact prefixLift 1810049
  have htrace : WordTrace (prefixWord ++ tailWord_1810049) baseStart_1810049 baseEnd_1810049 := by
    simpa [prefixWord, tailWord_1810049, baseEnd_1810049] using wordTrace_append hprefix tailTrace_1810049
  have hstable : (prefixWord ++ tailWord_1810049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810049).length < 2 ^ (prefixWord ++ tailWord_1810049).sum := by decide
  have hdescent : baseEnd_1810049 < baseStart_1810049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810079 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 2, 4]
def baseStart_1810079 : Nat := 118140960795 + 1810079 * 2 ^ 59
def prefixEnd_1810079 : Nat := 4983230072969 + 3 ^ 40 * 1810079 * 2
def baseEnd_1810079 : Nat := 619627033073152527525403

theorem tailTrace_1810079 : CollatzResearch.WordTrace tailWord_1810079 prefixEnd_1810079 619627033073152527525403 := by
  unfold tailWord_1810079
  simp only [CollatzResearch.WordTrace]
  refine ⟨66019004809400394726665291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44012669872933596484443527 66019004809400394726665291)
  ·
    refine ⟨99028507214100592089997937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66019004809400394726665291 99028507214100592089997937)
    ·
      refine ⟨74271380410575444067498453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99028507214100592089997937 74271380410575444067498453)
      ·
        refine ⟨1740735478372861970331995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74271380410575444067498453 1740735478372861970331995)
        ·
          refine ⟨2611103217559292955497993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740735478372861970331995 2611103217559292955497993)
          ·
            refine ⟨1958327413169469716623495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611103217559292955497993 1958327413169469716623495)
            ·
              refine ⟨2937491119754204574935243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958327413169469716623495 2937491119754204574935243)
              ·
                refine ⟨4406236679631306862402865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937491119754204574935243 4406236679631306862402865)
                ·
                  refine ⟨3304677509723480146802149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406236679631306862402865 3304677509723480146802149)
                  ·
                    refine ⟨619627033073152527525403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304677509723480146802149 619627033073152527525403)
                    ·
                      rfl

theorem cell22_1810079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_1810079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810079 prefixEnd_1810079 := by exact prefixLift 1810079
  have htrace : WordTrace (prefixWord ++ tailWord_1810079) baseStart_1810079 baseEnd_1810079 := by
    simpa [prefixWord, tailWord_1810079, baseEnd_1810079] using wordTrace_append hprefix tailTrace_1810079
  have hstable : (prefixWord ++ tailWord_1810079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810079).length < 2 ^ (prefixWord ++ tailWord_1810079).sum := by decide
  have hdescent : baseEnd_1810079 < baseStart_1810079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810105 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 5]
def baseStart_1810105 : Nat := 118140960795 + 1810105 * 2 ^ 59
def prefixEnd_1810105 : Nat := 4983230072969 + 3 ^ 40 * 1810105 * 2
def baseEnd_1810105 : Nat := 206545311134832375458441

theorem tailTrace_1810105 : CollatzResearch.WordTrace tailWord_1810105 prefixEnd_1810105 206545311134832375458441 := by
  unfold tailWord_1810105
  simp only [CollatzResearch.WordTrace]
  refine ⟨66019953107306201167111769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44013302071537467444741179 66019953107306201167111769)
  ·
    refine ⟨49514964830479650875333827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66019953107306201167111769 49514964830479650875333827)
    ·
      refine ⟨74272447245719476313000741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49514964830479650875333827 74272447245719476313000741)
      ·
        refine ⟨13926083858572401808687639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74272447245719476313000741 13926083858572401808687639)
        ·
          refine ⟨20889125787858602713031459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13926083858572401808687639 20889125787858602713031459)
          ·
            refine ⟨31333688681787904069547189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20889125787858602713031459 31333688681787904069547189)
            ·
              refine ⟨2937533313917616006520049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31333688681787904069547189 2937533313917616006520049)
              ·
                refine ⟨2203149985438212004890037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937533313917616006520049 2203149985438212004890037)
                ·
                  refine ⟨206545311134832375458441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2203149985438212004890037 206545311134832375458441)
                  ·
                    rfl

theorem cell22_1810105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_1810105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810105 prefixEnd_1810105 := by exact prefixLift 1810105
  have htrace : WordTrace (prefixWord ++ tailWord_1810105) baseStart_1810105 baseEnd_1810105 := by
    simpa [prefixWord, tailWord_1810105, baseEnd_1810105] using wordTrace_append hprefix tailTrace_1810105
  have hstable : (prefixWord ++ tailWord_1810105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810105).length < 2 ^ (prefixWord ++ tailWord_1810105).sum := by decide
  have hdescent : baseEnd_1810105 < baseStart_1810105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810152 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_1810152 : Nat := 118140960795 + 1810152 * 2 ^ 59
def prefixEnd_1810152 : Nat := 4983230072969 + 3 ^ 40 * 1810152 * 2
def baseEnd_1810152 : Nat := 619652022465004670450179

theorem tailTrace_1810152 : CollatzResearch.WordTrace tailWord_1810152 prefixEnd_1810152 619652022465004670450179 := by
  unfold tailWord_1810152
  simp only [CollatzResearch.WordTrace]
  refine ⟨33010833669067964097036355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44014444892090618796048473 33010833669067964097036355)
  ·
    refine ⟨49516250503601946145554533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33010833669067964097036355 49516250503601946145554533)
    ·
      refine ⟨9284296969425364902291475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49516250503601946145554533 9284296969425364902291475)
      ·
        refine ⟨13926445454138047353437213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9284296969425364902291475 13926445454138047353437213)
        ·
          refine ⟨5222417045301767757538955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13926445454138047353437213 5222417045301767757538955)
          ·
            refine ⟨7833625567952651636308433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222417045301767757538955 7833625567952651636308433)
            ·
              refine ⟨5875219175964488727231325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7833625567952651636308433 5875219175964488727231325)
              ·
                refine ⟨2203207190986683272711747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5875219175964488727231325 2203207190986683272711747)
                ·
                  refine ⟨3304810786480024909067621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203207190986683272711747 3304810786480024909067621)
                  ·
                    refine ⟨619652022465004670450179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304810786480024909067621 619652022465004670450179)
                    ·
                      rfl

theorem cell22_1810152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_1810152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810152 prefixEnd_1810152 := by exact prefixLift 1810152
  have htrace : WordTrace (prefixWord ++ tailWord_1810152) baseStart_1810152 baseEnd_1810152 := by
    simpa [prefixWord, tailWord_1810152, baseEnd_1810152] using wordTrace_append hprefix tailTrace_1810152
  have hstable : (prefixWord ++ tailWord_1810152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810152).length < 2 ^ (prefixWord ++ tailWord_1810152).sum := by decide
  have hdescent : baseEnd_1810152 < baseStart_1810152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810197 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1810197 : Nat := 118140960795 + 1810197 * 2 ^ 59
def prefixEnd_1810197 : Nat := 4983230072969 + 3 ^ 40 * 1810197 * 2
def baseEnd_1810197 : Nat := 619667426884639553075041

theorem tailTrace_1810197 : CollatzResearch.WordTrace tailWord_1810197 prefixEnd_1810197 619667426884639553075041 := by
  unfold tailWord_1810197
  simp only [CollatzResearch.WordTrace]
  refine ⟨66023308622972900879460845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44015539081981933919640563 66023308622972900879460845)
  ·
    refine ⟨24758740733614837829797817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66023308622972900879460845 24758740733614837829797817)
    ·
      refine ⟨18569055550211128372348363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24758740733614837829797817 18569055550211128372348363)
      ·
        refine ⟨27853583325316692558522545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18569055550211128372348363 27853583325316692558522545)
        ·
          refine ⟨20890187493987519418891909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27853583325316692558522545 20890187493987519418891909)
          ·
            refine ⟨3916910155122659891042233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20890187493987519418891909 3916910155122659891042233)
            ·
              refine ⟨2937682616341994918281675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916910155122659891042233 2937682616341994918281675)
              ·
                refine ⟨4406523924512992377422513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937682616341994918281675 4406523924512992377422513)
                ·
                  refine ⟨3304892943384744283066885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406523924512992377422513 3304892943384744283066885)
                  ·
                    refine ⟨619667426884639553075041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304892943384744283066885 619667426884639553075041)
                    ·
                      rfl

theorem cell22_1810197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1810197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810197 prefixEnd_1810197 := by exact prefixLift 1810197
  have htrace : WordTrace (prefixWord ++ tailWord_1810197) baseStart_1810197 baseEnd_1810197 := by
    simpa [prefixWord, tailWord_1810197, baseEnd_1810197] using wordTrace_append hprefix tailTrace_1810197
  have hstable : (prefixWord ++ tailWord_1810197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810197).length < 2 ^ (prefixWord ++ tailWord_1810197).sum := by decide
  have hdescent : baseEnd_1810197 < baseStart_1810197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810225 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1810225 : Nat := 118140960795 + 1810225 * 2 ^ 59
def prefixEnd_1810225 : Nat := 4983230072969 + 3 ^ 40 * 1810225 * 2
def baseEnd_1810225 : Nat := 619677011856856813374955

theorem tailTrace_1810225 : CollatzResearch.WordTrace tailWord_1810225 prefixEnd_1810225 619677011856856813374955 := by
  unfold tailWord_1810225
  simp only [CollatzResearch.WordTrace]
  refine ⟨66024329866871461661480129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44016219911247641107653419 66024329866871461661480129)
  ·
    refine ⟨49518247400153596246110097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66024329866871461661480129 49518247400153596246110097)
    ·
      refine ⟨37138685550115197184582573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49518247400153596246110097 37138685550115197184582573)
      ·
        refine ⟨13927007081293198944218465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37138685550115197184582573 13927007081293198944218465)
        ·
          refine ⟨10445255310969899208163849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13927007081293198944218465 10445255310969899208163849)
          ·
            refine ⟨7833941483227424406122887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10445255310969899208163849 7833941483227424406122887)
            ·
              refine ⟨11750912224841136609184331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833941483227424406122887 11750912224841136609184331)
              ·
                refine ⟨17626368337261704913776497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750912224841136609184331 17626368337261704913776497)
                ·
                  refine ⟨13219776252946278685332373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17626368337261704913776497 13219776252946278685332373)
                  ·
                    refine ⟨619677011856856813374955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13219776252946278685332373 619677011856856813374955)
                    ·
                      rfl

theorem cell22_1810225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1810225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810225 prefixEnd_1810225 := by exact prefixLift 1810225
  have htrace : WordTrace (prefixWord ++ tailWord_1810225) baseStart_1810225 baseEnd_1810225 := by
    simpa [prefixWord, tailWord_1810225, baseEnd_1810225] using wordTrace_append hprefix tailTrace_1810225
  have hstable : (prefixWord ++ tailWord_1810225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810225).length < 2 ^ (prefixWord ++ tailWord_1810225).sum := by decide
  have hdescent : baseEnd_1810225 < baseStart_1810225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810229 : List Nat := [1, 3, 3, 1, 5, 1, 1, 7]
def baseStart_1810229 : Nat := 118140960795 + 1810229 * 2 ^ 59
def prefixEnd_1810229 : Nat := 4983230072969 + 3 ^ 40 * 1810229 * 2
def baseEnd_1810229 : Nat := 68853153459844681808327

theorem tailTrace_1810229 : CollatzResearch.WordTrace tailWord_1810229 prefixEnd_1810229 68853153459844681808327 := by
  unfold tailWord_1810229
  simp only [CollatzResearch.WordTrace]
  refine ⟨66024475758856970344625741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44016317172571313563083827 66024475758856970344625741)
  ·
    refine ⟨24759178409571363879234653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66024475758856970344625741 24759178409571363879234653)
    ·
      refine ⟨9284691903589261454712995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24759178409571363879234653 9284691903589261454712995)
      ·
        refine ⟨13927037855383892182069493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9284691903589261454712995 13927037855383892182069493)
        ·
          refine ⟨1305659798942239892069015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13927037855383892182069493 1305659798942239892069015)
          ·
            refine ⟨1958489698413359838103523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305659798942239892069015 1958489698413359838103523)
            ·
              refine ⟨2937734547620039757155285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958489698413359838103523 2937734547620039757155285)
              ·
                refine ⟨68853153459844681808327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2937734547620039757155285 68853153459844681808327)
                ·
                  rfl

theorem cell22_1810229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 7].length) (baseStart_1810229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810229 prefixEnd_1810229 := by exact prefixLift 1810229
  have htrace : WordTrace (prefixWord ++ tailWord_1810229) baseStart_1810229 baseEnd_1810229 := by
    simpa [prefixWord, tailWord_1810229, baseEnd_1810229] using wordTrace_append hprefix tailTrace_1810229
  have hstable : (prefixWord ++ tailWord_1810229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810229).length < 2 ^ (prefixWord ++ tailWord_1810229).sum := by decide
  have hdescent : baseEnd_1810229 < baseStart_1810229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810246 : List Nat := [6, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1810246 : Nat := 118140960795 + 1810246 * 2 ^ 59
def prefixEnd_1810246 : Nat := 4983230072969 + 3 ^ 40 * 1810246 * 2
def baseEnd_1810246 : Nat := 68853800065113306511099

theorem tailTrace_1810246 : CollatzResearch.WordTrace tailWord_1810246 prefixEnd_1810246 68853800065113306511099 := by
  unfold tailWord_1810246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063284243743605695249831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44016730533196921498663061 2063284243743605695249831)
  ·
    refine ⟨3094926365615408542874747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063284243743605695249831 3094926365615408542874747)
    ·
      refine ⟨4642389548423112814312121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094926365615408542874747 4642389548423112814312121)
      ·
        refine ⟨3481792161317334610734091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642389548423112814312121 3481792161317334610734091)
        ·
          refine ⟨5222688241976001916101137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481792161317334610734091 5222688241976001916101137)
          ·
            refine ⟨3917016181482001437075853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5222688241976001916101137 3917016181482001437075853)
            ·
              refine ⟨1468881068055750538903445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3917016181482001437075853 1468881068055750538903445)
              ·
                refine ⟨68853800065113306511099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1468881068055750538903445 68853800065113306511099)
                ·
                  rfl

theorem cell22_1810246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1810246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810246 prefixEnd_1810246 := by exact prefixLift 1810246
  have htrace : WordTrace (prefixWord ++ tailWord_1810246) baseStart_1810246 baseEnd_1810246 := by
    simpa [prefixWord, tailWord_1810246, baseEnd_1810246] using wordTrace_append hprefix tailTrace_1810246
  have hstable : (prefixWord ++ tailWord_1810246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810246).length < 2 ^ (prefixWord ++ tailWord_1810246).sum := by decide
  have hdescent : baseEnd_1810246 < baseStart_1810246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810261 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1810261 : Nat := 118140960795 + 1810261 * 2 ^ 59
def prefixEnd_1810261 : Nat := 4983230072969 + 3 ^ 40 * 1810261 * 2
def baseEnd_1810261 : Nat := 619689335392564719474845

theorem tailTrace_1810261 : CollatzResearch.WordTrace tailWord_1810261 prefixEnd_1810261 619689335392564719474845 := by
  unfold tailWord_1810261
  simp only [CollatzResearch.WordTrace]
  refine ⟨66025642894741039809790637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44017095263160693206527091 66025642894741039809790637)
  ·
    refine ⟨24759616085527889928671489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66025642894741039809790637 24759616085527889928671489)
    ·
      refine ⟨18569712064145917446503617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24759616085527889928671489 18569712064145917446503617)
      ·
        refine ⟨13927284048109438084877713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18569712064145917446503617 13927284048109438084877713)
        ·
          refine ⟨10445463036082078563658285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13927284048109438084877713 10445463036082078563658285)
          ·
            refine ⟨3917048638530779461371857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10445463036082078563658285 3917048638530779461371857)
            ·
              refine ⟨2937786478898084596028893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917048638530779461371857 2937786478898084596028893)
              ·
                refine ⟨1101669929586781723510835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2937786478898084596028893 1101669929586781723510835)
                ·
                  refine ⟨1652504894380172585266253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101669929586781723510835 1652504894380172585266253)
                  ·
                    refine ⟨619689335392564719474845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652504894380172585266253 619689335392564719474845)
                    ·
                      rfl

theorem cell22_1810261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1810261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810261 prefixEnd_1810261 := by exact prefixLift 1810261
  have htrace : WordTrace (prefixWord ++ tailWord_1810261) baseStart_1810261 baseEnd_1810261 := by
    simpa [prefixWord, tailWord_1810261, baseEnd_1810261] using wordTrace_append hprefix tailTrace_1810261
  have hstable : (prefixWord ++ tailWord_1810261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810261).length < 2 ^ (prefixWord ++ tailWord_1810261).sum := by decide
  have hdescent : baseEnd_1810261 < baseStart_1810261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810274 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1810274 : Nat := 118140960795 + 1810274 * 2 ^ 59
def prefixEnd_1810274 : Nat := 4983230072969 + 3 ^ 40 * 1810274 * 2
def baseEnd_1810274 : Nat := 206564595186079006299935

theorem tailTrace_1810274 : CollatzResearch.WordTrace tailWord_1810274 prefixEnd_1810274 206564595186079006299935 := by
  unfold tailWord_1810274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506529260923485757503469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44017411362462628686675917 16506529260923485757503469)
  ·
    refine ⟨6189948472846307159063801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16506529260923485757503469 6189948472846307159063801)
    ·
      refine ⟨4642461354634730369297851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6189948472846307159063801 4642461354634730369297851)
      ·
        refine ⟨6963692031952095553946777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642461354634730369297851 6963692031952095553946777)
        ·
          refine ⟨5222769023964071665460083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6963692031952095553946777 5222769023964071665460083)
          ·
            refine ⟨7834153535946107498190125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222769023964071665460083 7834153535946107498190125)
            ·
              refine ⟨2937807575979790311821297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7834153535946107498190125 2937807575979790311821297)
              ·
                refine ⟨2203355681984842733865973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937807575979790311821297 2203355681984842733865973)
                ·
                  refine ⟨206564595186079006299935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2203355681984842733865973 206564595186079006299935)
                  ·
                    rfl

theorem cell22_1810274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1810274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810274 prefixEnd_1810274 := by exact prefixLift 1810274
  have htrace : WordTrace (prefixWord ++ tailWord_1810274) baseStart_1810274 baseEnd_1810274 := by
    simpa [prefixWord, tailWord_1810274, baseEnd_1810274] using wordTrace_append hprefix tailTrace_1810274
  have hstable : (prefixWord ++ tailWord_1810274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810274).length < 2 ^ (prefixWord ++ tailWord_1810274).sum := by decide
  have hdescent : baseEnd_1810274 < baseStart_1810274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810345 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_1810345 : Nat := 118140960795 + 1810345 * 2 ^ 59
def prefixEnd_1810345 : Nat := 4983230072969 + 3 ^ 40 * 1810345 * 2
def baseEnd_1810345 : Nat := 619718090309216500374587

theorem tailTrace_1810345 : CollatzResearch.WordTrace tailWord_1810345 prefixEnd_1810345 619718090309216500374587 := by
  unfold tailWord_1810345
  simp only [CollatzResearch.WordTrace]
  refine ⟨66028706626436722155848489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44019137750957814770565659 66028706626436722155848489)
  ·
    refine ⟨49521529969827541616886367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66028706626436722155848489 49521529969827541616886367)
    ·
      refine ⟨74282294954741312425329551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49521529969827541616886367 74282294954741312425329551)
      ·
        refine ⟨111423442432111968637994327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74282294954741312425329551 111423442432111968637994327)
        ·
          refine ⟨167135163648167952956991491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111423442432111968637994327 167135163648167952956991491)
          ·
            refine ⟨250702745472251929435487237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167135163648167952956991491 250702745472251929435487237)
            ·
              refine ⟨47006764776047236769153857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250702745472251929435487237 47006764776047236769153857)
              ·
                refine ⟨35255073582035427576865393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47006764776047236769153857 35255073582035427576865393)
                ·
                  refine ⟨26441305186526570682649045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35255073582035427576865393 26441305186526570682649045)
                  ·
                    refine ⟨619718090309216500374587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26441305186526570682649045 619718090309216500374587)
                    ·
                      rfl

theorem cell22_1810345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_1810345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810345 prefixEnd_1810345 := by exact prefixLift 1810345
  have htrace : WordTrace (prefixWord ++ tailWord_1810345) baseStart_1810345 baseEnd_1810345 := by
    simpa [prefixWord, tailWord_1810345, baseEnd_1810345] using wordTrace_append hprefix tailTrace_1810345
  have hstable : (prefixWord ++ tailWord_1810345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810345).length < 2 ^ (prefixWord ++ tailWord_1810345).sum := by decide
  have hdescent : baseEnd_1810345 < baseStart_1810345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810413 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1810413 : Nat := 118140960795 + 1810413 * 2 ^ 59
def prefixEnd_1810413 : Nat := 4983230072969 + 3 ^ 40 * 1810413 * 2
def baseEnd_1810413 : Nat := 619741368098886989674379

theorem tailTrace_1810413 : CollatzResearch.WordTrace tailWord_1810413 prefixEnd_1810413 619741368098886989674379 := by
  unfold tailWord_1810413
  simp only [CollatzResearch.WordTrace]
  refine ⟨66031186790190369769323893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44020791193460246512882595 66031186790190369769323893)
  ·
    refine ⟨6190423761580347165874115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66031186790190369769323893 6190423761580347165874115)
    ·
      refine ⟨9285635642370520748811173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6190423761580347165874115 9285635642370520748811173)
      ·
        refine ⟨1741056682944472640402095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9285635642370520748811173 1741056682944472640402095)
        ·
          refine ⟨2611585024416708960603143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741056682944472640402095 2611585024416708960603143)
          ·
            refine ⟨3917377536625063440904715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611585024416708960603143 3917377536625063440904715)
            ·
              refine ⟨5876066304937595161357073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917377536625063440904715 5876066304937595161357073)
              ·
                refine ⟨4407049728703196371017805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876066304937595161357073 4407049728703196371017805)
                ·
                  refine ⟨1652643648263698639131677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4407049728703196371017805 1652643648263698639131677)
                  ·
                    refine ⟨619741368098886989674379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652643648263698639131677 619741368098886989674379)
                    ·
                      rfl

theorem cell22_1810413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1810413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810413 prefixEnd_1810413 := by exact prefixLift 1810413
  have htrace : WordTrace (prefixWord ++ tailWord_1810413) baseStart_1810413 baseEnd_1810413 := by
    simpa [prefixWord, tailWord_1810413, baseEnd_1810413] using wordTrace_append hprefix tailTrace_1810413
  have hstable : (prefixWord ++ tailWord_1810413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810413).length < 2 ^ (prefixWord ++ tailWord_1810413).sum := by decide
  have hdescent : baseEnd_1810413 < baseStart_1810413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810430 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1810430 : Nat := 118140960795 + 1810430 * 2 ^ 59
def prefixEnd_1810430 : Nat := 4983230072969 + 3 ^ 40 * 1810430 * 2
def baseEnd_1810430 : Nat := 619747187546304611999327

theorem tailTrace_1810430 : CollatzResearch.WordTrace tailWord_1810430 prefixEnd_1810430 619747187546304611999327 := by
  unfold tailWord_1810430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253975853891097709086593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44021204554085854448461829 8253975853891097709086593)
  ·
    refine ⟨6190481890418323281814945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8253975853891097709086593 6190481890418323281814945)
    ·
      refine ⟨4642861417813742461361209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6190481890418323281814945 4642861417813742461361209)
      ·
        refine ⟨3482146063360306846020907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642861417813742461361209 3482146063360306846020907)
        ·
          refine ⟨5223219095040460269031361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482146063360306846020907 5223219095040460269031361)
          ·
            refine ⟨3917414321280345201773521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5223219095040460269031361 3917414321280345201773521)
            ·
              refine ⟨2938060740960258901330141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917414321280345201773521 2938060740960258901330141)
              ·
                refine ⟨1101772777860097087998803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938060740960258901330141 1101772777860097087998803)
                ·
                  refine ⟨1652659166790145631998205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101772777860097087998803 1652659166790145631998205)
                  ·
                    refine ⟨619747187546304611999327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652659166790145631998205 619747187546304611999327)
                    ·
                      rfl

theorem cell22_1810430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1810430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810430 prefixEnd_1810430 := by exact prefixLift 1810430
  have htrace : WordTrace (prefixWord ++ tailWord_1810430) baseStart_1810430 baseEnd_1810430 := by
    simpa [prefixWord, tailWord_1810430, baseEnd_1810430] using wordTrace_append hprefix tailTrace_1810430
  have hstable : (prefixWord ++ tailWord_1810430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810430).length < 2 ^ (prefixWord ++ tailWord_1810430).sum := by decide
  have hdescent : baseEnd_1810430 < baseStart_1810430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810467 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_1810467 : Nat := 118140960795 + 1810467 * 2 ^ 59
def prefixEnd_1810467 : Nat := 4983230072969 + 3 ^ 40 * 1810467 * 2
def baseEnd_1810467 : Nat := 619759853402448848824213

theorem tailTrace_1810467 : CollatzResearch.WordTrace tailWord_1810467 prefixEnd_1810467 619759853402448848824213 := by
  unfold tailWord_1810467
  simp only [CollatzResearch.WordTrace]
  refine ⟨66033156331994736991789655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44022104221329824661193103 66033156331994736991789655)
  ·
    refine ⟨99049734497992105487684483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66033156331994736991789655 99049734497992105487684483)
    ·
      refine ⟨148574601746988158231526725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99049734497992105487684483 148574601746988158231526725)
      ·
        refine ⟨27857737827560279668411261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148574601746988158231526725 27857737827560279668411261)
        ·
          refine ⟨10446651685335104875654223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27857737827560279668411261 10446651685335104875654223)
          ·
            refine ⟨15669977528002657313481335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446651685335104875654223 15669977528002657313481335)
            ·
              refine ⟨23504966292003985970222003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15669977528002657313481335 23504966292003985970222003)
              ·
                refine ⟨35257449438005978955333005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23504966292003985970222003 35257449438005978955333005)
                ·
                  refine ⟨13221543539252242108249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35257449438005978955333005 13221543539252242108249877)
                  ·
                    refine ⟨619759853402448848824213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13221543539252242108249877 619759853402448848824213)
                    ·
                      rfl

theorem cell22_1810467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_1810467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810467 prefixEnd_1810467 := by exact prefixLift 1810467
  have htrace : WordTrace (prefixWord ++ tailWord_1810467) baseStart_1810467 baseEnd_1810467 := by
    simpa [prefixWord, tailWord_1810467, baseEnd_1810467] using wordTrace_append hprefix tailTrace_1810467
  have hstable : (prefixWord ++ tailWord_1810467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810467).length < 2 ^ (prefixWord ++ tailWord_1810467).sum := by decide
  have hdescent : baseEnd_1810467 < baseStart_1810467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810469 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_1810469 : Nat := 118140960795 + 1810469 * 2 ^ 59
def prefixEnd_1810469 : Nat := 4983230072969 + 3 ^ 40 * 1810469 * 2
def baseEnd_1810469 : Nat := 619760538043321510274207

theorem tailTrace_1810469 : CollatzResearch.WordTrace tailWord_1810469 prefixEnd_1810469 619760538043321510274207 := by
  unfold tailWord_1810469
  simp only [CollatzResearch.WordTrace]
  refine ⟨66033229277987491333362461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44022152851991660888908307 66033229277987491333362461)
  ·
    refine ⟨24762460979245309250010923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66033229277987491333362461 24762460979245309250010923)
    ·
      refine ⟨37143691468867963875016385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24762460979245309250010923 37143691468867963875016385)
      ·
        refine ⟨27857768601650972906262289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37143691468867963875016385 27857768601650972906262289)
        ·
          refine ⟨20893326451238229679696717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27857768601650972906262289 20893326451238229679696717)
          ·
            refine ⟨7834997419214336129886269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20893326451238229679696717 7834997419214336129886269)
            ·
              refine ⟨2938124032205376048707351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7834997419214336129886269 2938124032205376048707351)
              ·
                refine ⟨4407186048308064073061027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938124032205376048707351 4407186048308064073061027)
                ·
                  refine ⟨6610779072462096109591541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407186048308064073061027 6610779072462096109591541)
                  ·
                    refine ⟨619760538043321510274207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6610779072462096109591541 619760538043321510274207)
                    ·
                      rfl

theorem cell22_1810469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_1810469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810469 prefixEnd_1810469 := by exact prefixLift 1810469
  have htrace : WordTrace (prefixWord ++ tailWord_1810469) baseStart_1810469 baseEnd_1810469 := by
    simpa [prefixWord, tailWord_1810469, baseEnd_1810469] using wordTrace_append hprefix tailTrace_1810469
  have hstable : (prefixWord ++ tailWord_1810469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810469).length < 2 ^ (prefixWord ++ tailWord_1810469).sum := by decide
  have hdescent : baseEnd_1810469 < baseStart_1810469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810486 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1810486 : Nat := 118140960795 + 1810486 * 2 ^ 59
def prefixEnd_1810486 : Nat := 4983230072969 + 3 ^ 40 * 1810486 * 2
def baseEnd_1810486 : Nat := 619766357490739132599155

theorem tailTrace_1810486 : CollatzResearch.WordTrace tailWord_1810486 prefixEnd_1810486 619766357490739132599155 := by
  unfold tailWord_1810486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127115582432868952295707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44022566212617268824487541 4127115582432868952295707)
  ·
    refine ⟨6190673373649303428443561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4127115582432868952295707 6190673373649303428443561)
    ·
      refine ⟨4643005030236977571332671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6190673373649303428443561 4643005030236977571332671)
      ·
        refine ⟨6964507545355466356999007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643005030236977571332671 6964507545355466356999007)
        ·
          refine ⟨10446761318033199535498511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964507545355466356999007 10446761318033199535498511)
          ·
            refine ⟨15670141977049799303247767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446761318033199535498511 15670141977049799303247767)
            ·
              refine ⟨23505212965574698954871651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15670141977049799303247767 23505212965574698954871651)
              ·
                refine ⟨35257819448362048432307477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23505212965574698954871651 35257819448362048432307477)
                ·
                  refine ⟨1652710286641971020264413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35257819448362048432307477 1652710286641971020264413)
                  ·
                    refine ⟨619766357490739132599155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652710286641971020264413 619766357490739132599155)
                    ·
                      rfl

theorem cell22_1810486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1810486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810486 prefixEnd_1810486 := by exact prefixLift 1810486
  have htrace : WordTrace (prefixWord ++ tailWord_1810486) baseStart_1810486 baseEnd_1810486 := by
    simpa [prefixWord, tailWord_1810486, baseEnd_1810486] using wordTrace_append hprefix tailTrace_1810486
  have hstable : (prefixWord ++ tailWord_1810486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810486).length < 2 ^ (prefixWord ++ tailWord_1810486).sum := by decide
  have hdescent : baseEnd_1810486 < baseStart_1810486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810488 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 4]
def baseStart_1810488 : Nat := 118140960795 + 1810488 * 2 ^ 59
def prefixEnd_1810488 : Nat := 4983230072969 + 3 ^ 40 * 1810488 * 2
def baseEnd_1810488 : Nat := 206589014043870598016383

theorem tailTrace_1810488 : CollatzResearch.WordTrace tailWord_1810488 prefixEnd_1810488 206589014043870598016383 := by
  unfold tailWord_1810488
  simp only [CollatzResearch.WordTrace]
  refine ⟨33016961132459328789152059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44022614843279105052202745 33016961132459328789152059)
  ·
    refine ⟨49525441698688993183728089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33016961132459328789152059 49525441698688993183728089)
    ·
      refine ⟨37144081274016744887796067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49525441698688993183728089 37144081274016744887796067)
      ·
        refine ⟨55716121911025117331694101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37144081274016744887796067 55716121911025117331694101)
        ·
          refine ⟨2611693214579302374923161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55716121911025117331694101 2611693214579302374923161)
          ·
            refine ⟨1958769910934476781192371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611693214579302374923161 1958769910934476781192371)
            ·
              refine ⟨2938154866401715171788557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958769910934476781192371 2938154866401715171788557)
              ·
                refine ⟨1101808074900643189420709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938154866401715171788557 1101808074900643189420709)
                ·
                  refine ⟨206589014043870598016383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101808074900643189420709 206589014043870598016383)
                  ·
                    rfl

theorem cell22_1810488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_1810488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810488 prefixEnd_1810488 := by exact prefixLift 1810488
  have htrace : WordTrace (prefixWord ++ tailWord_1810488) baseStart_1810488 baseEnd_1810488 := by
    simpa [prefixWord, tailWord_1810488, baseEnd_1810488] using wordTrace_append hprefix tailTrace_1810488
  have hstable : (prefixWord ++ tailWord_1810488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810488).length < 2 ^ (prefixWord ++ tailWord_1810488).sum := by decide
  have hdescent : baseEnd_1810488 < baseStart_1810488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810527 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 9]
def baseStart_1810527 : Nat := 118140960795 + 1810527 * 2 ^ 59
def prefixEnd_1810527 : Nat := 4983230072969 + 3 ^ 40 * 1810527 * 2
def baseEnd_1810527 : Nat := 206593464209542897441343

theorem tailTrace_1810527 : CollatzResearch.WordTrace tailWord_1810527 prefixEnd_1810527 206593464209542897441343 := by
  unfold tailWord_1810527
  simp only [CollatzResearch.WordTrace]
  refine ⟨66035344711777367238973835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44023563141184911492649223 66035344711777367238973835)
  ·
    refine ⟨99053017067666050858460753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66035344711777367238973835 99053017067666050858460753)
    ·
      refine ⟨74289762800749538143845565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99053017067666050858460753 74289762800749538143845565)
      ·
        refine ⟨27858661050281076803942087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74289762800749538143845565 27858661050281076803942087)
        ·
          refine ⟨41787991575421615205913131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27858661050281076803942087 41787991575421615205913131)
          ·
            refine ⟨62681987363132422808869697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41787991575421615205913131 62681987363132422808869697)
            ·
              refine ⟨47011490522349317106652273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62681987363132422808869697 47011490522349317106652273)
              ·
                refine ⟨35258617891761987829989205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47011490522349317106652273 35258617891761987829989205)
                ·
                  refine ⟨206593464209542897441343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35258617891761987829989205 206593464209542897441343)
                  ·
                    rfl

theorem cell22_1810527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_1810527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810527 prefixEnd_1810527 := by exact prefixLift 1810527
  have htrace : WordTrace (prefixWord ++ tailWord_1810527) baseStart_1810527 baseEnd_1810527 := by
    simpa [prefixWord, tailWord_1810527, baseEnd_1810527] using wordTrace_append hprefix tailTrace_1810527
  have hstable : (prefixWord ++ tailWord_1810527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810527).length < 2 ^ (prefixWord ++ tailWord_1810527).sum := by decide
  have hdescent : baseEnd_1810527 < baseStart_1810527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810565 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_1810565 : Nat := 118140960795 + 1810565 * 2 ^ 59
def prefixEnd_1810565 : Nat := 4983230072969 + 3 ^ 40 * 1810565 * 2
def baseEnd_1810565 : Nat := 619793400805209259873913

theorem tailTrace_1810565 : CollatzResearch.WordTrace tailWord_1810565 prefixEnd_1810565 619793400805209259873913 := by
  unfold tailWord_1810565
  simp only [CollatzResearch.WordTrace]
  refine ⟨66036730685639699728857149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44024487123759799819238099 66036730685639699728857149)
  ·
    refine ⟨24763774007114887398321431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66036730685639699728857149 24763774007114887398321431)
    ·
      refine ⟨37145661010672331097482147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24763774007114887398321431 37145661010672331097482147)
      ·
        refine ⟨55718491516008496646223221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37145661010672331097482147 55718491516008496646223221)
        ·
          refine ⟨5223608579625796560583427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55718491516008496646223221 5223608579625796560583427)
          ·
            refine ⟨7835412869438694840875141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223608579625796560583427 7835412869438694840875141)
            ·
              refine ⟨1469139913019755282664089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7835412869438694840875141 1469139913019755282664089)
              ·
                refine ⟨1101854934764816461998067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469139913019755282664089 1101854934764816461998067)
                ·
                  refine ⟨1652782402147224692997101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101854934764816461998067 1652782402147224692997101)
                  ·
                    refine ⟨619793400805209259873913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652782402147224692997101 619793400805209259873913)
                    ·
                      rfl

theorem cell22_1810565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_1810565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810565 prefixEnd_1810565 := by exact prefixLift 1810565
  have htrace : WordTrace (prefixWord ++ tailWord_1810565) baseStart_1810565 baseEnd_1810565 := by
    simpa [prefixWord, tailWord_1810565, baseEnd_1810565] using wordTrace_append hprefix tailTrace_1810565
  have hstable : (prefixWord ++ tailWord_1810565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810565).length < 2 ^ (prefixWord ++ tailWord_1810565).sum := by decide
  have hdescent : baseEnd_1810565 < baseStart_1810565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810589 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 8]
def baseStart_1810589 : Nat := 118140960795 + 1810589 * 2 ^ 59
def prefixEnd_1810589 : Nat := 4983230072969 + 3 ^ 40 * 1810589 * 2
def baseEnd_1810589 : Nat := 206600538831893732424613

theorem tailTrace_1810589 : CollatzResearch.WordTrace tailWord_1810589 prefixEnd_1810589 206600538831893732424613 := by
  unfold tailWord_1810589
  simp only [CollatzResearch.WordTrace]
  refine ⟨66037606037552751827730821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44025070691701834551820547 66037606037552751827730821)
  ·
    refine ⟨12382051132041140967699529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66037606037552751827730821 12382051132041140967699529)
    ·
      refine ⟨9286538349030855725774647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12382051132041140967699529 9286538349030855725774647)
      ·
        refine ⟨13929807523546283588661971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286538349030855725774647 13929807523546283588661971)
        ·
          refine ⟨20894711285319425382992957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13929807523546283588661971 20894711285319425382992957)
          ·
            refine ⟨7835516731994784518622359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20894711285319425382992957 7835516731994784518622359)
            ·
              refine ⟨11753275097992176777933539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835516731994784518622359 11753275097992176777933539)
              ·
                refine ⟨17629912646988265166900309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11753275097992176777933539 17629912646988265166900309)
                ·
                  refine ⟨206600538831893732424613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17629912646988265166900309 206600538831893732424613)
                  ·
                    rfl

theorem cell22_1810589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_1810589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810589 prefixEnd_1810589 := by exact prefixLift 1810589
  have htrace : WordTrace (prefixWord ++ tailWord_1810589) baseStart_1810589 baseEnd_1810589 := by
    simpa [prefixWord, tailWord_1810589, baseEnd_1810589] using wordTrace_append hprefix tailTrace_1810589
  have hstable : (prefixWord ++ tailWord_1810589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810589).length < 2 ^ (prefixWord ++ tailWord_1810589).sum := by decide
  have hdescent : baseEnd_1810589 < baseStart_1810589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810591 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 3, 4]
def baseStart_1810591 : Nat := 118140960795 + 1810591 * 2 ^ 59
def prefixEnd_1810591 : Nat := 4983230072969 + 3 ^ 40 * 1810591 * 2
def baseEnd_1810591 : Nat := 619802301136553858723833

theorem tailTrace_1810591 : CollatzResearch.WordTrace tailWord_1810591 prefixEnd_1810591 619802301136553858723833 := by
  unfold tailWord_1810591
  simp only [CollatzResearch.WordTrace]
  refine ⟨66037678983545506169303627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44025119322363670779535751 66037678983545506169303627)
  ·
    refine ⟨99056518475318259253955441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66037678983545506169303627 99056518475318259253955441)
    ·
      refine ⟨74292388856488694440466581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99056518475318259253955441 74292388856488694440466581)
      ·
        refine ⟨3482455727647907551896871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74292388856488694440466581 3482455727647907551896871)
        ·
          refine ⟨5223683591471861327845307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482455727647907551896871 5223683591471861327845307)
          ·
            refine ⟨7835525387207791991767961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223683591471861327845307 7835525387207791991767961)
            ·
              refine ⟨5876644040405843993825971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7835525387207791991767961 5876644040405843993825971)
              ·
                refine ⟨8814966060608765990738957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876644040405843993825971 8814966060608765990738957)
                ·
                  refine ⟨3305612272728287246527109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8814966060608765990738957 3305612272728287246527109)
                  ·
                    refine ⟨619802301136553858723833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3305612272728287246527109 619802301136553858723833)
                    ·
                      rfl

theorem cell22_1810591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_1810591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810591 prefixEnd_1810591 := by exact prefixLift 1810591
  have htrace : WordTrace (prefixWord ++ tailWord_1810591) baseStart_1810591 baseEnd_1810591 := by
    simpa [prefixWord, tailWord_1810591, baseEnd_1810591] using wordTrace_append hprefix tailTrace_1810591
  have hstable : (prefixWord ++ tailWord_1810591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810591).length < 2 ^ (prefixWord ++ tailWord_1810591).sum := by decide
  have hdescent : baseEnd_1810591 < baseStart_1810591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810619 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 4, 4]
def baseStart_1810619 : Nat := 118140960795 + 1810619 * 2 ^ 59
def prefixEnd_1810619 : Nat := 4983230072969 + 3 ^ 40 * 1810619 * 2
def baseEnd_1810619 : Nat := 619811886108771119023747

theorem tailTrace_1810619 : CollatzResearch.WordTrace tailWord_1810619 prefixEnd_1810619 619811886108771119023747 := by
  unfold tailWord_1810619
  simp only [CollatzResearch.WordTrace]
  refine ⟨66038700227444066951322911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44025800151629377967548607 66038700227444066951322911)
  ·
    refine ⟨99058050341166100426984367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66038700227444066951322911 99058050341166100426984367)
    ·
      refine ⟨148587075511749150640476551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99058050341166100426984367 148587075511749150640476551)
      ·
        refine ⟨222880613267623725960714827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148587075511749150640476551 222880613267623725960714827)
        ·
          refine ⟨334320919901435588941072241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222880613267623725960714827 334320919901435588941072241)
          ·
            refine ⟨250740689926076691705804181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334320919901435588941072241 250740689926076691705804181)
            ·
              refine ⟨11753469840284844923709571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250740689926076691705804181 11753469840284844923709571)
              ·
                refine ⟨17630204760427267385564357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11753469840284844923709571 17630204760427267385564357)
                ·
                  refine ⟨3305663392580112634793317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17630204760427267385564357 3305663392580112634793317)
                  ·
                    refine ⟨619811886108771119023747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3305663392580112634793317 619811886108771119023747)
                    ·
                      rfl

theorem cell22_1810619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_1810619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810619 prefixEnd_1810619 := by exact prefixLift 1810619
  have htrace : WordTrace (prefixWord ++ tailWord_1810619) baseStart_1810619 baseEnd_1810619 := by
    simpa [prefixWord, tailWord_1810619, baseEnd_1810619] using wordTrace_append hprefix tailTrace_1810619
  have hstable : (prefixWord ++ tailWord_1810619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810619).length < 2 ^ (prefixWord ++ tailWord_1810619).sum := by decide
  have hdescent : baseEnd_1810619 < baseStart_1810619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810634 : List Nat := [3, 1, 2, 1, 3, 1, 2, 9]
def baseStart_1810634 : Nat := 118140960795 + 1810634 * 2 ^ 59
def prefixEnd_1810634 : Nat := 4983230072969 + 3 ^ 40 * 1810634 * 2
def baseEnd_1810634 : Nat := 68868557879479564433189

theorem tailTrace_1810634 : CollatzResearch.WordTrace tailWord_1810634 prefixEnd_1810634 68868557879479564433189 := by
  unfold tailWord_1810634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16509811830597431128279739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44026164881593149675412637 16509811830597431128279739)
  ·
    refine ⟨24764717745896146692419609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16509811830597431128279739 24764717745896146692419609)
    ·
      refine ⟨18573538309422110019314707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24764717745896146692419609 18573538309422110019314707)
      ·
        refine ⟨27860307464133165028972061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573538309422110019314707 27860307464133165028972061)
        ·
          refine ⟨10447615299049936885864523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27860307464133165028972061 10447615299049936885864523)
          ·
            refine ⟨15671422948574905328796785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10447615299049936885864523 15671422948574905328796785)
            ·
              refine ⟨11753567211431178996597589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15671422948574905328796785 11753567211431178996597589)
              ·
                refine ⟨68868557879479564433189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11753567211431178996597589 68868557879479564433189)
                ·
                  rfl

theorem cell22_1810634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_1810634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810634 prefixEnd_1810634 := by exact prefixLift 1810634
  have htrace : WordTrace (prefixWord ++ tailWord_1810634) baseStart_1810634 baseEnd_1810634 := by
    simpa [prefixWord, tailWord_1810634, baseEnd_1810634] using wordTrace_append hprefix tailTrace_1810634
  have hstable : (prefixWord ++ tailWord_1810634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810634).length < 2 ^ (prefixWord ++ tailWord_1810634).sum := by decide
  have hdescent : baseEnd_1810634 < baseStart_1810634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810638 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_1810638 : Nat := 118140960795 + 1810638 * 2 ^ 59
def prefixEnd_1810638 : Nat := 4983230072969 + 3 ^ 40 * 1810638 * 2
def baseEnd_1810638 : Nat := 619818390197061402798689

theorem tailTrace_1810638 : CollatzResearch.WordTrace tailWord_1810638 prefixEnd_1810638 619818390197061402798689 := by
  unfold tailWord_1810638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254924151796904149533071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44026262142916822130843045 8254924151796904149533071)
  ·
    refine ⟨12382386227695356224299607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8254924151796904149533071 12382386227695356224299607)
    ·
      refine ⟨18573579341543034336449411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382386227695356224299607 18573579341543034336449411)
      ·
        refine ⟨27860369012314551504674117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573579341543034336449411 27860369012314551504674117)
        ·
          refine ⟨5223819189808978407126397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27860369012314551504674117 5223819189808978407126397)
          ·
            refine ⟨1958932196178366902672399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5223819189808978407126397 1958932196178366902672399)
            ·
              refine ⟨2938398294267550354008599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958932196178366902672399 2938398294267550354008599)
              ·
                refine ⟨4407597441401325531012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938398294267550354008599 4407597441401325531012899)
                ·
                  refine ⟨6611396162101988296519349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407597441401325531012899 6611396162101988296519349)
                  ·
                    refine ⟨619818390197061402798689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6611396162101988296519349 619818390197061402798689)
                    ·
                      rfl

theorem cell22_1810638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_1810638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810638 prefixEnd_1810638 := by exact prefixLift 1810638
  have htrace : WordTrace (prefixWord ++ tailWord_1810638) baseStart_1810638 baseEnd_1810638 := by
    simpa [prefixWord, tailWord_1810638, baseEnd_1810638] using wordTrace_append hprefix tailTrace_1810638
  have hstable : (prefixWord ++ tailWord_1810638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810638).length < 2 ^ (prefixWord ++ tailWord_1810638).sum := by decide
  have hdescent : baseEnd_1810638 < baseStart_1810638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810730 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_1810730 : Nat := 118140960795 + 1810730 * 2 ^ 59
def prefixEnd_1810730 : Nat := 4983230072969 + 3 ^ 40 * 1810730 * 2
def baseEnd_1810730 : Nat := 206616627892401276499469

theorem tailTrace_1810730 : CollatzResearch.WordTrace tailWord_1810730 prefixEnd_1810730 206616627892401276499469 := by
  unfold tailWord_1810730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16510687182510483227153411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44028499153361288605742429 16510687182510483227153411)
  ·
    refine ⟨24766030773765724840730117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16510687182510483227153411 24766030773765724840730117)
    ·
      refine ⟨4643630770081073407636897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24766030773765724840730117 4643630770081073407636897)
      ·
        refine ⟨3482723077560805055727673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4643630770081073407636897 3482723077560805055727673)
        ·
          refine ⟨2612042308170603791795755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482723077560805055727673 2612042308170603791795755)
          ·
            refine ⟨3918063462255905687693633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612042308170603791795755 3918063462255905687693633)
            ·
              refine ⟨2938547596691929265770225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918063462255905687693633 2938547596691929265770225)
              ·
                refine ⟨2203910697518946949327669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938547596691929265770225 2203910697518946949327669)
                ·
                  refine ⟨206616627892401276499469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2203910697518946949327669 206616627892401276499469)
                  ·
                    rfl

theorem cell22_1810730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_1810730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810730 prefixEnd_1810730 := by exact prefixLift 1810730
  have htrace : WordTrace (prefixWord ++ tailWord_1810730) baseStart_1810730 baseEnd_1810730 := by
    simpa [prefixWord, tailWord_1810730, baseEnd_1810730] using wordTrace_append hprefix tailTrace_1810730
  have hstable : (prefixWord ++ tailWord_1810730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810730).length < 2 ^ (prefixWord ++ tailWord_1810730).sum := by decide
  have hdescent : baseEnd_1810730 < baseStart_1810730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810734 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1810734 : Nat := 118140960795 + 1810734 * 2 ^ 59
def prefixEnd_1810734 : Nat := 4983230072969 + 3 ^ 40 * 1810734 * 2
def baseEnd_1810734 : Nat := 619851252958949152398395

theorem tailTrace_1810734 : CollatzResearch.WordTrace tailWord_1810734 prefixEnd_1810734 619851252958949152398395 := by
  unfold tailWord_1810734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255361827753430198969907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44028596414684961061172837 8255361827753430198969907)
  ·
    refine ⟨12383042741630145298454861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8255361827753430198969907 12383042741630145298454861)
    ·
      refine ⟨4643641028111304486920573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12383042741630145298454861 4643641028111304486920573)
      ·
        refine ⟨1741365385541739182595215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4643641028111304486920573 1741365385541739182595215)
        ·
          refine ⟨2612048078312608773892823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741365385541739182595215 2612048078312608773892823)
          ·
            refine ⟨3918072117468913160839235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612048078312608773892823 3918072117468913160839235)
            ·
              refine ⟨5877108176203369741258853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918072117468913160839235 5877108176203369741258853)
              ·
                refine ⟨1101957783038131826486035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5877108176203369741258853 1101957783038131826486035)
                ·
                  refine ⟨1652936674557197739729053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101957783038131826486035 1652936674557197739729053)
                  ·
                    refine ⟨619851252958949152398395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1652936674557197739729053 619851252958949152398395)
                    ·
                      rfl

theorem cell22_1810734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1810734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810734 prefixEnd_1810734 := by exact prefixLift 1810734
  have htrace : WordTrace (prefixWord ++ tailWord_1810734) baseStart_1810734 baseEnd_1810734 := by
    simpa [prefixWord, tailWord_1810734, baseEnd_1810734] using wordTrace_append hprefix tailTrace_1810734
  have hstable : (prefixWord ++ tailWord_1810734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810734).length < 2 ^ (prefixWord ++ tailWord_1810734).sum := by decide
  have hdescent : baseEnd_1810734 < baseStart_1810734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810741 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 6]
def baseStart_1810741 : Nat := 118140960795 + 1810741 * 2 ^ 59
def prefixEnd_1810741 : Nat := 4983230072969 + 3 ^ 40 * 1810741 * 2
def baseEnd_1810741 : Nat := 206617883067334489157791

theorem tailTrace_1810741 : CollatzResearch.WordTrace tailWord_1810741 prefixEnd_1810741 206617883067334489157791 := by
  unfold tailWord_1810741
  simp only [CollatzResearch.WordTrace]
  refine ⟨66043149933002081787264077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44028766622001387858176051 66043149933002081787264077)
  ·
    refine ⟨24766181224875780670224029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66043149933002081787264077 24766181224875780670224029)
    ·
      refine ⟨9287317959328417751334011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24766181224875780670224029 9287317959328417751334011)
      ·
        refine ⟨13930976938992626627001017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9287317959328417751334011 13930976938992626627001017)
        ·
          refine ⟨10448232704244469970250763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13930976938992626627001017 10448232704244469970250763)
          ·
            refine ⟨15672349056366704955376145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448232704244469970250763 15672349056366704955376145)
            ·
              refine ⟨11754261792275028716532109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15672349056366704955376145 11754261792275028716532109)
              ·
                refine ⟨4407848172103135768699541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11754261792275028716532109 4407848172103135768699541)
                ·
                  refine ⟨206617883067334489157791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4407848172103135768699541 206617883067334489157791)
                  ·
                    rfl

theorem cell22_1810741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_1810741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810741 prefixEnd_1810741 := by exact prefixLift 1810741
  have htrace : WordTrace (prefixWord ++ tailWord_1810741) baseStart_1810741 baseEnd_1810741 := by
    simpa [prefixWord, tailWord_1810741, baseEnd_1810741] using wordTrace_append hprefix tailTrace_1810741
  have hstable : (prefixWord ++ tailWord_1810741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810741).length < 2 ^ (prefixWord ++ tailWord_1810741).sum := by decide
  have hdescent : baseEnd_1810741 < baseStart_1810741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810771 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 2, 4]
def baseStart_1810771 : Nat := 118140960795 + 1810771 * 2 ^ 59
def prefixEnd_1810771 : Nat := 4983230072969 + 3 ^ 40 * 1810771 * 2
def baseEnd_1810771 : Nat := 619863918815093389223281

theorem tailTrace_1810771 : CollatzResearch.WordTrace tailWord_1810771 prefixEnd_1810771 619863918815093389223281 := by
  unfold tailWord_1810771
  simp only [CollatzResearch.WordTrace]
  refine ⟨66044244122893396910856167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44029496081928931273904111 66044244122893396910856167)
  ·
    refine ⟨99066366184340095366284251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66044244122893396910856167 99066366184340095366284251)
    ·
      refine ⟨148599549276510143049426377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99066366184340095366284251 148599549276510143049426377)
      ·
        refine ⟨111449661957382607287069783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148599549276510143049426377 111449661957382607287069783)
        ·
          refine ⟨167174492936073910930604675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111449661957382607287069783 167174492936073910930604675)
          ·
            refine ⟨250761739404110866395907013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167174492936073910930604675 250761739404110866395907013)
            ·
              refine ⟨47017826138270787449232565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250761739404110866395907013 47017826138270787449232565)
              ·
                refine ⟨4407921200462886323365553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47017826138270787449232565 4407921200462886323365553)
                ·
                  refine ⟨3305940900347164742524165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407921200462886323365553 3305940900347164742524165)
                  ·
                    refine ⟨619863918815093389223281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3305940900347164742524165 619863918815093389223281)
                    ·
                      rfl

theorem cell22_1810771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_1810771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810771 prefixEnd_1810771 := by exact prefixLift 1810771
  have htrace : WordTrace (prefixWord ++ tailWord_1810771) baseStart_1810771 baseEnd_1810771 := by
    simpa [prefixWord, tailWord_1810771, baseEnd_1810771] using wordTrace_append hprefix tailTrace_1810771
  have hstable : (prefixWord ++ tailWord_1810771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810771).length < 2 ^ (prefixWord ++ tailWord_1810771).sum := by decide
  have hdescent : baseEnd_1810771 < baseStart_1810771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810858 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1810858 : Nat := 118140960795 + 1810858 * 2 ^ 59
def prefixEnd_1810858 : Nat := 4983230072969 + 3 ^ 40 * 1810858 * 2
def baseEnd_1810858 : Nat := 619893700693054162298015

theorem tailTrace_1810858 : CollatzResearch.WordTrace tailWord_1810858 prefixEnd_1810858 619893700693054162298015 := by
  unfold tailWord_1810858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16511854318394552692318307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44031611515718807179515485 16511854318394552692318307)
  ·
    refine ⟨24767781477591829038477461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16511854318394552692318307 24767781477591829038477461)
    ·
      refine ⟨1160989756762116986178631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24767781477591829038477461 1160989756762116986178631)
      ·
        refine ⟨1741484635143175479267947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160989756762116986178631 1741484635143175479267947)
        ·
          refine ⟨2612226952714763218901921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741484635143175479267947 2612226952714763218901921)
          ·
            refine ⟨1959170214536072414176441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2612226952714763218901921 1959170214536072414176441)
            ·
              refine ⟨1469377660902054310632331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959170214536072414176441 1469377660902054310632331)
              ·
                refine ⟨2204066491353081465948497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469377660902054310632331 2204066491353081465948497)
                ·
                  refine ⟨1653049868514811099461373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204066491353081465948497 1653049868514811099461373)
                  ·
                    refine ⟨619893700693054162298015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653049868514811099461373 619893700693054162298015)
                    ·
                      rfl

theorem cell22_1810858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1810858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810858 prefixEnd_1810858 := by exact prefixLift 1810858
  have htrace : WordTrace (prefixWord ++ tailWord_1810858) baseStart_1810858 baseEnd_1810858 := by
    simpa [prefixWord, tailWord_1810858, baseEnd_1810858] using wordTrace_append hprefix tailTrace_1810858
  have hstable : (prefixWord ++ tailWord_1810858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810858).length < 2 ^ (prefixWord ++ tailWord_1810858).sum := by decide
  have hdescent : baseEnd_1810858 < baseStart_1810858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810865 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 5]
def baseStart_1810865 : Nat := 118140960795 + 1810865 * 2 ^ 59
def prefixEnd_1810865 : Nat := 4983230072969 + 3 ^ 40 * 1810865 * 2
def baseEnd_1810865 : Nat := 206632032312036159124331

theorem tailTrace_1810865 : CollatzResearch.WordTrace tailWord_1810865 prefixEnd_1810865 206632032312036159124331 := by
  unfold tailWord_1810865
  simp only [CollatzResearch.WordTrace]
  refine ⟨66047672584552850964778049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44031781723035233976518699 66047672584552850964778049)
  ·
    refine ⟨49535754438414638223583537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66047672584552850964778049 49535754438414638223583537)
    ·
      refine ⟨37151815828810978667687653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49535754438414638223583537 37151815828810978667687653)
      ·
        refine ⟨6965965467902058500191435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37151815828810978667687653 6965965467902058500191435)
        ·
          refine ⟨10448948201853087750287153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965965467902058500191435 10448948201853087750287153)
          ·
            refine ⟨7836711151389815812715365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10448948201853087750287153 7836711151389815812715365)
            ·
              refine ⟨1469383340885590464884131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7836711151389815812715365 1469383340885590464884131)
              ·
                refine ⟨2204075011328385697326197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469383340885590464884131 2204075011328385697326197)
                ·
                  refine ⟨206632032312036159124331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2204075011328385697326197 206632032312036159124331)
                  ·
                    rfl

theorem cell22_1810865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_1810865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810865 prefixEnd_1810865 := by exact prefixLift 1810865
  have htrace : WordTrace (prefixWord ++ tailWord_1810865) baseStart_1810865 baseEnd_1810865 := by
    simpa [prefixWord, tailWord_1810865, baseEnd_1810865] using wordTrace_append hprefix tailTrace_1810865
  have hstable : (prefixWord ++ tailWord_1810865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810865).length < 2 ^ (prefixWord ++ tailWord_1810865).sum := by decide
  have hdescent : baseEnd_1810865 < baseStart_1810865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810921 : List Nat := [1, 2, 1, 1, 1, 2, 1, 13]
def baseStart_1810921 : Nat := 118140960795 + 1810921 * 2 ^ 59
def prefixEnd_1810921 : Nat := 4983230072969 + 3 ^ 40 * 1810921 * 2
def baseEnd_1810921 : Nat := 68879474097838110885869

theorem tailTrace_1810921 : CollatzResearch.WordTrace tailWord_1810921 prefixEnd_1810921 68879474097838110885869 := by
  unfold tailWord_1810921
  simp only [CollatzResearch.WordTrace]
  refine ⟨66049715072349972528816617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44033143381566648352544411 66049715072349972528816617)
  ·
    refine ⟨49537286304262479396612463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66049715072349972528816617 49537286304262479396612463)
    ·
      refine ⟨74305929456393719094918695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49537286304262479396612463 74305929456393719094918695)
      ·
        refine ⟨111458894184590578642378043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74305929456393719094918695 111458894184590578642378043)
        ·
          refine ⟨167188341276885867963567065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111458894184590578642378043 167188341276885867963567065)
          ·
            refine ⟨125391255957664400972675299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167188341276885867963567065 125391255957664400972675299)
            ·
              refine ⟨188086883936496601459012949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125391255957664400972675299 188086883936496601459012949)
              ·
                refine ⟨68879474097838110885869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 188086883936496601459012949 68879474097838110885869)
                ·
                  rfl

theorem cell22_1810921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 13].length) (baseStart_1810921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810921 prefixEnd_1810921 := by exact prefixLift 1810921
  have htrace : WordTrace (prefixWord ++ tailWord_1810921) baseStart_1810921 baseEnd_1810921 := by
    simpa [prefixWord, tailWord_1810921, baseEnd_1810921] using wordTrace_append hprefix tailTrace_1810921
  have hstable : (prefixWord ++ tailWord_1810921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810921).length < 2 ^ (prefixWord ++ tailWord_1810921).sum := by decide
  have hdescent : baseEnd_1810921 < baseStart_1810921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810925 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1810925 : Nat := 118140960795 + 1810925 * 2 ^ 59
def prefixEnd_1810925 : Nat := 4983230072969 + 3 ^ 40 * 1810925 * 2
def baseEnd_1810925 : Nat := 619916636162288320872809

theorem tailTrace_1810925 : CollatzResearch.WordTrace tailWord_1810925 prefixEnd_1810925 619916636162288320872809 := by
  unfold tailWord_1810925
  simp only [CollatzResearch.WordTrace]
  refine ⟨66049860964335481211962229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44033240642890320807974819 66049860964335481211962229)
  ·
    refine ⟨6192174465406451363621459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66049860964335481211962229 6192174465406451363621459)
    ·
      refine ⟨9288261698109677045432189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6192174465406451363621459 9288261698109677045432189)
      ·
        refine ⟨3483098136791128892037071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9288261698109677045432189 3483098136791128892037071)
        ·
          refine ⟨5224647205186693338055607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483098136791128892037071 5224647205186693338055607)
          ·
            refine ⟨7836970807780040007083411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224647205186693338055607 7836970807780040007083411)
            ·
              refine ⟨11755456211670060010625117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836970807780040007083411 11755456211670060010625117)
              ·
                refine ⟨4408296079376272503984419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11755456211670060010625117 4408296079376272503984419)
                ·
                  refine ⟨6612444119064408755976629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408296079376272503984419 6612444119064408755976629)
                  ·
                    refine ⟨619916636162288320872809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6612444119064408755976629 619916636162288320872809)
                    ·
                      rfl

theorem cell22_1810925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1810925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810925 prefixEnd_1810925 := by exact prefixLift 1810925
  have htrace : WordTrace (prefixWord ++ tailWord_1810925) baseStart_1810925 baseEnd_1810925 := by
    simpa [prefixWord, tailWord_1810925, baseEnd_1810925] using wordTrace_append hprefix tailTrace_1810925
  have hstable : (prefixWord ++ tailWord_1810925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810925).length < 2 ^ (prefixWord ++ tailWord_1810925).sum := by decide
  have hdescent : baseEnd_1810925 < baseStart_1810925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810946 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1810946 : Nat := 118140960795 + 1810946 * 2 ^ 59
def prefixEnd_1810946 : Nat := 4983230072969 + 3 ^ 40 * 1810946 * 2
def baseEnd_1810946 : Nat := 619923824891451266097745

theorem tailTrace_1810946 : CollatzResearch.WordTrace tailWord_1810946 prefixEnd_1810946 619923824891451266097745 := by
  unfold tailWord_1810946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16512656724314850449619173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44033751264839601198984461 16512656724314850449619173)
  ·
    refine ⟨3096123135809034459303595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16512656724314850449619173 3096123135809034459303595)
    ·
      refine ⟨4644184703713551688955393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3096123135809034459303595 4644184703713551688955393)
      ·
        refine ⟨3483138527785163766716545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4644184703713551688955393 3483138527785163766716545)
        ·
          refine ⟨2612353895838872825037409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3483138527785163766716545 2612353895838872825037409)
          ·
            refine ⟨1959265421879154618778057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2612353895838872825037409 1959265421879154618778057)
            ·
              refine ⟨1469449066409365964083543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959265421879154618778057 1469449066409365964083543)
              ·
                refine ⟨2204173599614048946125315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469449066409365964083543 2204173599614048946125315)
                ·
                  refine ⟨3306260399421073419187973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204173599614048946125315 3306260399421073419187973)
                  ·
                    refine ⟨619923824891451266097745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3306260399421073419187973 619923824891451266097745)
                    ·
                      rfl

theorem cell22_1810946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1810946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810946 prefixEnd_1810946 := by exact prefixLift 1810946
  have htrace : WordTrace (prefixWord ++ tailWord_1810946) baseStart_1810946 baseEnd_1810946 := by
    simpa [prefixWord, tailWord_1810946, baseEnd_1810946] using wordTrace_append hprefix tailTrace_1810946
  have hstable : (prefixWord ++ tailWord_1810946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810946).length < 2 ^ (prefixWord ++ tailWord_1810946).sum := by decide
  have hdescent : baseEnd_1810946 < baseStart_1810946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810970 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_1810970 : Nat := 118140960795 + 1810970 * 2 ^ 59
def prefixEnd_1810970 : Nat := 4983230072969 + 3 ^ 40 * 1810970 * 2
def baseEnd_1810970 : Nat := 619932040581923203497671

theorem tailTrace_1810970 : CollatzResearch.WordTrace tailWord_1810970 prefixEnd_1810970 619932040581923203497671 := by
  unfold tailWord_1810970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16512875562293113474337591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44034334832781635931566909 16512875562293113474337591)
  ·
    refine ⟨24769313343439670211506387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16512875562293113474337591 24769313343439670211506387)
    ·
      refine ⟨37153970015159505317259581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24769313343439670211506387 37153970015159505317259581)
      ·
        refine ⟨13932738755684814493972343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37153970015159505317259581 13932738755684814493972343)
        ·
          refine ⟨20899108133527221740958515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13932738755684814493972343 20899108133527221740958515)
          ·
            refine ⟨31348662200290832611437773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20899108133527221740958515 31348662200290832611437773)
            ·
              refine ⟨11755748325109062229289165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31348662200290832611437773 11755748325109062229289165)
              ·
                refine ⟨4408405621915898335983437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11755748325109062229289165 4408405621915898335983437)
                ·
                  refine ⟨1653152108218461875993789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4408405621915898335983437 1653152108218461875993789)
                  ·
                    refine ⟨619932040581923203497671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653152108218461875993789 619932040581923203497671)
                    ·
                      rfl

theorem cell22_1810970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_1810970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810970 prefixEnd_1810970 := by exact prefixLift 1810970
  have htrace : WordTrace (prefixWord ++ tailWord_1810970) baseStart_1810970 baseEnd_1810970 := by
    simpa [prefixWord, tailWord_1810970, baseEnd_1810970] using wordTrace_append hprefix tailTrace_1810970
  have hstable : (prefixWord ++ tailWord_1810970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810970).length < 2 ^ (prefixWord ++ tailWord_1810970).sum := by decide
  have hdescent : baseEnd_1810970 < baseStart_1810970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810989 : List Nat := [1, 5, 4, 1, 1, 1, 1, 8]
def baseStart_1810989 : Nat := 118140960795 + 1810989 * 2 ^ 59
def prefixEnd_1810989 : Nat := 4983230072969 + 3 ^ 40 * 1810989 * 2
def baseEnd_1810989 : Nat := 68882060518912609696957

theorem tailTrace_1810989 : CollatzResearch.WordTrace tailWord_1810989 prefixEnd_1810989 68882060518912609696957 := by
  unfold tailWord_1810989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66052195236103620142292021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44034796824069080094861347 66052195236103620142292021)
  ·
    refine ⟨6192393303384714388339877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66052195236103620142292021 6192393303384714388339877)
    ·
      refine ⟨1161073744384633947813727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6192393303384714388339877 1161073744384633947813727)
      ·
        refine ⟨1741610616576950921720591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161073744384633947813727 1741610616576950921720591)
        ·
          refine ⟨2612415924865426382580887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741610616576950921720591 2612415924865426382580887)
          ·
            refine ⟨3918623887298139573871331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612415924865426382580887 3918623887298139573871331)
            ·
              refine ⟨5877935830947209360806997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918623887298139573871331 5877935830947209360806997)
              ·
                refine ⟨68882060518912609696957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5877935830947209360806997 68882060518912609696957)
                ·
                  rfl

theorem cell22_1810989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 8].length) (baseStart_1810989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1810989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1810989 prefixEnd_1810989 := by exact prefixLift 1810989
  have htrace : WordTrace (prefixWord ++ tailWord_1810989) baseStart_1810989 baseEnd_1810989 := by
    simpa [prefixWord, tailWord_1810989, baseEnd_1810989] using wordTrace_append hprefix tailTrace_1810989
  have hstable : (prefixWord ++ tailWord_1810989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810989).length < 2 ^ (prefixWord ++ tailWord_1810989).sum := by decide
  have hdescent : baseEnd_1810989 < baseStart_1810989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811004 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_1811004 : Nat := 118140960795 + 1811004 * 2 ^ 59
def prefixEnd_1811004 : Nat := 4983230072969 + 3 ^ 40 * 1811004 * 2
def baseEnd_1811004 : Nat := 619943679476758448147567

theorem tailTrace_1811004 : CollatzResearch.WordTrace tailWord_1811004 prefixEnd_1811004 619943679476758448147567 := by
  unfold tailWord_1811004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33026371165524638852044033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44035161554032851802725377 33026371165524638852044033)
  ·
    refine ⟨24769778374143479139033025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33026371165524638852044033 24769778374143479139033025)
    ·
      refine ⟨18577333780607609354274769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24769778374143479139033025 18577333780607609354274769)
      ·
        refine ⟨13933000335455707015706077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18577333780607609354274769 13933000335455707015706077)
        ·
          refine ⟨5224875125795890130889779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13933000335455707015706077 5224875125795890130889779)
          ·
            refine ⟨7837312688693835196334669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224875125795890130889779 7837312688693835196334669)
            ·
              refine ⟨2938992258260188198625501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7837312688693835196334669 2938992258260188198625501)
              ·
                refine ⟨1102122096847570574484563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938992258260188198625501 1102122096847570574484563)
                ·
                  refine ⟨1653183145271355861726845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102122096847570574484563 1653183145271355861726845)
                  ·
                    refine ⟨619943679476758448147567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653183145271355861726845 619943679476758448147567)
                    ·
                      rfl

theorem cell22_1811004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_1811004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811004 prefixEnd_1811004 := by exact prefixLift 1811004
  have htrace : WordTrace (prefixWord ++ tailWord_1811004) baseStart_1811004 baseEnd_1811004 := by
    simpa [prefixWord, tailWord_1811004, baseEnd_1811004] using wordTrace_append hprefix tailTrace_1811004
  have hstable : (prefixWord ++ tailWord_1811004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811004).length < 2 ^ (prefixWord ++ tailWord_1811004).sum := by decide
  have hdescent : baseEnd_1811004 < baseStart_1811004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811075 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 2, 4]
def baseStart_1811075 : Nat := 118140960795 + 1811075 * 2 ^ 59
def prefixEnd_1811075 : Nat := 4983230072969 + 3 ^ 40 * 1811075 * 2
def baseEnd_1811075 : Nat := 619967984227737929622349

theorem tailTrace_1811075 : CollatzResearch.WordTrace tailWord_1811075 prefixEnd_1811075 619967984227737929622349 := by
  unfold tailWord_1811075
  simp only [CollatzResearch.WordTrace]
  refine ⟨66055331913792056829922679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44036887942528037886615119 66055331913792056829922679)
  ·
    refine ⟨99082997870688085244884019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66055331913792056829922679 99082997870688085244884019)
    ·
      refine ⟨148624496806032127867326029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99082997870688085244884019 148624496806032127867326029)
      ·
        refine ⟨55734186302262047950247261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148624496806032127867326029 55734186302262047950247261)
        ·
          refine ⟨20900319863348267981342723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55734186302262047950247261 20900319863348267981342723)
          ·
            refine ⟨31350479795022401972014085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20900319863348267981342723 31350479795022401972014085)
            ·
              refine ⟨5878214961566700369752641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31350479795022401972014085 5878214961566700369752641)
              ·
                refine ⟨4408661221175025277314481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5878214961566700369752641 4408661221175025277314481)
                ·
                  refine ⟨3306495915881268957985861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408661221175025277314481 3306495915881268957985861)
                  ·
                    refine ⟨619967984227737929622349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3306495915881268957985861 619967984227737929622349)
                    ·
                      rfl

theorem cell22_1811075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_1811075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811075 prefixEnd_1811075 := by exact prefixLift 1811075
  have htrace : WordTrace (prefixWord ++ tailWord_1811075) baseStart_1811075 baseEnd_1811075 := by
    simpa [prefixWord, tailWord_1811075, baseEnd_1811075] using wordTrace_append hprefix tailTrace_1811075
  have hstable : (prefixWord ++ tailWord_1811075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811075).length < 2 ^ (prefixWord ++ tailWord_1811075).sum := by decide
  have hdescent : baseEnd_1811075 < baseStart_1811075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811077 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_1811077 : Nat := 118140960795 + 1811077 * 2 ^ 59
def prefixEnd_1811077 : Nat := 4983230072969 + 3 ^ 40 * 1811077 * 2
def baseEnd_1811077 : Nat := 619968668868610591072343

theorem tailTrace_1811077 : CollatzResearch.WordTrace tailWord_1811077 prefixEnd_1811077 619968668868610591072343 := by
  unfold tailWord_1811077
  simp only [CollatzResearch.WordTrace]
  refine ⟨66055404859784811171495485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44036936573189874114330323 66055404859784811171495485)
  ·
    refine ⟨24770776822419304189310807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66055404859784811171495485 24770776822419304189310807)
    ·
      refine ⟨37156165233628956283966211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24770776822419304189310807 37156165233628956283966211)
      ·
        refine ⟨55734247850443434425949317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37156165233628956283966211 55734247850443434425949317)
        ·
          refine ⟨10450171471958143954865497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55734247850443434425949317 10450171471958143954865497)
          ·
            refine ⟨7837628603968607966149123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450171471958143954865497 7837628603968607966149123)
            ·
              refine ⟨11756442905952911949223685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7837628603968607966149123 11756442905952911949223685)
              ·
                refine ⟨2204333044866170990479441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11756442905952911949223685 2204333044866170990479441)
                ·
                  refine ⟨1653249783649628242859581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204333044866170990479441 1653249783649628242859581)
                  ·
                    refine ⟨619968668868610591072343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653249783649628242859581 619968668868610591072343)
                    ·
                      rfl

theorem cell22_1811077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_1811077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811077 prefixEnd_1811077 := by exact prefixLift 1811077
  have htrace : WordTrace (prefixWord ++ tailWord_1811077) baseStart_1811077 baseEnd_1811077 := by
    simpa [prefixWord, tailWord_1811077, baseEnd_1811077] using wordTrace_append hprefix tailTrace_1811077
  have hstable : (prefixWord ++ tailWord_1811077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811077).length < 2 ^ (prefixWord ++ tailWord_1811077).sum := by decide
  have hdescent : baseEnd_1811077 < baseStart_1811077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811088 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_1811088 : Nat := 118140960795 + 1811088 * 2 ^ 59
def prefixEnd_1811088 : Nat := 4983230072969 + 3 ^ 40 * 1811088 * 2
def baseEnd_1811088 : Nat := 619972434393410229047309

theorem tailTrace_1811088 : CollatzResearch.WordTrace tailWord_1811088 prefixEnd_1811088 619972434393410229047309 := by
  unfold tailWord_1811088
  simp only [CollatzResearch.WordTrace]
  refine ⟨33027903031372480025072959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44037204041829973366763945 33027903031372480025072959)
  ·
    refine ⟨49541854547058720037609439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33027903031372480025072959 49541854547058720037609439)
    ·
      refine ⟨74312781820588080056414159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49541854547058720037609439 74312781820588080056414159)
      ·
        refine ⟨111469172730882120084621239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74312781820588080056414159 111469172730882120084621239)
        ·
          refine ⟨167203759096323180126931859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111469172730882120084621239 167203759096323180126931859)
          ·
            refine ⟨250805638644484770190397789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167203759096323180126931859 250805638644484770190397789)
            ·
              refine ⟨94052114491681788821399171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250805638644484770190397789 94052114491681788821399171)
              ·
                refine ⟨141078171737522683232098757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94052114491681788821399171 141078171737522683232098757)
                ·
                  refine ⟨26452157200785503106018517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141078171737522683232098757 26452157200785503106018517)
                  ·
                    refine ⟨619972434393410229047309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26452157200785503106018517 619972434393410229047309)
                    ·
                      rfl

theorem cell22_1811088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_1811088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811088 prefixEnd_1811088 := by exact prefixLift 1811088
  have htrace : WordTrace (prefixWord ++ tailWord_1811088) baseStart_1811088 baseEnd_1811088 := by
    simpa [prefixWord, tailWord_1811088, baseEnd_1811088] using wordTrace_append hprefix tailTrace_1811088
  have hstable : (prefixWord ++ tailWord_1811088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811088).length < 2 ^ (prefixWord ++ tailWord_1811088).sum := by decide
  have hdescent : baseEnd_1811088 < baseStart_1811088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811135 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 7]
def baseStart_1811135 : Nat := 118140960795 + 1811135 * 2 ^ 59
def prefixEnd_1811135 : Nat := 4983230072969 + 3 ^ 40 * 1811135 * 2
def baseEnd_1811135 : Nat := 206662841151305924374055

theorem tailTrace_1811135 : CollatzResearch.WordTrace tailWord_1811135 prefixEnd_1811135 206662841151305924374055 := by
  unfold tailWord_1811135
  simp only [CollatzResearch.WordTrace]
  refine ⟨66057520293574687077106859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44038346862383124718071239 66057520293574687077106859)
  ·
    refine ⟨99086280440362030615660289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66057520293574687077106859 99086280440362030615660289)
    ·
      refine ⟨74314710330271522961745217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99086280440362030615660289 74314710330271522961745217)
      ·
        refine ⟨55736032747703642221308913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74314710330271522961745217 55736032747703642221308913)
        ·
          refine ⟨41802024560777731665981685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55736032747703642221308913 41802024560777731665981685)
          ·
            refine ⟨3918939802572912343685783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41802024560777731665981685 3918939802572912343685783)
            ·
              refine ⟨5878409703859368515528675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918939802572912343685783 5878409703859368515528675)
              ·
                refine ⟨8817614555789052773293013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878409703859368515528675 8817614555789052773293013)
                ·
                  refine ⟨206662841151305924374055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8817614555789052773293013 206662841151305924374055)
                  ·
                    rfl

theorem cell22_1811135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 7].length) (baseStart_1811135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811135 prefixEnd_1811135 := by exact prefixLift 1811135
  have htrace : WordTrace (prefixWord ++ tailWord_1811135) baseStart_1811135 baseEnd_1811135 := by
    simpa [prefixWord, tailWord_1811135, baseEnd_1811135] using wordTrace_append hprefix tailTrace_1811135
  have hstable : (prefixWord ++ tailWord_1811135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811135).length < 2 ^ (prefixWord ++ tailWord_1811135).sum := by decide
  have hdescent : baseEnd_1811135 < baseStart_1811135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811242 : List Nat := [3, 1, 4, 3, 11]
def baseStart_1811242 : Nat := 118140960795 + 1811242 * 2 ^ 59
def prefixEnd_1811242 : Nat := 4983230072969 + 3 ^ 40 * 1811242 * 2
def baseEnd_1811242 : Nat := 2551543834323478027559

theorem tailTrace_1811242 : CollatzResearch.WordTrace tailWord_1811242 prefixEnd_1811242 2551543834323478027559 := by
  unfold tailWord_1811242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515355726046761087812995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44040948602791362900834653 16515355726046761087812995)
  ·
    refine ⟨24773033589070141631719493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16515355726046761087812995 24773033589070141631719493)
    ·
      refine ⟨4644943797950651555947405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24773033589070141631719493 4644943797950651555947405)
      ·
        refine ⟨1741853924231494333480277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4644943797950651555947405 1741853924231494333480277)
        ·
          refine ⟨2551543834323478027559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1741853924231494333480277 2551543834323478027559)
          ·
            rfl

theorem cell22_1811242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 11].length) (baseStart_1811242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811242 prefixEnd_1811242 := by exact prefixLift 1811242
  have htrace : WordTrace (prefixWord ++ tailWord_1811242) baseStart_1811242 baseEnd_1811242 := by
    simpa [prefixWord, tailWord_1811242, baseEnd_1811242] using wordTrace_append hprefix tailTrace_1811242
  have hstable : (prefixWord ++ tailWord_1811242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811242).length < 2 ^ (prefixWord ++ tailWord_1811242).sum := by decide
  have hdescent : baseEnd_1811242 < baseStart_1811242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811246 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1811246 : Nat := 118140960795 + 1811246 * 2 ^ 59
def prefixEnd_1811246 : Nat := 4983230072969 + 3 ^ 40 * 1811246 * 2
def baseEnd_1811246 : Nat := 620026521022350483596825

theorem tailTrace_1811246 : CollatzResearch.WordTrace tailWord_1811246 prefixEnd_1811246 620026521022350483596825 := by
  unfold tailWord_1811246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257696099521569129299699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44041045864115035356265061 8257696099521569129299699)
  ·
    refine ⟨12386544149282353693949549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8257696099521569129299699 12386544149282353693949549)
    ·
      refine ⟨4644954055980882635231081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12386544149282353693949549 4644954055980882635231081)
      ·
        refine ⟨3483715541985661976423311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4644954055980882635231081 3483715541985661976423311)
        ·
          refine ⟨5225573312978492964634967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483715541985661976423311 5225573312978492964634967)
          ·
            refine ⟨7838359969467739446952451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225573312978492964634967 7838359969467739446952451)
            ·
              refine ⟨11757539954201609170428677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7838359969467739446952451 11757539954201609170428677)
              ·
                refine ⟨2204538741412801719455377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11757539954201609170428677 2204538741412801719455377)
                ·
                  refine ⟨1653404056059601289591533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204538741412801719455377 1653404056059601289591533)
                  ·
                    refine ⟨620026521022350483596825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653404056059601289591533 620026521022350483596825)
                    ·
                      rfl

theorem cell22_1811246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1811246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811246 prefixEnd_1811246 := by exact prefixLift 1811246
  have htrace : WordTrace (prefixWord ++ tailWord_1811246) baseStart_1811246 baseEnd_1811246 := by
    simpa [prefixWord, tailWord_1811246, baseEnd_1811246] using wordTrace_append hprefix tailTrace_1811246
  have hstable : (prefixWord ++ tailWord_1811246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811246).length < 2 ^ (prefixWord ++ tailWord_1811246).sum := by decide
  have hdescent : baseEnd_1811246 < baseStart_1811246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811255 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1811255 : Nat := 118140960795 + 1811255 * 2 ^ 59
def prefixEnd_1811255 : Nat := 4983230072969 + 3 ^ 40 * 1811255 * 2
def baseEnd_1811255 : Nat := 620029601906277460121797

theorem tailTrace_1811255 : CollatzResearch.WordTrace tailWord_1811255 prefixEnd_1811255 620029601906277460121797 := by
  unfold tailWord_1811255
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061897053139947571475219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44041264702093298380983479 66061897053139947571475219)
  ·
    refine ⟨99092845579709921357212829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66061897053139947571475219 99092845579709921357212829)
    ·
      refine ⟨37159817092391220508954811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99092845579709921357212829 37159817092391220508954811)
      ·
        refine ⟨55739725638586830763432217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37159817092391220508954811 55739725638586830763432217)
        ·
          refine ⟨41804794228940123072574163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55739725638586830763432217 41804794228940123072574163)
          ·
            refine ⟨62707191343410184608861245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41804794228940123072574163 62707191343410184608861245)
            ·
              refine ⟨23515196753778819228322967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62707191343410184608861245 23515196753778819228322967)
              ·
                refine ⟨35272795130668228842484451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23515196753778819228322967 35272795130668228842484451)
                ·
                  refine ⟨52909192696002343263726677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35272795130668228842484451 52909192696002343263726677)
                  ·
                    refine ⟨620029601906277460121797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52909192696002343263726677 620029601906277460121797)
                    ·
                      rfl

theorem cell22_1811255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1811255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811255 prefixEnd_1811255 := by exact prefixLift 1811255
  have htrace : WordTrace (prefixWord ++ tailWord_1811255) baseStart_1811255 baseEnd_1811255 := by
    simpa [prefixWord, tailWord_1811255, baseEnd_1811255] using wordTrace_append hprefix tailTrace_1811255
  have hstable : (prefixWord ++ tailWord_1811255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811255).length < 2 ^ (prefixWord ++ tailWord_1811255).sum := by decide
  have hdescent : baseEnd_1811255 < baseStart_1811255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811304 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_1811304 : Nat := 118140960795 + 1811304 * 2 ^ 59
def prefixEnd_1811304 : Nat := 4983230072969 + 3 ^ 40 * 1811304 * 2
def baseEnd_1811304 : Nat := 206682125202552555215549

theorem tailTrace_1811304 : CollatzResearch.WordTrace tailWord_1811304 prefixEnd_1811304 206682125202552555215549 := by
  unfold tailWord_1811304
  simp only [CollatzResearch.WordTrace]
  refine ⟨33031842114981214470004483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44042456153308285960005977 33031842114981214470004483)
  ·
    refine ⟨49547763172471821705006725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33031842114981214470004483 49547763172471821705006725)
    ·
      refine ⟨9290205594838466569688761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49547763172471821705006725 9290205594838466569688761)
      ·
        refine ⟨6967654196128849927266571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9290205594838466569688761 6967654196128849927266571)
        ·
          refine ⟨10451481294193274890899857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967654196128849927266571 10451481294193274890899857)
          ·
            refine ⟨7838610970644956168174893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10451481294193274890899857 7838610970644956168174893)
            ·
              refine ⟨2939479113991858563065585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7838610970644956168174893 2939479113991858563065585)
              ·
                refine ⟨2204609335493893922299189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939479113991858563065585 2204609335493893922299189)
                ·
                  refine ⟨206682125202552555215549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2204609335493893922299189 206682125202552555215549)
                  ·
                    rfl

theorem cell22_1811304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_1811304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811304 prefixEnd_1811304 := by exact prefixLift 1811304
  have htrace : WordTrace (prefixWord ++ tailWord_1811304) baseStart_1811304 baseEnd_1811304 := by
    simpa [prefixWord, tailWord_1811304, baseEnd_1811304] using wordTrace_append hprefix tailTrace_1811304
  have hstable : (prefixWord ++ tailWord_1811304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811304).length < 2 ^ (prefixWord ++ tailWord_1811304).sum := by decide
  have hdescent : baseEnd_1811304 < baseStart_1811304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811364 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1811364 : Nat := 118140960795 + 1811364 * 2 ^ 59
def prefixEnd_1811364 : Nat := 4983230072969 + 3 ^ 40 * 1811364 * 2
def baseEnd_1811364 : Nat := 620066914833837509146463

theorem tailTrace_1811364 : CollatzResearch.WordTrace tailWord_1811364 prefixEnd_1811364 620066914833837509146463 := by
  unfold tailWord_1811364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33032936304872529593596573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44043915073163372791462097 33032936304872529593596573)
  ·
    refine ⟨12387351114327198597598715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33032936304872529593596573 12387351114327198597598715)
    ·
      refine ⟨18581026671490797896398073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12387351114327198597598715 18581026671490797896398073)
      ·
        refine ⟨13935770003618098422298555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18581026671490797896398073 13935770003618098422298555)
        ·
          refine ⟨20903655005427147633447833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13935770003618098422298555 20903655005427147633447833)
          ·
            refine ⟨15677741254070360725085875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20903655005427147633447833 15677741254070360725085875)
            ·
              refine ⟨23516611881105541087628813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15677741254070360725085875 23516611881105541087628813)
              ·
                refine ⟨8818729455414577907860805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23516611881105541087628813 8818729455414577907860805)
                ·
                  refine ⟨1653511772890233357723901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8818729455414577907860805 1653511772890233357723901)
                  ·
                    refine ⟨620066914833837509146463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653511772890233357723901 620066914833837509146463)
                    ·
                      rfl

theorem cell22_1811364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1811364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811364 prefixEnd_1811364 := by exact prefixLift 1811364
  have htrace : WordTrace (prefixWord ++ tailWord_1811364) baseStart_1811364 baseEnd_1811364 := by
    simpa [prefixWord, tailWord_1811364, baseEnd_1811364] using wordTrace_append hprefix tailTrace_1811364
  have hstable : (prefixWord ++ tailWord_1811364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811364).length < 2 ^ (prefixWord ++ tailWord_1811364).sum := by decide
  have hdescent : baseEnd_1811364 < baseStart_1811364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811381 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1811381 : Nat := 118140960795 + 1811381 * 2 ^ 59
def prefixEnd_1811381 : Nat := 4983230072969 + 3 ^ 40 * 1811381 * 2
def baseEnd_1811381 : Nat := 620072734281255131471411

theorem tailTrace_1811381 : CollatzResearch.WordTrace tailWord_1811381 prefixEnd_1811381 620072734281255131471411 := by
  unfold tailWord_1811381
  simp only [CollatzResearch.WordTrace]
  refine ⟨66066492650683471090561997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44044328433788980727041331 66066492650683471090561997)
  ·
    refine ⟨24774934744006301658960749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66066492650683471090561997 24774934744006301658960749)
    ·
      refine ⟨9290600529002363122110281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24774934744006301658960749 9290600529002363122110281)
      ·
        refine ⟨6967950396751772341582711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9290600529002363122110281 6967950396751772341582711)
        ·
          refine ⟨10451925595127658512374067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967950396751772341582711 10451925595127658512374067)
          ·
            refine ⟨15677888392691487768561101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451925595127658512374067 15677888392691487768561101)
            ·
              refine ⟨5879208147259307913210413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15677888392691487768561101 5879208147259307913210413)
              ·
                refine ⟨2204703055222240467453905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5879208147259307913210413 2204703055222240467453905)
                ·
                  refine ⟨1653527291416680350590429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204703055222240467453905 1653527291416680350590429)
                  ·
                    refine ⟨620072734281255131471411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653527291416680350590429 620072734281255131471411)
                    ·
                      rfl

theorem cell22_1811381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1811381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811381 prefixEnd_1811381 := by exact prefixLift 1811381
  have htrace : WordTrace (prefixWord ++ tailWord_1811381) baseStart_1811381 baseEnd_1811381 := by
    simpa [prefixWord, tailWord_1811381, baseEnd_1811381] using wordTrace_append hprefix tailTrace_1811381
  have hstable : (prefixWord ++ tailWord_1811381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811381).length < 2 ^ (prefixWord ++ tailWord_1811381).sum := by decide
  have hdescent : baseEnd_1811381 < baseStart_1811381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811439 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 5]
def baseStart_1811439 : Nat := 118140960795 + 1811439 * 2 ^ 59
def prefixEnd_1811439 : Nat := 4983230072969 + 3 ^ 40 * 1811439 * 2
def baseEnd_1811439 : Nat := 206697529622187437840411

theorem tailTrace_1811439 : CollatzResearch.WordTrace tailWord_1811439 prefixEnd_1811439 206697529622187437840411 := by
  unfold tailWord_1811439
  simp only [CollatzResearch.WordTrace]
  refine ⟨66068608084473346996173371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44045738722982231330782247 66068608084473346996173371)
  ·
    refine ⟨99102912126710020494260057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66068608084473346996173371 99102912126710020494260057)
    ·
      refine ⟨74327184095032515370695043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99102912126710020494260057 74327184095032515370695043)
      ·
        refine ⟨111490776142548773056042565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74327184095032515370695043 111490776142548773056042565)
        ·
          refine ⟨20904520526727894948007981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111490776142548773056042565 20904520526727894948007981)
          ·
            refine ⟨7839195197522960605502993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20904520526727894948007981 7839195197522960605502993)
            ·
              refine ⟨5879396398142220454127245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839195197522960605502993 5879396398142220454127245)
              ·
                refine ⟨2204773649303332670297717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5879396398142220454127245 2204773649303332670297717)
                ·
                  refine ⟨206697529622187437840411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2204773649303332670297717 206697529622187437840411)
                  ·
                    rfl

theorem cell22_1811439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 5].length) (baseStart_1811439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811439 prefixEnd_1811439 := by exact prefixLift 1811439
  have htrace : WordTrace (prefixWord ++ tailWord_1811439) baseStart_1811439 baseEnd_1811439 := by
    simpa [prefixWord, tailWord_1811439, baseEnd_1811439] using wordTrace_append hprefix tailTrace_1811439
  have hstable : (prefixWord ++ tailWord_1811439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811439).length < 2 ^ (prefixWord ++ tailWord_1811439).sum := by decide
  have hdescent : baseEnd_1811439 < baseStart_1811439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811514 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1811514 : Nat := 118140960795 + 1811514 * 2 ^ 59
def prefixEnd_1811514 : Nat := 4983230072969 + 3 ^ 40 * 1811514 * 2
def baseEnd_1811514 : Nat := 620118262899287117896003

theorem tailTrace_1811514 : CollatzResearch.WordTrace tailWord_1811514 prefixEnd_1811514 620118262899287117896003 := by
  unfold tailWord_1811514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16517835889800408701288399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44047562372801089870102397 16517835889800408701288399)
  ·
    refine ⟨24776753834700613051932599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16517835889800408701288399 24776753834700613051932599)
    ·
      refine ⟨37165130752050919577898899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24776753834700613051932599 37165130752050919577898899)
      ·
        refine ⟨55747696128076379366848349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37165130752050919577898899 55747696128076379366848349)
        ·
          refine ⟨20905386048028642262568131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55747696128076379366848349 20905386048028642262568131)
          ·
            refine ⟨31358079072042963393852197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20905386048028642262568131 31358079072042963393852197)
            ·
              refine ⟨5879639826008055636347287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31358079072042963393852197 5879639826008055636347287)
              ·
                refine ⟨8819459739012083454520931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879639826008055636347287 8819459739012083454520931)
                ·
                  refine ⟨13229189608518125181781397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819459739012083454520931 13229189608518125181781397)
                  ·
                    refine ⟨620118262899287117896003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13229189608518125181781397 620118262899287117896003)
                    ·
                      rfl

theorem cell22_1811514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1811514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811514 prefixEnd_1811514 := by exact prefixLift 1811514
  have htrace : WordTrace (prefixWord ++ tailWord_1811514) baseStart_1811514 baseEnd_1811514 := by
    simpa [prefixWord, tailWord_1811514, baseEnd_1811514] using wordTrace_append hprefix tailTrace_1811514
  have hstable : (prefixWord ++ tailWord_1811514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811514).length < 2 ^ (prefixWord ++ tailWord_1811514).sum := by decide
  have hdescent : baseEnd_1811514 < baseStart_1811514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811516 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_1811516 : Nat := 118140960795 + 1811516 * 2 ^ 59
def prefixEnd_1811516 : Nat := 4983230072969 + 3 ^ 40 * 1811516 * 2
def baseEnd_1811516 : Nat := 620118947540159779345997

theorem tailTrace_1811516 : CollatzResearch.WordTrace tailWord_1811516 prefixEnd_1811516 620118947540159779345997 := by
  unfold tailWord_1811516
  simp only [CollatzResearch.WordTrace]
  refine ⟨33035708252597194573363201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44047611003462926097817601 33035708252597194573363201)
  ·
    refine ⟨24776781189447895930022401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33035708252597194573363201 24776781189447895930022401)
    ·
      refine ⟨18582585892085921947516801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24776781189447895930022401 18582585892085921947516801)
      ·
        refine ⟨13936939419064441460637601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18582585892085921947516801 13936939419064441460637601)
        ·
          refine ⟨10452704564298331095478201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13936939419064441460637601 10452704564298331095478201)
          ·
            refine ⟨7839528423223748321608651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10452704564298331095478201 7839528423223748321608651)
            ·
              refine ⟨11759292634835622482412977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7839528423223748321608651 11759292634835622482412977)
              ·
                refine ⟨8819469476126716861809733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11759292634835622482412977 8819469476126716861809733)
                ·
                  refine ⟨1653650526773759411589325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8819469476126716861809733 1653650526773759411589325)
                  ·
                    refine ⟨620118947540159779345997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653650526773759411589325 620118947540159779345997)
                    ·
                      rfl

theorem cell22_1811516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_1811516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811516 prefixEnd_1811516 := by exact prefixLift 1811516
  have htrace : WordTrace (prefixWord ++ tailWord_1811516) baseStart_1811516 baseEnd_1811516 := by
    simpa [prefixWord, tailWord_1811516, baseEnd_1811516] using wordTrace_append hprefix tailTrace_1811516
  have hstable : (prefixWord ++ tailWord_1811516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811516).length < 2 ^ (prefixWord ++ tailWord_1811516).sum := by decide
  have hdescent : baseEnd_1811516 < baseStart_1811516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811533 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1811533 : Nat := 118140960795 + 1811533 * 2 ^ 59
def prefixEnd_1811533 : Nat := 4983230072969 + 3 ^ 40 * 1811533 * 2
def baseEnd_1811533 : Nat := 620124766987577401670945

theorem tailTrace_1811533 : CollatzResearch.WordTrace tailWord_1811533 prefixEnd_1811533 620124766987577401670945 := by
  unfold tailWord_1811533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66072036546132801050095253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44048024364088534033396835 66072036546132801050095253)
  ·
    refine ⟨3097126713099975049223215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66072036546132801050095253 3097126713099975049223215)
    ·
      refine ⟨4645690069649962573834823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097126713099975049223215 4645690069649962573834823)
      ·
        refine ⟨6968535104474943860752235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645690069649962573834823 6968535104474943860752235)
        ·
          refine ⟨10452802656712415791128353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6968535104474943860752235 10452802656712415791128353)
          ·
            refine ⟨7839601992534311843346265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10452802656712415791128353 7839601992534311843346265)
            ·
              refine ⟨5879701494400733882509699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839601992534311843346265 5879701494400733882509699)
              ·
                refine ⟨8819552241601100823764549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879701494400733882509699 8819552241601100823764549)
                ·
                  refine ⟨1653666045300206404455853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8819552241601100823764549 1653666045300206404455853)
                  ·
                    refine ⟨620124766987577401670945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653666045300206404455853 620124766987577401670945)
                    ·
                      rfl

theorem cell22_1811533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1811533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811533 prefixEnd_1811533 := by exact prefixLift 1811533
  have htrace : WordTrace (prefixWord ++ tailWord_1811533) baseStart_1811533 baseEnd_1811533 := by
    simpa [prefixWord, tailWord_1811533, baseEnd_1811533] using wordTrace_append hprefix tailTrace_1811533
  have hstable : (prefixWord ++ tailWord_1811533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811533).length < 2 ^ (prefixWord ++ tailWord_1811533).sum := by decide
  have hdescent : baseEnd_1811533 < baseStart_1811533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811621 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_1811621 : Nat := 118140960795 + 1811621 * 2 ^ 59
def prefixEnd_1811621 : Nat := 4983230072969 + 3 ^ 40 * 1811621 * 2
def baseEnd_1811621 : Nat := 620154891185974505470675

theorem tailTrace_1811621 : CollatzResearch.WordTrace tailWord_1811621 prefixEnd_1811621 620154891185974505470675 := by
  unfold tailWord_1811621
  simp only [CollatzResearch.WordTrace]
  refine ⟨66075246169813992079298717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44050164113209328052865811 66075246169813992079298717)
  ·
    refine ⟨24778217313680247029737019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66075246169813992079298717 24778217313680247029737019)
    ·
      refine ⟨37167325970520370544605529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24778217313680247029737019 37167325970520370544605529)
      ·
        refine ⟨27875494477890277908454147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37167325970520370544605529 27875494477890277908454147)
        ·
          refine ⟨41813241716835416862681221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27875494477890277908454147 41813241716835416862681221)
          ·
            refine ⟨7839982821906640661752729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41813241716835416862681221 7839982821906640661752729)
            ·
              refine ⟨5879987116429980496314547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839982821906640661752729 5879987116429980496314547)
              ·
                refine ⟨8819980674644970744471821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879987116429980496314547 8819980674644970744471821)
                ·
                  refine ⟨3307492752991864029176933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8819980674644970744471821 3307492752991864029176933)
                  ·
                    refine ⟨620154891185974505470675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3307492752991864029176933 620154891185974505470675)
                    ·
                      rfl

theorem cell22_1811621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_1811621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811621 prefixEnd_1811621 := by exact prefixLift 1811621
  have htrace : WordTrace (prefixWord ++ tailWord_1811621) baseStart_1811621 baseEnd_1811621 := by
    simpa [prefixWord, tailWord_1811621, baseEnd_1811621] using wordTrace_append hprefix tailTrace_1811621
  have hstable : (prefixWord ++ tailWord_1811621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811621).length < 2 ^ (prefixWord ++ tailWord_1811621).sum := by decide
  have hdescent : baseEnd_1811621 < baseStart_1811621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811666 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1811666 : Nat := 118140960795 + 1811666 * 2 ^ 59
def prefixEnd_1811666 : Nat := 4983230072969 + 3 ^ 40 * 1811666 * 2
def baseEnd_1811666 : Nat := 620170295605609388095537

theorem tailTrace_1811666 : CollatzResearch.WordTrace tailWord_1811666 prefixEnd_1811666 620170295605609388095537 := by
  unfold tailWord_1811666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16519221863662741191171713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44051258303100643176457901 16519221863662741191171713)
  ·
    refine ⟨12389416397747055893378785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16519221863662741191171713 12389416397747055893378785)
    ·
      refine ⟨9292062298310291920034089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12389416397747055893378785 9292062298310291920034089)
      ·
        refine ⟨6969046723732718940025567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9292062298310291920034089 6969046723732718940025567)
        ·
          refine ⟨10453570085599078410038351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969046723732718940025567 10453570085599078410038351)
          ·
            refine ⟨15680355128398617615057527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453570085599078410038351 15680355128398617615057527)
            ·
              refine ⟨23520532692597926422586291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680355128398617615057527 23520532692597926422586291)
              ·
                refine ⟨35280799038896889633879437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23520532692597926422586291 35280799038896889633879437)
                ·
                  refine ⟨13230299639586333612704789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35280799038896889633879437 13230299639586333612704789)
                  ·
                    refine ⟨620170295605609388095537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13230299639586333612704789 620170295605609388095537)
                    ·
                      rfl

theorem cell22_1811666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1811666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811666 prefixEnd_1811666 := by exact prefixLift 1811666
  have htrace : WordTrace (prefixWord ++ tailWord_1811666) baseStart_1811666 baseEnd_1811666 := by
    simpa [prefixWord, tailWord_1811666, baseEnd_1811666] using wordTrace_append hprefix tailTrace_1811666
  have hstable : (prefixWord ++ tailWord_1811666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811666).length < 2 ^ (prefixWord ++ tailWord_1811666).sum := by decide
  have hdescent : baseEnd_1811666 < baseStart_1811666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811681 : List Nat := [1, 2, 3, 1, 3, 3, 1, 8]
def baseStart_1811681 : Nat := 118140960795 + 1811681 * 2 ^ 59
def prefixEnd_1811681 : Nat := 4983230072969 + 3 ^ 40 * 1811681 * 2
def baseEnd_1811681 : Nat := 68908381156906038774499

theorem tailTrace_1811681 : CollatzResearch.WordTrace tailWord_1811681 prefixEnd_1811681 68908381156906038774499 := by
  unfold tailWord_1811681
  simp only [CollatzResearch.WordTrace]
  refine ⟨66077434549596622326482897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44051623033064414884321931 66077434549596622326482897)
  ·
    refine ⟨49558075912197466744862173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66077434549596622326482897 49558075912197466744862173)
    ·
      refine ⟨18584278467074050029323315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49558075912197466744862173 18584278467074050029323315)
      ·
        refine ⟨27876417700611075043984973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18584278467074050029323315 27876417700611075043984973)
        ·
          refine ⟨10453656637729153141494365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27876417700611075043984973 10453656637729153141494365)
          ·
            refine ⟨3920121239148432428060387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10453656637729153141494365 3920121239148432428060387)
            ·
              refine ⟨5880181858722648642090581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920121239148432428060387 5880181858722648642090581)
              ·
                refine ⟨68908381156906038774499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5880181858722648642090581 68908381156906038774499)
                ·
                  rfl

theorem cell22_1811681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 8].length) (baseStart_1811681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811681 prefixEnd_1811681 := by exact prefixLift 1811681
  have htrace : WordTrace (prefixWord ++ tailWord_1811681) baseStart_1811681 baseEnd_1811681 := by
    simpa [prefixWord, tailWord_1811681, baseEnd_1811681] using wordTrace_append hprefix tailTrace_1811681
  have hstable : (prefixWord ++ tailWord_1811681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811681).length < 2 ^ (prefixWord ++ tailWord_1811681).sum := by decide
  have hdescent : baseEnd_1811681 < baseStart_1811681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811687 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 4]
def baseStart_1811687 : Nat := 118140960795 + 1811687 * 2 ^ 59
def prefixEnd_1811687 : Nat := 4983230072969 + 3 ^ 40 * 1811687 * 2
def baseEnd_1811687 : Nat := 206725828111590777773491

theorem tailTrace_1811687 : CollatzResearch.WordTrace tailWord_1811687 prefixEnd_1811687 206725828111590777773491 := by
  unfold tailWord_1811687
  simp only [CollatzResearch.WordTrace]
  refine ⟨66077653387574885351201315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44051768925049923567467543 66077653387574885351201315)
  ·
    refine ⟨99116480081362328026801973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66077653387574885351201315 99116480081362328026801973)
    ·
      refine ⟨9292170007627718252512685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99116480081362328026801973 9292170007627718252512685)
      ·
        refine ⟨3484563752860394344692257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9292170007627718252512685 3484563752860394344692257)
        ·
          refine ⟨2613422814645295758519193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3484563752860394344692257 2613422814645295758519193)
          ·
            refine ⟨1960067110983971818889395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2613422814645295758519193 1960067110983971818889395)
            ·
              refine ⟨2940100666475957728334093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960067110983971818889395 2940100666475957728334093)
              ·
                refine ⟨1102537749928484148125285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2940100666475957728334093 1102537749928484148125285)
                ·
                  refine ⟨206725828111590777773491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1102537749928484148125285 206725828111590777773491)
                  ·
                    rfl

theorem cell22_1811687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 4].length) (baseStart_1811687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811687 prefixEnd_1811687 := by exact prefixLift 1811687
  have htrace : WordTrace (prefixWord ++ tailWord_1811687) baseStart_1811687 baseEnd_1811687 := by
    simpa [prefixWord, tailWord_1811687, baseEnd_1811687] using wordTrace_append hprefix tailTrace_1811687
  have hstable : (prefixWord ++ tailWord_1811687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811687).length < 2 ^ (prefixWord ++ tailWord_1811687).sum := by decide
  have hdescent : baseEnd_1811687 < baseStart_1811687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811698 : List Nat := [3, 2, 1, 3, 3, 2, 8]
def baseStart_1811698 : Nat := 118140960795 + 1811698 * 2 ^ 59
def prefixEnd_1811698 : Nat := 4983230072969 + 3 ^ 40 * 1811698 * 2
def baseEnd_1811698 : Nat := 22969675920724887825757

theorem tailTrace_1811698 : CollatzResearch.WordTrace tailWord_1811698 prefixEnd_1811698 22969675920724887825757 := by
  unfold tailWord_1811698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16519513647633758557462937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44052036393690022819901165 16519513647633758557462937)
  ·
    refine ⟨12389635235725318918097203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16519513647633758557462937 12389635235725318918097203)
    ·
      refine ⟨18584452853587978377145805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389635235725318918097203 18584452853587978377145805)
      ·
        refine ⟨6969169820095491891429677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18584452853587978377145805 6969169820095491891429677)
        ·
          refine ⟨2613438682535809459286129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6969169820095491891429677 2613438682535809459286129)
          ·
            refine ⟨1960079011901857094464597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2613438682535809459286129 1960079011901857094464597)
            ·
              refine ⟨22969675920724887825757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1960079011901857094464597 22969675920724887825757)
              ·
                rfl

theorem cell22_1811698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 8].length) (baseStart_1811698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811698 prefixEnd_1811698 := by exact prefixLift 1811698
  have htrace : WordTrace (prefixWord ++ tailWord_1811698) baseStart_1811698 baseEnd_1811698 := by
    simpa [prefixWord, tailWord_1811698, baseEnd_1811698] using wordTrace_append hprefix tailTrace_1811698
  have hstable : (prefixWord ++ tailWord_1811698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811698).length < 2 ^ (prefixWord ++ tailWord_1811698).sum := by decide
  have hdescent : baseEnd_1811698 < baseStart_1811698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811788 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_1811788 : Nat := 118140960795 + 1811788 * 2 ^ 59
def prefixEnd_1811788 : Nat := 4983230072969 + 3 ^ 40 * 1811788 * 2
def baseEnd_1811788 : Nat := 206737352899613912181721

theorem tailTrace_1811788 : CollatzResearch.WordTrace tailWord_1811788 prefixEnd_1811788 206737352899613912181721 := by
  unfold tailWord_1811788
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040668580104489800314009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44054224773472653067085345 33040668580104489800314009)
  ·
    refine ⟨24780501435078367350235507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33040668580104489800314009 24780501435078367350235507)
    ·
      refine ⟨37170752152617551025353261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24780501435078367350235507 37170752152617551025353261)
      ·
        refine ⟨13939032057231581634507473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37170752152617551025353261 13939032057231581634507473)
        ·
          refine ⟨10454274042923686225880605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13939032057231581634507473 10454274042923686225880605)
          ·
            refine ⟨3920352766096382334705227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10454274042923686225880605 3920352766096382334705227)
            ·
              refine ⟨5880529149144573502057841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920352766096382334705227 5880529149144573502057841)
              ·
                refine ⟨4410396861858430126543381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880529149144573502057841 4410396861858430126543381)
                ·
                  refine ⟨206737352899613912181721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4410396861858430126543381 206737352899613912181721)
                  ·
                    rfl

theorem cell22_1811788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_1811788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811788 prefixEnd_1811788 := by exact prefixLift 1811788
  have htrace : WordTrace (prefixWord ++ tailWord_1811788) baseStart_1811788 baseEnd_1811788 := by
    simpa [prefixWord, tailWord_1811788, baseEnd_1811788] using wordTrace_append hprefix tailTrace_1811788
  have hstable : (prefixWord ++ tailWord_1811788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811788).length < 2 ^ (prefixWord ++ tailWord_1811788).sum := by decide
  have hdescent : baseEnd_1811788 < baseStart_1811788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811820 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_1811820 : Nat := 118140960795 + 1811820 * 2 ^ 59
def prefixEnd_1811820 : Nat := 4983230072969 + 3 ^ 40 * 1811820 * 2
def baseEnd_1811820 : Nat := 620223012952804319745065

theorem tailTrace_1811820 : CollatzResearch.WordTrace tailWord_1811820 prefixEnd_1811820 620223012952804319745065 := by
  unfold tailWord_1811820
  simp only [CollatzResearch.WordTrace]
  refine ⟨33041252148046524532896457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44055002864062032710528609 33041252148046524532896457)
  ·
    refine ⟨24780939111034893399672343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33041252148046524532896457 24780939111034893399672343)
    ·
      refine ⟨37171408666552340099508515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24780939111034893399672343 37171408666552340099508515)
      ·
        refine ⟨55757112999828510149262773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37171408666552340099508515 55757112999828510149262773)
        ·
          refine ⟨5227229343733922826493385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55757112999828510149262773 5227229343733922826493385)
          ·
            refine ⟨3920422007800442119870039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227229343733922826493385 3920422007800442119870039)
            ·
              refine ⟨5880633011700663179805059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920422007800442119870039 5880633011700663179805059)
              ·
                refine ⟨8820949517550994769707589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880633011700663179805059 8820949517550994769707589)
                ·
                  refine ⟨1653928034540811519320173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8820949517550994769707589 1653928034540811519320173)
                  ·
                    refine ⟨620223012952804319745065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653928034540811519320173 620223012952804319745065)
                    ·
                      rfl

theorem cell22_1811820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_1811820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811820 prefixEnd_1811820 := by exact prefixLift 1811820
  have htrace : WordTrace (prefixWord ++ tailWord_1811820) baseStart_1811820 baseEnd_1811820 := by
    simpa [prefixWord, tailWord_1811820, baseEnd_1811820] using wordTrace_append hprefix tailTrace_1811820
  have hstable : (prefixWord ++ tailWord_1811820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811820).length < 2 ^ (prefixWord ++ tailWord_1811820).sum := by decide
  have hdescent : baseEnd_1811820 < baseStart_1811820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811822 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_1811822 : Nat := 118140960795 + 1811822 * 2 ^ 59
def prefixEnd_1811822 : Nat := 4983230072969 + 3 ^ 40 * 1811822 * 2
def baseEnd_1811822 : Nat := 206741232531225660398353

theorem tailTrace_1811822 : CollatzResearch.WordTrace tailWord_1811822 prefixEnd_1811822 206741232531225660398353 := by
  unfold tailWord_1811822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260322155260725425920715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44055051494723868938243813 8260322155260725425920715)
  ·
    refine ⟨12390483232891088138881073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8260322155260725425920715 12390483232891088138881073)
    ·
      refine ⟨9292862424668316104160805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12390483232891088138881073 9292862424668316104160805)
      ·
        refine ⟨1742411704625309269530151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9292862424668316104160805 1742411704625309269530151)
        ·
          refine ⟨2613617556937963904295227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742411704625309269530151 2613617556937963904295227)
          ·
            refine ⟨3920426335406945856442841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613617556937963904295227 3920426335406945856442841)
            ·
              refine ⟨2940319751555209392332131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3920426335406945856442841 2940319751555209392332131)
              ·
                refine ⟨4410479627332814088498197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940319751555209392332131 4410479627332814088498197)
                ·
                  refine ⟨206741232531225660398353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4410479627332814088498197 206741232531225660398353)
                  ·
                    rfl

theorem cell22_1811822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_1811822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811822 prefixEnd_1811822 := by exact prefixLift 1811822
  have htrace : WordTrace (prefixWord ++ tailWord_1811822) baseStart_1811822 baseEnd_1811822 := by
    simpa [prefixWord, tailWord_1811822, baseEnd_1811822] using wordTrace_append hprefix tailTrace_1811822
  have hstable : (prefixWord ++ tailWord_1811822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811822).length < 2 ^ (prefixWord ++ tailWord_1811822).sum := by decide
  have hdescent : baseEnd_1811822 < baseStart_1811822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811837 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_1811837 : Nat := 118140960795 + 1811837 * 2 ^ 59
def prefixEnd_1811837 : Nat := 4983230072969 + 3 ^ 40 * 1811837 * 2
def baseEnd_1811837 : Nat := 620228832400221942070013

theorem tailTrace_1811837 : CollatzResearch.WordTrace tailWord_1811837 prefixEnd_1811837 620228832400221942070013 := by
  unfold tailWord_1811837
  simp only [CollatzResearch.WordTrace]
  refine ⟨66083124337031460969161765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44055416224687640646107843 66083124337031460969161765)
  ·
    refine ⟨12390585813193398931717831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66083124337031460969161765 12390585813193398931717831)
    ·
      refine ⟨18585878719790098397576747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390585813193398931717831 18585878719790098397576747)
      ·
        refine ⟨27878818079685147596365121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18585878719790098397576747 27878818079685147596365121)
        ·
          refine ⟨20909113559763860697273841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27878818079685147596365121 20909113559763860697273841)
          ·
            refine ⟨15681835169822895522955381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20909113559763860697273841 15681835169822895522955381)
            ·
              refine ⟨1470172047170896455277067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15681835169822895522955381 1470172047170896455277067)
              ·
                refine ⟨2205258070756344682915601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470172047170896455277067 2205258070756344682915601)
                ·
                  refine ⟨1653943553067258512186701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2205258070756344682915601 1653943553067258512186701)
                  ·
                    refine ⟨620228832400221942070013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1653943553067258512186701 620228832400221942070013)
                    ·
                      rfl

theorem cell22_1811837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_1811837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811837 prefixEnd_1811837 := by exact prefixLift 1811837
  have htrace : WordTrace (prefixWord ++ tailWord_1811837) baseStart_1811837 baseEnd_1811837 := by
    simpa [prefixWord, tailWord_1811837, baseEnd_1811837] using wordTrace_append hprefix tailTrace_1811837
  have hstable : (prefixWord ++ tailWord_1811837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811837).length < 2 ^ (prefixWord ++ tailWord_1811837).sum := by decide
  have hdescent : baseEnd_1811837 < baseStart_1811837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811957 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 6]
def baseStart_1811957 : Nat := 118140960795 + 1811957 * 2 ^ 59
def prefixEnd_1811957 : Nat := 4983230072969 + 3 ^ 40 * 1811957 * 2
def baseEnd_1811957 : Nat := 206756636950860543023215

theorem tailTrace_1811957 : CollatzResearch.WordTrace tailWord_1811957 prefixEnd_1811957 206756636950860543023215 := by
  unfold tailWord_1811957
  simp only [CollatzResearch.WordTrace]
  refine ⟨66087501096596721463530125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44058334064397814309020083 66087501096596721463530125)
  ·
    refine ⟨24782812911223770548823797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66087501096596721463530125 24782812911223770548823797)
    ·
      refine ⟨2323388710427228488952231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24782812911223770548823797 2323388710427228488952231)
      ·
        refine ⟨3485083065640842733428347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323388710427228488952231 3485083065640842733428347)
        ·
          refine ⟨5227624598461264100142521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3485083065640842733428347 5227624598461264100142521)
          ·
            refine ⟨3920718448845948075106891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227624598461264100142521 3920718448845948075106891)
            ·
              refine ⟨5881077673268922112660337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920718448845948075106891 5881077673268922112660337)
              ·
                refine ⟨4410808254951691584495253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5881077673268922112660337 4410808254951691584495253)
                ·
                  refine ⟨206756636950860543023215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4410808254951691584495253 206756636950860543023215)
                  ·
                    rfl

theorem cell22_1811957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_1811957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811957 prefixEnd_1811957 := by exact prefixLift 1811957
  have htrace : WordTrace (prefixWord ++ tailWord_1811957) baseStart_1811957 baseEnd_1811957 := by
    simpa [prefixWord, tailWord_1811957, baseEnd_1811957] using wordTrace_append hprefix tailTrace_1811957
  have hstable : (prefixWord ++ tailWord_1811957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811957).length < 2 ^ (prefixWord ++ tailWord_1811957).sum := by decide
  have hdescent : baseEnd_1811957 < baseStart_1811957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811989 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1811989 : Nat := 118140960795 + 1811989 * 2 ^ 59
def prefixEnd_1811989 : Nat := 4983230072969 + 3 ^ 40 * 1811989 * 2
def baseEnd_1811989 : Nat := 620280865106544212269547

theorem tailTrace_1811989 : CollatzResearch.WordTrace tailWord_1811989 prefixEnd_1811989 620280865106544212269547 := by
  unfold tailWord_1811989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66088668232480790928695021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44059112154987193952463347 66088668232480790928695021)
  ·
    refine ⟨24783250587180296598260633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66088668232480790928695021 24783250587180296598260633)
    ·
      refine ⟨18587437940385222448695475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24783250587180296598260633 18587437940385222448695475)
      ·
        refine ⟨27881156910577833673043213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18587437940385222448695475 27881156910577833673043213)
        ·
          refine ⟨10455433841466687627391205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27881156910577833673043213 10455433841466687627391205)
          ·
            refine ⟨1960393845275003930135851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10455433841466687627391205 1960393845275003930135851)
            ·
              refine ⟨2940590767912505895203777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960393845275003930135851 2940590767912505895203777)
              ·
                refine ⟨2205443075934379421402833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940590767912505895203777 2205443075934379421402833)
                ·
                  refine ⟨1654082306950784566052125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2205443075934379421402833 1654082306950784566052125)
                  ·
                    refine ⟨620280865106544212269547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654082306950784566052125 620280865106544212269547)
                    ·
                      rfl

theorem cell22_1811989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1811989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1811989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1811989 prefixEnd_1811989 := by exact prefixLift 1811989
  have htrace : WordTrace (prefixWord ++ tailWord_1811989) baseStart_1811989 baseEnd_1811989 := by
    simpa [prefixWord, tailWord_1811989, baseEnd_1811989] using wordTrace_append hprefix tailTrace_1811989
  have hstable : (prefixWord ++ tailWord_1811989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811989).length < 2 ^ (prefixWord ++ tailWord_1811989).sum := by decide
  have hdescent : baseEnd_1811989 < baseStart_1811989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812092 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 4]
def baseStart_1812092 : Nat := 118140960795 + 1812092 * 2 ^ 59
def prefixEnd_1812092 : Nat := 4983230072969 + 3 ^ 40 * 1812092 * 2
def baseEnd_1812092 : Nat := 206772041370495425648077

theorem tailTrace_1812092 : CollatzResearch.WordTrace tailWord_1812092 prefixEnd_1812092 206772041370495425648077 := by
  unfold tailWord_1812092
  simp only [CollatzResearch.WordTrace]
  refine ⟨33046212475553819759847265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44061616634071759679796353 33046212475553819759847265)
  ·
    refine ⟨24784659356665364819885449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33046212475553819759847265 24784659356665364819885449)
    ·
      refine ⟨18588494517499023614914087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24784659356665364819885449 18588494517499023614914087)
      ·
        refine ⟨27882741776248535422371131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18588494517499023614914087 27882741776248535422371131)
        ·
          refine ⟨41824112664372803133556697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27882741776248535422371131 41824112664372803133556697)
          ·
            refine ⟨31368084498279602350167523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41824112664372803133556697 31368084498279602350167523)
            ·
              refine ⟨47052126747419403525251285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31368084498279602350167523 47052126747419403525251285)
              ·
                refine ⟨1102784220642642270123077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47052126747419403525251285 1102784220642642270123077)
                ·
                  refine ⟨206772041370495425648077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1102784220642642270123077 206772041370495425648077)
                  ·
                    rfl

theorem cell22_1812092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_1812092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812092 prefixEnd_1812092 := by exact prefixLift 1812092
  have htrace : WordTrace (prefixWord ++ tailWord_1812092) baseStart_1812092 baseEnd_1812092 := by
    simpa [prefixWord, tailWord_1812092, baseEnd_1812092] using wordTrace_append hprefix tailTrace_1812092
  have hstable : (prefixWord ++ tailWord_1812092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812092).length < 2 ^ (prefixWord ++ tailWord_1812092).sum := by decide
  have hdescent : baseEnd_1812092 < baseStart_1812092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812124 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1812124 : Nat := 118140960795 + 1812124 * 2 ^ 59
def prefixEnd_1812124 : Nat := 4983230072969 + 3 ^ 40 * 1812124 * 2
def baseEnd_1812124 : Nat := 620327078365448860144133

theorem tailTrace_1812124 : CollatzResearch.WordTrace tailWord_1812124 prefixEnd_1812124 620327078365448860144133 := by
  unfold tailWord_1812124
  simp only [CollatzResearch.WordTrace]
  refine ⟨33046796043495854492429713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44062394724661139323239617 33046796043495854492429713)
  ·
    refine ⟨24785097032621890869322285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33046796043495854492429713 24785097032621890869322285)
    ·
      refine ⟨9294411387233209075995857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24785097032621890869322285 9294411387233209075995857)
      ·
        refine ⟨6970808540424906806996893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9294411387233209075995857 6970808540424906806996893)
        ·
          refine ⟨2614053202659340052623835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6970808540424906806996893 2614053202659340052623835)
          ·
            refine ⟨3921079803989010078935753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614053202659340052623835 3921079803989010078935753)
            ·
              refine ⟨2940809852991757559201815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921079803989010078935753 2940809852991757559201815)
              ·
                refine ⟨4411214779487636338802723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940809852991757559201815 4411214779487636338802723)
                ·
                  refine ⟨6616822169231454508204085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411214779487636338802723 6616822169231454508204085)
                  ·
                    refine ⟨620327078365448860144133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6616822169231454508204085 620327078365448860144133)
                    ·
                      rfl

theorem cell22_1812124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1812124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812124 prefixEnd_1812124 := by exact prefixLift 1812124
  have htrace : WordTrace (prefixWord ++ tailWord_1812124) baseStart_1812124 baseEnd_1812124 := by
    simpa [prefixWord, tailWord_1812124, baseEnd_1812124] using wordTrace_append hprefix tailTrace_1812124
  have hstable : (prefixWord ++ tailWord_1812124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812124).length < 2 ^ (prefixWord ++ tailWord_1812124).sum := by decide
  have hdescent : baseEnd_1812124 < baseStart_1812124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812165 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 7]
def baseStart_1812165 : Nat := 118140960795 + 1812165 * 2 ^ 59
def prefixEnd_1812165 : Nat := 4983230072969 + 3 ^ 40 * 1812165 * 2
def baseEnd_1812165 : Nat := 206780371167779473289669

theorem tailTrace_1812165 : CollatzResearch.WordTrace tailWord_1812165 prefixEnd_1812165 206780371167779473289669 := by
  unfold tailWord_1812165
  simp only [CollatzResearch.WordTrace]
  refine ⟨66095087479843172987101949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44063391653228781991401299 66095087479843172987101949)
  ·
    refine ⟨24785657804941189870163231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66095087479843172987101949 24785657804941189870163231)
    ·
      refine ⟨37178486707411784805244847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24785657804941189870163231 37178486707411784805244847)
      ·
        refine ⟨55767730061117677207867271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37178486707411784805244847 55767730061117677207867271)
        ·
          refine ⟨83651595091676515811800907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55767730061117677207867271 83651595091676515811800907)
          ·
            refine ⟨125477392637514773717701361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83651595091676515811800907 125477392637514773717701361)
            ·
              refine ⟨94108044478136080288276021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125477392637514773717701361 94108044478136080288276021)
              ·
                refine ⟨8822629169825257527025877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94108044478136080288276021 8822629169825257527025877)
                ·
                  refine ⟨206780371167779473289669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8822629169825257527025877 206780371167779473289669)
                  ·
                    rfl

theorem cell22_1812165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_1812165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812165 prefixEnd_1812165 := by exact prefixLift 1812165
  have htrace : WordTrace (prefixWord ++ tailWord_1812165) baseStart_1812165 baseEnd_1812165 := by
    simpa [prefixWord, tailWord_1812165, baseEnd_1812165] using wordTrace_append hprefix tailTrace_1812165
  have hstable : (prefixWord ++ tailWord_1812165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812165).length < 2 ^ (prefixWord ++ tailWord_1812165).sum := by decide
  have hdescent : baseEnd_1812165 < baseStart_1812165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812188 : List Nat := [2, 2, 5, 1, 3, 1, 2, 6]
def baseStart_1812188 : Nat := 118140960795 + 1812188 * 2 ^ 59
def prefixEnd_1812188 : Nat := 4983230072969 + 3 ^ 40 * 1812188 * 2
def baseEnd_1812188 : Nat := 68927665208152669615993

theorem tailTrace_1812188 : CollatzResearch.WordTrace tailWord_1812188 prefixEnd_1812188 68927665208152669615993 := by
  unfold tailWord_1812188
  simp only [CollatzResearch.WordTrace]
  refine ⟨33047963179379923957594609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44063950905839898610126145 33047963179379923957594609)
  ·
    refine ⟨24785972384534942968195957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33047963179379923957594609 24785972384534942968195957)
    ·
      refine ⟨2323684911050150903268371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24785972384534942968195957 2323684911050150903268371)
      ·
        refine ⟨3485527366575226354902557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323684911050150903268371 3485527366575226354902557)
        ·
          refine ⟨1307072762465709883088459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3485527366575226354902557 1307072762465709883088459)
          ·
            refine ⟨1960609143698564824632689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307072762465709883088459 1960609143698564824632689)
            ·
              refine ⟨1470456857773923618474517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960609143698564824632689 1470456857773923618474517)
              ·
                refine ⟨68927665208152669615993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1470456857773923618474517 68927665208152669615993)
                ·
                  rfl

theorem cell22_1812188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 6].length) (baseStart_1812188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812188 prefixEnd_1812188 := by exact prefixLift 1812188
  have htrace : WordTrace (prefixWord ++ tailWord_1812188) baseStart_1812188 baseEnd_1812188 := by
    simpa [prefixWord, tailWord_1812188, baseEnd_1812188] using wordTrace_append hprefix tailTrace_1812188
  have hstable : (prefixWord ++ tailWord_1812188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812188).length < 2 ^ (prefixWord ++ tailWord_1812188).sum := by decide
  have hdescent : baseEnd_1812188 < baseStart_1812188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812227 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 6]
def baseStart_1812227 : Nat := 118140960795 + 1812227 * 2 ^ 59
def prefixEnd_1812227 : Nat := 4983230072969 + 3 ^ 40 * 1812227 * 2
def baseEnd_1812227 : Nat := 206787445790130308272939

theorem tailTrace_1812227 : CollatzResearch.WordTrace tailWord_1812227 prefixEnd_1812227 206787445790130308272939 := by
  unfold tailWord_1812227
  simp only [CollatzResearch.WordTrace]
  refine ⟨66097348805618557575858935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44064899203745705050572623 66097348805618557575858935)
  ·
    refine ⟨99146023208427836363788403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66097348805618557575858935 99146023208427836363788403)
    ·
      refine ⟨148719034812641754545682605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99146023208427836363788403 148719034812641754545682605)
      ·
        refine ⟨55769638054740657954630977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148719034812641754545682605 55769638054740657954630977)
        ·
          refine ⟨41827228541055493465973233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55769638054740657954630977 41827228541055493465973233)
          ·
            refine ⟨31370421405791620099479925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41827228541055493465973233 31370421405791620099479925)
            ·
              refine ⟨2940977006792964384326243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31370421405791620099479925 2940977006792964384326243)
              ·
                refine ⟨4411465510189446576489365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940977006792964384326243 4411465510189446576489365)
                ·
                  refine ⟨206787445790130308272939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4411465510189446576489365 206787445790130308272939)
                  ·
                    rfl

theorem cell22_1812227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 6].length) (baseStart_1812227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812227 prefixEnd_1812227 := by exact prefixLift 1812227
  have htrace : WordTrace (prefixWord ++ tailWord_1812227) baseStart_1812227 baseEnd_1812227 := by
    simpa [prefixWord, tailWord_1812227, baseEnd_1812227] using wordTrace_append hprefix tailTrace_1812227
  have hstable : (prefixWord ++ tailWord_1812227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812227).length < 2 ^ (prefixWord ++ tailWord_1812227).sum := by decide
  have hdescent : baseEnd_1812227 < baseStart_1812227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812274 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1812274 : Nat := 118140960795 + 1812274 * 2 ^ 59
def prefixEnd_1812274 : Nat := 4983230072969 + 3 ^ 40 * 1812274 * 2
def baseEnd_1812274 : Nat := 620378426430898468893673

theorem tailTrace_1812274 : CollatzResearch.WordTrace tailWord_1812274 prefixEnd_1812274 620378426430898468893673 := by
  unfold tailWord_1812274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524765759112071150704969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44066042024298856401879917 16524765759112071150704969)
  ·
    refine ⟨12393574319334053363028727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16524765759112071150704969 12393574319334053363028727)
    ·
      refine ⟨18590361479001080044543091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393574319334053363028727 18590361479001080044543091)
      ·
        refine ⟨27885542218501620066814637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18590361479001080044543091 27885542218501620066814637)
        ·
          refine ⟨10457078331938107525055489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27885542218501620066814637 10457078331938107525055489)
          ·
            refine ⟨7842808748953580643791617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10457078331938107525055489 7842808748953580643791617)
            ·
              refine ⟨5882106561715185482843713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7842808748953580643791617 5882106561715185482843713)
              ·
                refine ⟨4411579921286389112132785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5882106561715185482843713 4411579921286389112132785)
                ·
                  refine ⟨3308684940964791834099589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411579921286389112132785 3308684940964791834099589)
                  ·
                    refine ⟨620378426430898468893673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308684940964791834099589 620378426430898468893673)
                    ·
                      rfl

theorem cell22_1812274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1812274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812274 prefixEnd_1812274 := by exact prefixLift 1812274
  have htrace : WordTrace (prefixWord ++ tailWord_1812274) baseStart_1812274 baseEnd_1812274 := by
    simpa [prefixWord, tailWord_1812274, baseEnd_1812274] using wordTrace_append hprefix tailTrace_1812274
  have hstable : (prefixWord ++ tailWord_1812274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812274).length < 2 ^ (prefixWord ++ tailWord_1812274).sum := by decide
  have hdescent : baseEnd_1812274 < baseStart_1812274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812278 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1812278 : Nat := 118140960795 + 1812278 * 2 ^ 59
def prefixEnd_1812278 : Nat := 4983230072969 + 3 ^ 40 * 1812278 * 2
def baseEnd_1812278 : Nat := 206793265237547930597887

theorem tailTrace_1812278 : CollatzResearch.WordTrace tailWord_1812278 prefixEnd_1812278 206793265237547930597887 := by
  unfold tailWord_1812278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4131200558027112080372843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44066139285622528857310325 4131200558027112080372843)
  ·
    refine ⟨6196800837040668120559265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4131200558027112080372843 6196800837040668120559265)
    ·
      refine ⟨4647600627780501090419449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6196800837040668120559265 4647600627780501090419449)
      ·
        refine ⟨3485700470835375817814587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4647600627780501090419449 3485700470835375817814587)
        ·
          refine ⟨5228550706253063726721881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3485700470835375817814587 5228550706253063726721881)
          ·
            refine ⟨3921413029689797795041411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5228550706253063726721881 3921413029689797795041411)
            ·
              refine ⟨5882119544534696692562117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921413029689797795041411 5882119544534696692562117)
              ·
                refine ⟨1102897414600255629855397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5882119544534696692562117 1102897414600255629855397)
                ·
                  refine ⟨206793265237547930597887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1102897414600255629855397 206793265237547930597887)
                  ·
                    rfl

theorem cell22_1812278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1812278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812278 prefixEnd_1812278 := by exact prefixLift 1812278
  have htrace : WordTrace (prefixWord ++ tailWord_1812278) baseStart_1812278 baseEnd_1812278 := by
    simpa [prefixWord, tailWord_1812278, baseEnd_1812278] using wordTrace_append hprefix tailTrace_1812278
  have hstable : (prefixWord ++ tailWord_1812278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812278).length < 2 ^ (prefixWord ++ tailWord_1812278).sum := by decide
  have hdescent : baseEnd_1812278 < baseStart_1812278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812381 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1812381 : Nat := 118140960795 + 1812381 * 2 ^ 59
def prefixEnd_1812381 : Nat := 4983230072969 + 3 ^ 40 * 1812381 * 2
def baseEnd_1812381 : Nat := 620415054717585856468345

theorem tailTrace_1812381 : CollatzResearch.WordTrace tailWord_1812381 prefixEnd_1812381 620415054717585856468345 := by
  unfold tailWord_1812381
  simp only [CollatzResearch.WordTrace]
  refine ⟨66102965647060641876964997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44068643764707094584643331 66102965647060641876964997)
  ·
    refine ⟨12394306058823870351930937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66102965647060641876964997 12394306058823870351930937)
    ·
      refine ⟨9295729544117902763948203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12394306058823870351930937 9295729544117902763948203)
      ·
        refine ⟨13943594316176854145922305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9295729544117902763948203 13943594316176854145922305)
        ·
          refine ⟨10457695737132640609441729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13943594316176854145922305 10457695737132640609441729)
          ·
            refine ⟨7843271802849480457081297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10457695737132640609441729 7843271802849480457081297)
            ·
              refine ⟨5882453852137110342810973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7843271802849480457081297 5882453852137110342810973)
              ·
                refine ⟨2205920194551416378554115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5882453852137110342810973 2205920194551416378554115)
                ·
                  refine ⟨3308880291827124567831173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205920194551416378554115 3308880291827124567831173)
                  ·
                    refine ⟨620415054717585856468345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308880291827124567831173 620415054717585856468345)
                    ·
                      rfl

theorem cell22_1812381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1812381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812381 prefixEnd_1812381 := by exact prefixLift 1812381
  have htrace : WordTrace (prefixWord ++ tailWord_1812381) baseStart_1812381 baseEnd_1812381 := by
    simpa [prefixWord, tailWord_1812381, baseEnd_1812381] using wordTrace_append hprefix tailTrace_1812381
  have hstable : (prefixWord ++ tailWord_1812381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812381).length < 2 ^ (prefixWord ++ tailWord_1812381).sum := by decide
  have hdescent : baseEnd_1812381 < baseStart_1812381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812409 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_1812409 : Nat := 118140960795 + 1812409 * 2 ^ 59
def prefixEnd_1812409 : Nat := 4983230072969 + 3 ^ 40 * 1812409 * 2
def baseEnd_1812409 : Nat := 620424639689803116768259

theorem tailTrace_1812409 : CollatzResearch.WordTrace tailWord_1812409 prefixEnd_1812409 620424639689803116768259 := by
  unfold tailWord_1812409
  simp only [CollatzResearch.WordTrace]
  refine ⟨66103986890959202658984281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44069324593972801772656187 66103986890959202658984281)
  ·
    refine ⟨49577990168219401994238211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66103986890959202658984281 49577990168219401994238211)
    ·
      refine ⟨74366985252329102991357317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49577990168219401994238211 74366985252329102991357317)
      ·
        refine ⟨13943809734811706810879497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74366985252329102991357317 13943809734811706810879497)
        ·
          refine ⟨10457857301108780108159623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13943809734811706810879497 10457857301108780108159623)
          ·
            refine ⟨15686785951663170162239435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10457857301108780108159623 15686785951663170162239435)
            ·
              refine ⟨23530178927494755243359153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686785951663170162239435 23530178927494755243359153)
              ·
                refine ⟨17647634195621066432519365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23530178927494755243359153 17647634195621066432519365)
                ·
                  refine ⟨3308931411678949956097381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17647634195621066432519365 3308931411678949956097381)
                  ·
                    refine ⟨620424639689803116768259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308931411678949956097381 620424639689803116768259)
                    ·
                      rfl

theorem cell22_1812409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_1812409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812409 prefixEnd_1812409 := by exact prefixLift 1812409
  have htrace : WordTrace (prefixWord ++ tailWord_1812409) baseStart_1812409 baseEnd_1812409 := by
    simpa [prefixWord, tailWord_1812409, baseEnd_1812409] using wordTrace_append hprefix tailTrace_1812409
  have hstable : (prefixWord ++ tailWord_1812409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812409).length < 2 ^ (prefixWord ++ tailWord_1812409).sum := by decide
  have hdescent : baseEnd_1812409 < baseStart_1812409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812424 : List Nat := [2, 1, 3, 1, 4, 1, 2, 8]
def baseStart_1812424 : Nat := 118140960795 + 1812424 * 2 ^ 59
def prefixEnd_1812424 : Nat := 4983230072969 + 3 ^ 40 * 1812424 * 2
def baseEnd_1812424 : Nat := 68936641610705341960357

theorem tailTrace_1812424 : CollatzResearch.WordTrace tailWord_1812424 prefixEnd_1812424 68936641610705341960357 := by
  unfold tailWord_1812424
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052266992952430110390163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44069689323936573480520217 33052266992952430110390163)
  ·
    refine ⟨49578400489428645165585245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33052266992952430110390163 49578400489428645165585245)
    ·
      refine ⟨18591900183535741937094467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49578400489428645165585245 18591900183535741937094467)
      ·
        refine ⟨27887850275303612905641701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18591900183535741937094467 27887850275303612905641701)
        ·
          refine ⟨5228971926619427419807819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27887850275303612905641701 5228971926619427419807819)
          ·
            refine ⟨7843457889929141129711729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228971926619427419807819 7843457889929141129711729)
            ·
              refine ⟨5882593417446855847283797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7843457889929141129711729 5882593417446855847283797)
              ·
                refine ⟨68936641610705341960357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5882593417446855847283797 68936641610705341960357)
                ·
                  rfl

theorem cell22_1812424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_1812424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812424 prefixEnd_1812424 := by exact prefixLift 1812424
  have htrace : WordTrace (prefixWord ++ tailWord_1812424) baseStart_1812424 baseEnd_1812424 := by
    simpa [prefixWord, tailWord_1812424, baseEnd_1812424] using wordTrace_append hprefix tailTrace_1812424
  have hstable : (prefixWord ++ tailWord_1812424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812424).length < 2 ^ (prefixWord ++ tailWord_1812424).sum := by decide
  have hdescent : baseEnd_1812424 < baseStart_1812424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812445 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1812445 : Nat := 118140960795 + 1812445 * 2 ^ 59
def prefixEnd_1812445 : Nat := 4983230072969 + 3 ^ 40 * 1812445 * 2
def baseEnd_1812445 : Nat := 620436963225511022868149

theorem tailTrace_1812445 : CollatzResearch.WordTrace tailWord_1812445 prefixEnd_1812445 620436963225511022868149 := by
  unfold tailWord_1812445
  simp only [CollatzResearch.WordTrace]
  refine ⟨66105299918828780807294789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44070199945885853871529859 66105299918828780807294789)
  ·
    refine ⟨12394743734780396401367773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66105299918828780807294789 12394743734780396401367773)
    ·
      refine ⟨4648028900542648650512915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12394743734780396401367773 4648028900542648650512915)
      ·
        refine ⟨6972043350813972975769373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648028900542648650512915 6972043350813972975769373)
        ·
          refine ⟨2614516256555239865913515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6972043350813972975769373 2614516256555239865913515)
          ·
            refine ⟨3921774384832859798870273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614516256555239865913515 3921774384832859798870273)
            ·
              refine ⟨2941330788624644849152705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921774384832859798870273 2941330788624644849152705)
              ·
                refine ⟨2205998091468483636864529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941330788624644849152705 2205998091468483636864529)
                ·
                  refine ⟨1654498568601362727648397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2205998091468483636864529 1654498568601362727648397)
                  ·
                    refine ⟨620436963225511022868149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654498568601362727648397 620436963225511022868149)
                    ·
                      rfl

theorem cell22_1812445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1812445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812445 prefixEnd_1812445 := by exact prefixLift 1812445
  have htrace : WordTrace (prefixWord ++ tailWord_1812445) baseStart_1812445 baseEnd_1812445 := by
    simpa [prefixWord, tailWord_1812445, baseEnd_1812445] using wordTrace_append hprefix tailTrace_1812445
  have hstable : (prefixWord ++ tailWord_1812445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812445).length < 2 ^ (prefixWord ++ tailWord_1812445).sum := by decide
  have hdescent : baseEnd_1812445 < baseStart_1812445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812456 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_1812456 : Nat := 118140960795 + 1812456 * 2 ^ 59
def prefixEnd_1812456 : Nat := 4983230072969 + 3 ^ 40 * 1812456 * 2
def baseEnd_1812456 : Nat := 620440728750310660843115

theorem tailTrace_1812456 : CollatzResearch.WordTrace tailWord_1812456 prefixEnd_1812456 620440728750310660843115 := by
  unfold tailWord_1812456
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052850560894464842972611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44070467414525953123963481 33052850560894464842972611)
  ·
    refine ⟨49579275841341697264458917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33052850560894464842972611 49579275841341697264458917)
    ·
      refine ⟨9296114220251568237086047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49579275841341697264458917 9296114220251568237086047)
      ·
        refine ⟨13944171330377352355629071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296114220251568237086047 13944171330377352355629071)
        ·
          refine ⟨20916256995566028533443607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13944171330377352355629071 20916256995566028533443607)
          ·
            refine ⟨31374385493349042800165411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20916256995566028533443607 31374385493349042800165411)
            ·
              refine ⟨47061578240023564200248117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31374385493349042800165411 47061578240023564200248117)
              ·
                refine ⟨4412022960002209143773261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47061578240023564200248117 4412022960002209143773261)
                ·
                  refine ⟨1654508610000828428914973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4412022960002209143773261 1654508610000828428914973)
                  ·
                    refine ⟨620440728750310660843115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654508610000828428914973 620440728750310660843115)
                    ·
                      rfl

theorem cell22_1812456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_1812456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812456 prefixEnd_1812456 := by exact prefixLift 1812456
  have htrace : WordTrace (prefixWord ++ tailWord_1812456) baseStart_1812456 baseEnd_1812456 := by
    simpa [prefixWord, tailWord_1812456, baseEnd_1812456] using wordTrace_append hprefix tailTrace_1812456
  have hstable : (prefixWord ++ tailWord_1812456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812456).length < 2 ^ (prefixWord ++ tailWord_1812456).sum := by decide
  have hdescent : baseEnd_1812456 < baseStart_1812456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812550 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1812550 : Nat := 118140960795 + 1812550 * 2 ^ 59
def prefixEnd_1812550 : Nat := 4983230072969 + 3 ^ 40 * 1812550 * 2
def baseEnd_1812550 : Nat := 620472906871325748992827

theorem tailTrace_1812550 : CollatzResearch.WordTrace tailWord_1812550 prefixEnd_1812550 620472906871325748992827 := by
  unfold tailWord_1812550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065910299482761991870847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44072753055632255826578069 2065910299482761991870847)
  ·
    refine ⟨3098865449224142987806271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2065910299482761991870847 3098865449224142987806271)
    ·
      refine ⟨4648298173836214481709407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098865449224142987806271 4648298173836214481709407)
      ·
        refine ⟨6972447260754321722564111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648298173836214481709407 6972447260754321722564111)
        ·
          refine ⟨10458670891131482583846167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972447260754321722564111 10458670891131482583846167)
          ·
            refine ⟨15688006336697223875769251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458670891131482583846167 15688006336697223875769251)
            ·
              refine ⟨23532009505045835813653877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688006336697223875769251 23532009505045835813653877)
              ·
                refine ⟨2206125891098047107530051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23532009505045835813653877 2206125891098047107530051)
                ·
                  refine ⟨3309188836647070661295077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206125891098047107530051 3309188836647070661295077)
                  ·
                    refine ⟨620472906871325748992827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309188836647070661295077 620472906871325748992827)
                    ·
                      rfl

theorem cell22_1812550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1812550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812550 prefixEnd_1812550 := by exact prefixLift 1812550
  have htrace : WordTrace (prefixWord ++ tailWord_1812550) baseStart_1812550 baseEnd_1812550 := by
    simpa [prefixWord, tailWord_1812550, baseEnd_1812550] using wordTrace_append hprefix tailTrace_1812550
  have hstable : (prefixWord ++ tailWord_1812550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812550).length < 2 ^ (prefixWord ++ tailWord_1812550).sum := by decide
  have hdescent : baseEnd_1812550 < baseStart_1812550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812565 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 4]
def baseStart_1812565 : Nat := 118140960795 + 1812565 * 2 ^ 59
def prefixEnd_1812565 : Nat := 4983230072969 + 3 ^ 40 * 1812565 * 2
def baseEnd_1812565 : Nat := 206826013892623569955927

theorem tailTrace_1812565 : CollatzResearch.WordTrace tailWord_1812565 prefixEnd_1812565 206826013892623569955927 := by
  unfold tailWord_1812565
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109676678394041301663149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44073117785596027534442099 66109676678394041301663149)
  ·
    refine ⟨24791128754397765488123681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66109676678394041301663149 24791128754397765488123681)
    ·
      refine ⟨18593346565798324116092761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24791128754397765488123681 18593346565798324116092761)
      ·
        refine ⟨13945009924348743087069571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18593346565798324116092761 13945009924348743087069571)
        ·
          refine ⟨20917514886523114630604357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13945009924348743087069571 20917514886523114630604357)
          ·
            refine ⟨3922034041223083993238317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20917514886523114630604357 3922034041223083993238317)
            ·
              refine ⟨1470762765458656497464369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3922034041223083993238317 1470762765458656497464369)
              ·
                refine ⟨1103072074093992373098277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470762765458656497464369 1103072074093992373098277)
                ·
                  refine ⟨206826013892623569955927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103072074093992373098277 206826013892623569955927)
                  ·
                    rfl

theorem cell22_1812565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_1812565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812565 prefixEnd_1812565 := by exact prefixLift 1812565
  have htrace : WordTrace (prefixWord ++ tailWord_1812565) baseStart_1812565 baseEnd_1812565 := by
    simpa [prefixWord, tailWord_1812565, baseEnd_1812565] using wordTrace_append hprefix tailTrace_1812565
  have hstable : (prefixWord ++ tailWord_1812565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812565).length < 2 ^ (prefixWord ++ tailWord_1812565).sum := by decide
  have hdescent : baseEnd_1812565 < baseStart_1812565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812576 : List Nat := [2, 1, 1, 3, 2, 4, 2, 7]
def baseStart_1812576 : Nat := 118140960795 + 1812576 * 2 ^ 59
def prefixEnd_1812576 : Nat := 4983230072969 + 3 ^ 40 * 1812576 * 2
def baseEnd_1812576 : Nat := 68942423022518927538083

theorem tailTrace_1812576 : CollatzResearch.WordTrace tailWord_1812576 prefixEnd_1812576 68942423022518927538083 := by
  unfold tailWord_1812576
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055038940677095090156791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44073385254236126786875721 33055038940677095090156791)
  ·
    refine ⟨49582558411015642635235187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33055038940677095090156791 49582558411015642635235187)
    ·
      refine ⟨74373837616523463952852781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49582558411015642635235187 74373837616523463952852781)
      ·
        refine ⟨27890189106196298982319793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74373837616523463952852781 27890189106196298982319793)
        ·
          refine ⟨20917641829647224236739845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27890189106196298982319793 20917641829647224236739845)
          ·
            refine ⟨3922057843058854544388721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20917641829647224236739845 3922057843058854544388721)
            ·
              refine ⟨2941543382294140908291541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922057843058854544388721 2941543382294140908291541)
              ·
                refine ⟨68942423022518927538083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2941543382294140908291541 68942423022518927538083)
                ·
                  rfl

theorem cell22_1812576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_1812576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812576 prefixEnd_1812576 := by exact prefixLift 1812576
  have htrace : WordTrace (prefixWord ++ tailWord_1812576) baseStart_1812576 baseEnd_1812576 := by
    simpa [prefixWord, tailWord_1812576, baseEnd_1812576] using wordTrace_append hprefix tailTrace_1812576
  have hstable : (prefixWord ++ tailWord_1812576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812576).length < 2 ^ (prefixWord ++ tailWord_1812576).sum := by decide
  have hdescent : baseEnd_1812576 < baseStart_1812576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812580 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_1812580 : Nat := 118140960795 + 1812580 * 2 ^ 59
def prefixEnd_1812580 : Nat := 4983230072969 + 3 ^ 40 * 1812580 * 2
def baseEnd_1812580 : Nat := 620483176484415670742735

theorem tailTrace_1812580 : CollatzResearch.WordTrace tailWord_1812580 prefixEnd_1812580 620483176484415670742735 := by
  unfold tailWord_1812580
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055111886669849431729597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44073482515559799242306129 33055111886669849431729597)
  ·
    refine ⟨12395666957501193536898599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33055111886669849431729597 12395666957501193536898599)
    ·
      refine ⟨18593500436251790305347899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12395666957501193536898599 18593500436251790305347899)
      ·
        refine ⟨27890250654377685458021849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18593500436251790305347899 27890250654377685458021849)
        ·
          refine ⟨20917687990783264093516387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27890250654377685458021849 20917687990783264093516387)
          ·
            refine ⟨31376531986174896140274581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20917687990783264093516387 31376531986174896140274581)
            ·
              refine ⟨1470774936851948256575371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31376531986174896140274581 1470774936851948256575371)
              ·
                refine ⟨2206162405277922384863057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470774936851948256575371 2206162405277922384863057)
                ·
                  refine ⟨1654621803958441788647293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206162405277922384863057 1654621803958441788647293)
                  ·
                    refine ⟨620483176484415670742735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654621803958441788647293 620483176484415670742735)
                    ·
                      rfl

theorem cell22_1812580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_1812580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812580 prefixEnd_1812580 := by exact prefixLift 1812580
  have htrace : WordTrace (prefixWord ++ tailWord_1812580) baseStart_1812580 baseEnd_1812580 := by
    simpa [prefixWord, tailWord_1812580, baseEnd_1812580] using wordTrace_append hprefix tailTrace_1812580
  have hstable : (prefixWord ++ tailWord_1812580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812580).length < 2 ^ (prefixWord ++ tailWord_1812580).sum := by decide
  have hdescent : baseEnd_1812580 < baseStart_1812580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812683 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 4]
def baseStart_1812683 : Nat := 118140960795 + 1812683 * 2 ^ 59
def prefixEnd_1812683 : Nat := 4983230072969 + 3 ^ 40 * 1812683 * 2
def baseEnd_1812683 : Nat := 206839478496452578472473

theorem tailTrace_1812683 : CollatzResearch.WordTrace tailWord_1812683 prefixEnd_1812683 206839478496452578472473 := by
  unfold tailWord_1812683
  simp only [CollatzResearch.WordTrace]
  refine ⟨66113980491966547454458703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44075986994644364969639135 66113980491966547454458703)
  ·
    refine ⟨99170970737949821181688055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66113980491966547454458703 99170970737949821181688055)
    ·
      refine ⟨148756456106924731772532083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99170970737949821181688055 148756456106924731772532083)
      ·
        refine ⟨223134684160387097658798125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148756456106924731772532083 223134684160387097658798125)
        ·
          refine ⟨83675506560145161622049297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223134684160387097658798125 83675506560145161622049297)
          ·
            refine ⟨62756629920108871216536973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83675506560145161622049297 62756629920108871216536973)
            ·
              refine ⟨23533736220040826706201365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62756629920108871216536973 23533736220040826706201365)
              ·
                refine ⟨1103143885314413751853189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23533736220040826706201365 1103143885314413751853189)
                ·
                  refine ⟨206839478496452578472473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103143885314413751853189 206839478496452578472473)
                  ·
                    rfl

theorem cell22_1812683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 4].length) (baseStart_1812683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812683 prefixEnd_1812683 := by exact prefixLift 1812683
  have htrace : WordTrace (prefixWord ++ tailWord_1812683) baseStart_1812683 baseEnd_1812683 := by
    simpa [prefixWord, tailWord_1812683, baseEnd_1812683] using wordTrace_append hprefix tailTrace_1812683
  have hstable : (prefixWord ++ tailWord_1812683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812683).length < 2 ^ (prefixWord ++ tailWord_1812683).sum := by decide
  have hdescent : baseEnd_1812683 < baseStart_1812683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812698 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_1812698 : Nat := 118140960795 + 1812698 * 2 ^ 59
def prefixEnd_1812698 : Nat := 4983230072969 + 3 ^ 40 * 1812698 * 2
def baseEnd_1812698 : Nat := 620523570295902696292373

theorem tailTrace_1812698 : CollatzResearch.WordTrace tailWord_1812698 prefixEnd_1812698 620523570295902696292373 := by
  unfold tailWord_1812698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16528631896728051254063687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44076351724608136677503165 16528631896728051254063687)
  ·
    refine ⟨24792947845092076881095531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16528631896728051254063687 24792947845092076881095531)
    ·
      refine ⟨37189421767638115321643297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24792947845092076881095531 37189421767638115321643297)
      ·
        refine ⟨27892066325728586491232473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37189421767638115321643297 27892066325728586491232473)
        ·
          refine ⟨20919049744296439868424355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27892066325728586491232473 20919049744296439868424355)
          ·
            refine ⟨31378574616444659802636533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20919049744296439868424355 31378574616444659802636533)
            ·
              refine ⟨2941741370291686856497175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31378574616444659802636533 2941741370291686856497175)
              ·
                refine ⟨4412612055437530284745763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941741370291686856497175 4412612055437530284745763)
                ·
                  refine ⟨6618918083156295427118645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412612055437530284745763 6618918083156295427118645)
                  ·
                    refine ⟨620523570295902696292373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6618918083156295427118645 620523570295902696292373)
                    ·
                      rfl

theorem cell22_1812698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_1812698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812698 prefixEnd_1812698 := by exact prefixLift 1812698
  have htrace : WordTrace (prefixWord ++ tailWord_1812698) baseStart_1812698 baseEnd_1812698 := by
    simpa [prefixWord, tailWord_1812698, baseEnd_1812698] using wordTrace_append hprefix tailTrace_1812698
  have hstable : (prefixWord ++ tailWord_1812698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812698).length < 2 ^ (prefixWord ++ tailWord_1812698).sum := by decide
  have hdescent : baseEnd_1812698 < baseStart_1812698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812794 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_1812794 : Nat := 118140960795 + 1812794 * 2 ^ 59
def prefixEnd_1812794 : Nat := 4983230072969 + 3 ^ 40 * 1812794 * 2
def baseEnd_1812794 : Nat := 620556433057790445892079

theorem tailTrace_1812794 : CollatzResearch.WordTrace tailWord_1812794 prefixEnd_1812794 620556433057790445892079 := by
  unfold tailWord_1812794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16529507248641103352937359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44078685996376275607832957 16529507248641103352937359)
  ·
    refine ⟨24794260872961655029406039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16529507248641103352937359 24794260872961655029406039)
    ·
      refine ⟨37191391309442482544109059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24794260872961655029406039 37191391309442482544109059)
      ·
        refine ⟨55787086964163723816163589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37191391309442482544109059 55787086964163723816163589)
        ·
          refine ⟨10460078805780698215530673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55787086964163723816163589 10460078805780698215530673)
          ·
            refine ⟨7845059104335523661648005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10460078805780698215530673 7845059104335523661648005)
            ·
              refine ⟨1470948582062910686559001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7845059104335523661648005 1470948582062910686559001)
              ·
                refine ⟨1103211436547183014919251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470948582062910686559001 1103211436547183014919251)
                ·
                  refine ⟨1654817154820774522378877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103211436547183014919251 1654817154820774522378877)
                  ·
                    refine ⟨620556433057790445892079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654817154820774522378877 620556433057790445892079)
                    ·
                      rfl

theorem cell22_1812794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_1812794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812794 prefixEnd_1812794 := by exact prefixLift 1812794
  have htrace : WordTrace (prefixWord ++ tailWord_1812794) baseStart_1812794 baseEnd_1812794 := by
    simpa [prefixWord, tailWord_1812794, baseEnd_1812794] using wordTrace_append hprefix tailTrace_1812794
  have hstable : (prefixWord ++ tailWord_1812794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812794).length < 2 ^ (prefixWord ++ tailWord_1812794).sum := by decide
  have hdescent : baseEnd_1812794 < baseStart_1812794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812803 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 3, 4]
def baseStart_1812803 : Nat := 118140960795 + 1812803 * 2 ^ 59
def prefixEnd_1812803 : Nat := 4983230072969 + 3 ^ 40 * 1812803 * 2
def baseEnd_1812803 : Nat := 620559513941717422417051

theorem tailTrace_1812803 : CollatzResearch.WordTrace tailWord_1812803 prefixEnd_1812803 620559513941717422417051 := by
  unfold tailWord_1812803
  simp only [CollatzResearch.WordTrace]
  refine ⟨66118357251531807948827063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44078904834354538632551375 66118357251531807948827063)
  ·
    refine ⟨99177535877297711923240595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66118357251531807948827063 99177535877297711923240595)
    ·
      refine ⟨148766303815946567884860893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99177535877297711923240595 148766303815946567884860893)
      ·
        refine ⟨55787363930979962956822835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148766303815946567884860893 55787363930979962956822835)
        ·
          refine ⟨83681045896469944435234253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55787363930979962956822835 83681045896469944435234253)
          ·
            refine ⟨31380392211176229163212845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83681045896469944435234253 31380392211176229163212845)
            ·
              refine ⟨11767647079191085936204817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31380392211176229163212845 11767647079191085936204817)
              ·
                refine ⟨8825735309393314452153613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11767647079191085936204817 8825735309393314452153613)
                ·
                  refine ⟨3309650741022492919557605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8825735309393314452153613 3309650741022492919557605)
                  ·
                    refine ⟨620559513941717422417051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309650741022492919557605 620559513941717422417051)
                    ·
                      rfl

theorem cell22_1812803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_1812803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812803 prefixEnd_1812803 := by exact prefixLift 1812803
  have htrace : WordTrace (prefixWord ++ tailWord_1812803) baseStart_1812803 baseEnd_1812803 := by
    simpa [prefixWord, tailWord_1812803, baseEnd_1812803] using wordTrace_append hprefix tailTrace_1812803
  have hstable : (prefixWord ++ tailWord_1812803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812803).length < 2 ^ (prefixWord ++ tailWord_1812803).sum := by decide
  have hdescent : baseEnd_1812803 < baseStart_1812803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812818 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1812818 : Nat := 118140960795 + 1812818 * 2 ^ 59
def prefixEnd_1812818 : Nat := 4983230072969 + 3 ^ 40 * 1812818 * 2
def baseEnd_1812818 : Nat := 206854882916087461097335

theorem tailTrace_1812818 : CollatzResearch.WordTrace tailWord_1812818 prefixEnd_1812818 206854882916087461097335 := by
  unfold tailWord_1812818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16529726086619366377655777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44079269564318310340415405 16529726086619366377655777)
  ·
    refine ⟨12397294564964524783241833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16529726086619366377655777 12397294564964524783241833)
    ·
      refine ⟨9297970923723393587431375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12397294564964524783241833 9297970923723393587431375)
      ·
        refine ⟨13946956385585090381147063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9297970923723393587431375 13946956385585090381147063)
        ·
          refine ⟨20920434578377635571720595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13946956385585090381147063 20920434578377635571720595)
          ·
            refine ⟨31380651867566453357580893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20920434578377635571720595 31380651867566453357580893)
            ·
              refine ⟨11767744450337420009092835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31380651867566453357580893 11767744450337420009092835)
              ·
                refine ⟨17651616675506130013639253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11767744450337420009092835 17651616675506130013639253)
                ·
                  refine ⟨206854882916087461097335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17651616675506130013639253 206854882916087461097335)
                  ·
                    rfl

theorem cell22_1812818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1812818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812818 prefixEnd_1812818 := by exact prefixLift 1812818
  have htrace : WordTrace (prefixWord ++ tailWord_1812818) baseStart_1812818 baseEnd_1812818 := by
    simpa [prefixWord, tailWord_1812818, baseEnd_1812818] using wordTrace_append hprefix tailTrace_1812818
  have hstable : (prefixWord ++ tailWord_1812818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812818).length < 2 ^ (prefixWord ++ tailWord_1812818).sum := by decide
  have hdescent : baseEnd_1812818 < baseStart_1812818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812820 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1812820 : Nat := 118140960795 + 1812820 * 2 ^ 59
def prefixEnd_1812820 : Nat := 4983230072969 + 3 ^ 40 * 1812820 * 2
def baseEnd_1812820 : Nat := 620565333389135044741999

theorem tailTrace_1812820 : CollatzResearch.WordTrace tailWord_1812820 prefixEnd_1812820 620565333389135044741999 := by
  unfold tailWord_1812820
  simp only [CollatzResearch.WordTrace]
  refine ⟨33059488646235109926097957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44079318194980146568130609 33059488646235109926097957)
  ·
    refine ⟨6198654121169083111143367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33059488646235109926097957 6198654121169083111143367)
    ·
      refine ⟨9297981181753624666715051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6198654121169083111143367 9297981181753624666715051)
      ·
        refine ⟨13946971772630437000072577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9297981181753624666715051 13946971772630437000072577)
        ·
          refine ⟨10460228829472827750054433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13946971772630437000072577 10460228829472827750054433)
          ·
            refine ⟨7845171622104620812540825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10460228829472827750054433 7845171622104620812540825)
            ·
              refine ⟨5883878716578465609405619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7845171622104620812540825 5883878716578465609405619)
              ·
                refine ⟨8825818074867698414108429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883878716578465609405619 8825818074867698414108429)
                ·
                  refine ⟨3309681778075386905290661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8825818074867698414108429 3309681778075386905290661)
                  ·
                    refine ⟨620565333389135044741999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309681778075386905290661 620565333389135044741999)
                    ·
                      rfl

theorem cell22_1812820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1812820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812820 prefixEnd_1812820 := by exact prefixLift 1812820
  have htrace : WordTrace (prefixWord ++ tailWord_1812820) baseStart_1812820 baseEnd_1812820 := by
    simpa [prefixWord, tailWord_1812820, baseEnd_1812820] using wordTrace_append hprefix tailTrace_1812820
  have hstable : (prefixWord ++ tailWord_1812820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812820).length < 2 ^ (prefixWord ++ tailWord_1812820).sum := by decide
  have hdescent : baseEnd_1812820 < baseStart_1812820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812837 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_1812837 : Nat := 118140960795 + 1812837 * 2 ^ 59
def prefixEnd_1812837 : Nat := 4983230072969 + 3 ^ 40 * 1812837 * 2
def baseEnd_1812837 : Nat := 620571152836552667066947

theorem tailTrace_1812837 : CollatzResearch.WordTrace tailWord_1812837 prefixEnd_1812837 620571152836552667066947 := by
  unfold tailWord_1812837
  simp only [CollatzResearch.WordTrace]
  refine ⟨66119597333408631755564765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44079731555605754503709843 66119597333408631755564765)
  ·
    refine ⟨24794849000028236908336787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66119597333408631755564765 24794849000028236908336787)
    ·
      refine ⟨37192273500042355362505181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24794849000028236908336787 37192273500042355362505181)
      ·
        refine ⟨13947102562515883260939443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37192273500042355362505181 13947102562515883260939443)
        ·
          refine ⟨20920653843773824891409165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13947102562515883260939443 20920653843773824891409165)
          ·
            refine ⟨7845245191415184334278437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20920653843773824891409165 7845245191415184334278437)
            ·
              refine ⟨1470983473390347062677207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7845245191415184334278437 1470983473390347062677207)
              ·
                refine ⟨2206475210085520594015811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470983473390347062677207 2206475210085520594015811)
                ·
                  refine ⟨3309712815128280891023717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206475210085520594015811 3309712815128280891023717)
                  ·
                    refine ⟨620571152836552667066947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309712815128280891023717 620571152836552667066947)
                    ·
                      rfl

theorem cell22_1812837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_1812837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812837 prefixEnd_1812837 := by exact prefixLift 1812837
  have htrace : WordTrace (prefixWord ++ tailWord_1812837) baseStart_1812837 baseEnd_1812837 := by
    simpa [prefixWord, tailWord_1812837, baseEnd_1812837] using wordTrace_append hprefix tailTrace_1812837
  have hstable : (prefixWord ++ tailWord_1812837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812837).length < 2 ^ (prefixWord ++ tailWord_1812837).sum := by decide
  have hdescent : baseEnd_1812837 < baseStart_1812837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812865 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1812865 : Nat := 118140960795 + 1812865 * 2 ^ 59
def prefixEnd_1812865 : Nat := 4983230072969 + 3 ^ 40 * 1812865 * 2
def baseEnd_1812865 : Nat := 620580737808769927366861

theorem tailTrace_1812865 : CollatzResearch.WordTrace tailWord_1812865 prefixEnd_1812865 620580737808769927366861 := by
  unfold tailWord_1812865
  simp only [CollatzResearch.WordTrace]
  refine ⟨66120618577307192537584049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44080412384871461691722699 66120618577307192537584049)
  ·
    refine ⟨49590463932980394403188037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66120618577307192537584049 49590463932980394403188037)
    ·
      refine ⟨9298211987433823950597757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49590463932980394403188037 9298211987433823950597757)
      ·
        refine ⟨3486829495287683981474159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9298211987433823950597757 3486829495287683981474159)
        ·
          refine ⟨5230244242931525972211239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486829495287683981474159 5230244242931525972211239)
          ·
            refine ⟨7845366364397288958316859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230244242931525972211239 7845366364397288958316859)
            ·
              refine ⟨11768049546595933437475289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845366364397288958316859 11768049546595933437475289)
              ·
                refine ⟨8826037159946950078106467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11768049546595933437475289 8826037159946950078106467)
                ·
                  refine ⟨13239055739920425117159701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8826037159946950078106467 13239055739920425117159701)
                  ·
                    refine ⟨620580737808769927366861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13239055739920425117159701 620580737808769927366861)
                    ·
                      rfl

theorem cell22_1812865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1812865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812865 prefixEnd_1812865 := by exact prefixLift 1812865
  have htrace : WordTrace (prefixWord ++ tailWord_1812865) baseStart_1812865 baseEnd_1812865 := by
    simpa [prefixWord, tailWord_1812865, baseEnd_1812865] using wordTrace_append hprefix tailTrace_1812865
  have hstable : (prefixWord ++ tailWord_1812865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812865).length < 2 ^ (prefixWord ++ tailWord_1812865).sum := by decide
  have hdescent : baseEnd_1812865 < baseStart_1812865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812867 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 1, 5]
def baseStart_1812867 : Nat := 118140960795 + 1812867 * 2 ^ 59
def prefixEnd_1812867 : Nat := 4983230072969 + 3 ^ 40 * 1812867 * 2
def baseEnd_1812867 : Nat := 620581422449642588816855

theorem tailTrace_1812867 : CollatzResearch.WordTrace tailWord_1812867 prefixEnd_1812867 620581422449642588816855 := by
  unfold tailWord_1812867
  simp only [CollatzResearch.WordTrace]
  refine ⟨66120691523299946879156855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44080461015533297919437903 66120691523299946879156855)
  ·
    refine ⟨99181037284949920318735283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66120691523299946879156855 99181037284949920318735283)
    ·
      refine ⟨148771555927424880478102925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99181037284949920318735283 148771555927424880478102925)
      ·
        refine ⟨55789333472784330179288597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148771555927424880478102925 55789333472784330179288597)
        ·
          refine ⟨2615125006536765477154153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55789333472784330179288597 2615125006536765477154153)
          ·
            refine ⟨1961343754902574107865615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615125006536765477154153 1961343754902574107865615)
            ·
              refine ⟨2942015632353861161798423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961343754902574107865615 2942015632353861161798423)
              ·
                refine ⟨4413023448530791742697635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942015632353861161798423 4413023448530791742697635)
                ·
                  refine ⟨6619535172796187614046453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413023448530791742697635 6619535172796187614046453)
                  ·
                    refine ⟨620581422449642588816855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6619535172796187614046453 620581422449642588816855)
                    ·
                      rfl

theorem cell22_1812867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 5].length) (baseStart_1812867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812867 prefixEnd_1812867 := by exact prefixLift 1812867
  have htrace : WordTrace (prefixWord ++ tailWord_1812867) baseStart_1812867 baseEnd_1812867 := by
    simpa [prefixWord, tailWord_1812867, baseEnd_1812867] using wordTrace_append hprefix tailTrace_1812867
  have hstable : (prefixWord ++ tailWord_1812867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812867).length < 2 ^ (prefixWord ++ tailWord_1812867).sum := by decide
  have hdescent : baseEnd_1812867 < baseStart_1812867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812897 : List Nat := [1, 2, 3, 5, 1, 2, 8]
def baseStart_1812897 : Nat := 118140960795 + 1812897 * 2 ^ 59
def prefixEnd_1812897 : Nat := 4983230072969 + 3 ^ 40 * 1812897 * 2
def baseEnd_1812897 : Nat := 22984877483804907798769

theorem tailTrace_1812897 : CollatzResearch.WordTrace tailWord_1812897 prefixEnd_1812897 22984877483804907798769 := by
  unfold tailWord_1812897
  simp only [CollatzResearch.WordTrace]
  refine ⟨66121785713191262002748945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44081190475460841335165963 66121785713191262002748945)
  ·
    refine ⟨49591339284893446502061709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66121785713191262002748945 49591339284893446502061709)
    ·
      refine ⟨18596752231835042438273141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49591339284893446502061709 18596752231835042438273141)
      ·
        refine ⟨1743445521734535228588107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18596752231835042438273141 1743445521734535228588107)
        ·
          refine ⟨2615168282601802842882161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743445521734535228588107 2615168282601802842882161)
          ·
            refine ⟨1961376211951352132161621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615168282601802842882161 1961376211951352132161621)
            ·
              refine ⟨22984877483804907798769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1961376211951352132161621 22984877483804907798769)
              ·
                rfl

theorem cell22_1812897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 8].length) (baseStart_1812897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812897 prefixEnd_1812897 := by exact prefixLift 1812897
  have htrace : WordTrace (prefixWord ++ tailWord_1812897) baseStart_1812897 baseEnd_1812897 := by
    simpa [prefixWord, tailWord_1812897, baseEnd_1812897] using wordTrace_append hprefix tailTrace_1812897
  have hstable : (prefixWord ++ tailWord_1812897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812897).length < 2 ^ (prefixWord ++ tailWord_1812897).sum := by decide
  have hdescent : baseEnd_1812897 < baseStart_1812897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812963 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 1, 3]
def baseStart_1812963 : Nat := 118140960795 + 1812963 * 2 ^ 59
def prefixEnd_1812963 : Nat := 4983230072969 + 3 ^ 40 * 1812963 * 2
def baseEnd_1812963 : Nat := 620614285211530338416561

theorem tailTrace_1812963 : CollatzResearch.WordTrace tailWord_1812963 prefixEnd_1812963 620614285211530338416561 := by
  unfold tailWord_1812963
  simp only [CollatzResearch.WordTrace]
  refine ⟨66124192930952155274651543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44082795287301436849767695 66124192930952155274651543)
  ·
    refine ⟨99186289396428232911977315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66124192930952155274651543 99186289396428232911977315)
    ·
      refine ⟨148779434094642349367965973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99186289396428232911977315 148779434094642349367965973)
      ·
        refine ⟨6974035973186360126623405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148779434094642349367965973 6974035973186360126623405)
        ·
          refine ⟨2615263489944885047483777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6974035973186360126623405 2615263489944885047483777)
          ·
            refine ⟨1961447617458663785612833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615263489944885047483777 1961447617458663785612833)
            ·
              refine ⟨1471085713093997839209625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961447617458663785612833 1471085713093997839209625)
              ·
                refine ⟨1103314284820498379407219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471085713093997839209625 1103314284820498379407219)
                ·
                  refine ⟨1654971427230747569110829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103314284820498379407219 1654971427230747569110829)
                  ·
                    refine ⟨620614285211530338416561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1654971427230747569110829 620614285211530338416561)
                    ·
                      rfl

theorem cell22_1812963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 3].length) (baseStart_1812963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812963 prefixEnd_1812963 := by exact prefixLift 1812963
  have htrace : WordTrace (prefixWord ++ tailWord_1812963) baseStart_1812963 baseEnd_1812963 := by
    simpa [prefixWord, tailWord_1812963, baseEnd_1812963] using wordTrace_append hprefix tailTrace_1812963
  have hstable : (prefixWord ++ tailWord_1812963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812963).length < 2 ^ (prefixWord ++ tailWord_1812963).sum := by decide
  have hdescent : baseEnd_1812963 < baseStart_1812963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812985 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_1812985 : Nat := 118140960795 + 1812985 * 2 ^ 59
def prefixEnd_1812985 : Nat := 4983230072969 + 3 ^ 40 * 1812985 * 2
def baseEnd_1812985 : Nat := 620621816261129614366493

theorem tailTrace_1812985 : CollatzResearch.WordTrace tailWord_1812985 prefixEnd_1812985 620621816261129614366493 := by
  unfold tailWord_1812985
  simp only [CollatzResearch.WordTrace]
  refine ⟨66124995336872453031952409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44083330224581635354634939 66124995336872453031952409)
  ·
    refine ⟨49593746502654339773964307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66124995336872453031952409 49593746502654339773964307)
    ·
      refine ⟨74390619753981509660946461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49593746502654339773964307 74390619753981509660946461)
      ·
        refine ⟨27896482407743066122854923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74390619753981509660946461 27896482407743066122854923)
        ·
          refine ⟨41844723611614599184282385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27896482407743066122854923 41844723611614599184282385)
          ·
            refine ⟨31383542708710949388211789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41844723611614599184282385 31383542708710949388211789)
            ·
              refine ⟨11768828515766606020579421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31383542708710949388211789 11768828515766606020579421)
              ·
                refine ⟨4413310693412477257717283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11768828515766606020579421 4413310693412477257717283)
                ·
                  refine ⟨6619966040118715886575925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413310693412477257717283 6619966040118715886575925)
                  ·
                    refine ⟨620621816261129614366493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6619966040118715886575925 620621816261129614366493)
                    ·
                      rfl

theorem cell22_1812985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_1812985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812985 prefixEnd_1812985 := by exact prefixLift 1812985
  have htrace : WordTrace (prefixWord ++ tailWord_1812985) baseStart_1812985 baseEnd_1812985 := by
    simpa [prefixWord, tailWord_1812985, baseEnd_1812985] using wordTrace_append hprefix tailTrace_1812985
  have hstable : (prefixWord ++ tailWord_1812985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812985).length < 2 ^ (prefixWord ++ tailWord_1812985).sum := by decide
  have hdescent : baseEnd_1812985 < baseStart_1812985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813002 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1813002 : Nat := 118140960795 + 1813002 * 2 ^ 59
def prefixEnd_1813002 : Nat := 4983230072969 + 3 ^ 40 * 1813002 * 2
def baseEnd_1813002 : Nat := 620627635708547236691441

theorem tailTrace_1813002 : CollatzResearch.WordTrace tailWord_1813002 prefixEnd_1813002 620627635708547236691441 := by
  unfold tailWord_1813002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16531403844452716233830315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44083743585207243290214173 16531403844452716233830315)
  ·
    refine ⟨24797105766679074350745473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16531403844452716233830315 24797105766679074350745473)
    ·
      refine ⟨18597829325009305763059105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24797105766679074350745473 18597829325009305763059105)
      ·
        refine ⟨13948371993756979322294329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18597829325009305763059105 13948371993756979322294329)
        ·
          refine ⟨10461278995317734491720747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13948371993756979322294329 10461278995317734491720747)
          ·
            refine ⟨15691918492976601737581121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461278995317734491720747 15691918492976601737581121)
            ·
              refine ⟨11768938869732451303185841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15691918492976601737581121 11768938869732451303185841)
              ·
                refine ⟨8826704152299338477389381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11768938869732451303185841 8826704152299338477389381)
                ·
                  refine ⟨1655007028556125964510509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8826704152299338477389381 1655007028556125964510509)
                  ·
                    refine ⟨620627635708547236691441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655007028556125964510509 620627635708547236691441)
                    ·
                      rfl

theorem cell22_1813002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1813002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813002 prefixEnd_1813002 := by exact prefixLift 1813002
  have htrace : WordTrace (prefixWord ++ tailWord_1813002) baseStart_1813002 baseEnd_1813002 := by
    simpa [prefixWord, tailWord_1813002, baseEnd_1813002] using wordTrace_append hprefix tailTrace_1813002
  have hstable : (prefixWord ++ tailWord_1813002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813002).length < 2 ^ (prefixWord ++ tailWord_1813002).sum := by decide
  have hdescent : baseEnd_1813002 < baseStart_1813002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813004 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 4]
def baseStart_1813004 : Nat := 118140960795 + 1813004 * 2 ^ 59
def prefixEnd_1813004 : Nat := 4983230072969 + 3 ^ 40 * 1813004 * 2
def baseEnd_1813004 : Nat := 206876106783139966047145

theorem tailTrace_1813004 : CollatzResearch.WordTrace tailWord_1813004 prefixEnd_1813004 206876106783139966047145 := by
  unfold tailWord_1813004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33062844161901809638447033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44083792215869079517929377 33062844161901809638447033)
  ·
    refine ⟨24797133121426357228835275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33062844161901809638447033 24797133121426357228835275)
    ·
      refine ⟨37195699682139535843252913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24797133121426357228835275 37195699682139535843252913)
      ·
        refine ⟨27896774761604651882439685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37195699682139535843252913 27896774761604651882439685)
        ·
          refine ⟨5230645267800872227957441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27896774761604651882439685 5230645267800872227957441)
          ·
            refine ⟨3922983950850654170968081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230645267800872227957441 3922983950850654170968081)
            ·
              refine ⟨2942237963137990628226061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922983950850654170968081 2942237963137990628226061)
              ·
                refine ⟨1103339236176746485584773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2942237963137990628226061 1103339236176746485584773)
                ·
                  refine ⟨206876106783139966047145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103339236176746485584773 206876106783139966047145)
                  ·
                    rfl

theorem cell22_1813004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_1813004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813004 prefixEnd_1813004 := by exact prefixLift 1813004
  have htrace : WordTrace (prefixWord ++ tailWord_1813004) baseStart_1813004 baseEnd_1813004 := by
    simpa [prefixWord, tailWord_1813004, baseEnd_1813004] using wordTrace_append hprefix tailTrace_1813004
  have hstable : (prefixWord ++ tailWord_1813004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813004).length < 2 ^ (prefixWord ++ tailWord_1813004).sum := by decide
  have hdescent : baseEnd_1813004 < baseStart_1813004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813006 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_1813006 : Nat := 118140960795 + 1813006 * 2 ^ 59
def prefixEnd_1813006 : Nat := 4983230072969 + 3 ^ 40 * 1813006 * 2
def baseEnd_1813006 : Nat := 620629004990292559591429

theorem tailTrace_1813006 : CollatzResearch.WordTrace tailWord_1813006 prefixEnd_1813006 620629004990292559591429 := by
  unfold tailWord_1813006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265720158724546702308359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44083840846530915745644581 8265720158724546702308359)
  ·
    refine ⟨12398580238086820053462539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8265720158724546702308359 12398580238086820053462539)
    ·
      refine ⟨18597870357130230080193809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12398580238086820053462539 18597870357130230080193809)
      ·
        refine ⟨13948402767847672560145357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18597870357130230080193809 13948402767847672560145357)
        ·
          refine ⟨5230651037942877210054509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13948402767847672560145357 5230651037942877210054509)
          ·
            refine ⟨1961494139228578953770441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5230651037942877210054509 1961494139228578953770441)
            ·
              refine ⟨1471120604421434215327831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961494139228578953770441 1471120604421434215327831)
              ·
                refine ⟨2206680906632151322991747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471120604421434215327831 2206680906632151322991747)
                ·
                  refine ⟨3310021359948226984487621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206680906632151322991747 3310021359948226984487621)
                  ·
                    refine ⟨620629004990292559591429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310021359948226984487621 620629004990292559591429)
                    ·
                      rfl

theorem cell22_1813006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_1813006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813006 prefixEnd_1813006 := by exact prefixLift 1813006
  have htrace : WordTrace (prefixWord ++ tailWord_1813006) baseStart_1813006 baseEnd_1813006 := by
    simpa [prefixWord, tailWord_1813006, baseEnd_1813006] using wordTrace_append hprefix tailTrace_1813006
  have hstable : (prefixWord ++ tailWord_1813006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813006).length < 2 ^ (prefixWord ++ tailWord_1813006).sum := by decide
  have hdescent : baseEnd_1813006 < baseStart_1813006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813047 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 3, 3]
def baseStart_1813047 : Nat := 118140960795 + 1813047 * 2 ^ 59
def prefixEnd_1813047 : Nat := 4983230072969 + 3 ^ 40 * 1813047 * 2
def baseEnd_1813047 : Nat := 620643040128182119316303

theorem tailTrace_1813047 : CollatzResearch.WordTrace tailWord_1813047 prefixEnd_1813047 620643040128182119316303 := by
  unfold tailWord_1813047
  simp only [CollatzResearch.WordTrace]
  refine ⟨66127256662647837620709395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44084837775098558413806263 66127256662647837620709395)
  ·
    refine ⟨99190884993971756431064093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66127256662647837620709395 99190884993971756431064093)
    ·
      refine ⟨37196581872739408661649035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99190884993971756431064093 37196581872739408661649035)
      ·
        refine ⟨55794872809109112992473553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37196581872739408661649035 55794872809109112992473553)
        ·
          refine ⟨41846154606831834744355165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55794872809109112992473553 41846154606831834744355165)
          ·
            refine ⟨15692307977561938029133187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41846154606831834744355165 15692307977561938029133187)
            ·
              refine ⟨23538461966342907043699781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15692307977561938029133187 23538461966342907043699781)
              ·
                refine ⟨4413461618689295070693709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23538461966342907043699781 4413461618689295070693709)
                ·
                  refine ⟨1655048107008485651510141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4413461618689295070693709 1655048107008485651510141)
                  ·
                    refine ⟨620643040128182119316303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655048107008485651510141 620643040128182119316303)
                    ·
                      rfl

theorem cell22_1813047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_1813047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813047 prefixEnd_1813047 := by exact prefixLift 1813047
  have htrace : WordTrace (prefixWord ++ tailWord_1813047) baseStart_1813047 baseEnd_1813047 := by
    simpa [prefixWord, tailWord_1813047, baseEnd_1813047] using wordTrace_append hprefix tailTrace_1813047
  have hstable : (prefixWord ++ tailWord_1813047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813047).length < 2 ^ (prefixWord ++ tailWord_1813047).sum := by decide
  have hdescent : baseEnd_1813047 < baseStart_1813047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813107 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 1, 4]
def baseStart_1813107 : Nat := 118140960795 + 1813107 * 2 ^ 59
def prefixEnd_1813107 : Nat := 4983230072969 + 3 ^ 40 * 1813107 * 2
def baseEnd_1813107 : Nat := 620663579354361962816119

theorem tailTrace_1813107 : CollatzResearch.WordTrace tailWord_1813107 prefixEnd_1813107 620663579354361962816119 := by
  unfold tailWord_1813107
  simp only [CollatzResearch.WordTrace]
  refine ⟨66129445042430467867893575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44086296694953645245262383 66129445042430467867893575)
  ·
    refine ⟨99194167563645701801840363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66129445042430467867893575 99194167563645701801840363)
    ·
      refine ⟨148791251345468552702760545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99194167563645701801840363 148791251345468552702760545)
      ·
        refine ⟨111593438509101414527070409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148791251345468552702760545 111593438509101414527070409)
        ·
          refine ⟨83695078881826060895302807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111593438509101414527070409 83695078881826060895302807)
          ·
            refine ⟨125542618322739091342954211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83695078881826060895302807 125542618322739091342954211)
            ·
              refine ⟨188313927484108637014431317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125542618322739091342954211 188313927484108637014431317)
              ·
                refine ⟨2206803837704398090012867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 188313927484108637014431317 2206803837704398090012867)
                ·
                  refine ⟨3310205756556597135019301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206803837704398090012867 3310205756556597135019301)
                  ·
                    refine ⟨620663579354361962816119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310205756556597135019301 620663579354361962816119)
                    ·
                      rfl

theorem cell22_1813107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 4].length) (baseStart_1813107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813107 prefixEnd_1813107 := by exact prefixLift 1813107
  have htrace : WordTrace (prefixWord ++ tailWord_1813107) baseStart_1813107 baseEnd_1813107 := by
    simpa [prefixWord, tailWord_1813107, baseEnd_1813107] using wordTrace_append hprefix tailTrace_1813107
  have hstable : (prefixWord ++ tailWord_1813107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813107).length < 2 ^ (prefixWord ++ tailWord_1813107).sum := by decide
  have hdescent : baseEnd_1813107 < baseStart_1813107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813137 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_1813137 : Nat := 118140960795 + 1813137 * 2 ^ 59
def prefixEnd_1813137 : Nat := 4983230072969 + 3 ^ 40 * 1813137 * 2
def baseEnd_1813137 : Nat := 620673848967451884566027

theorem tailTrace_1813137 : CollatzResearch.WordTrace tailWord_1813137 prefixEnd_1813137 620673848967451884566027 := by
  unfold tailWord_1813137
  simp only [CollatzResearch.WordTrace]
  refine ⟨66130539232321782991485665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44087026154881188660990443 66130539232321782991485665)
  ·
    refine ⟨49597904424241337243614249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66130539232321782991485665 49597904424241337243614249)
    ·
      refine ⟨37198428318181002932710687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49597904424241337243614249 37198428318181002932710687)
      ·
        refine ⟨55797642477271504399066031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37198428318181002932710687 55797642477271504399066031)
        ·
          refine ⟨83696463715907256598599047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55797642477271504399066031 83696463715907256598599047)
          ·
            refine ⟨125544695573860884897898571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83696463715907256598599047 125544695573860884897898571)
            ·
              refine ⟨188317043360791327346847857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125544695573860884897898571 188317043360791327346847857)
              ·
                refine ⟨141237782520593495510135893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188317043360791327346847857 141237782520593495510135893)
                ·
                  refine ⟨1655130263913205025509405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 141237782520593495510135893 1655130263913205025509405)
                  ·
                    refine ⟨620673848967451884566027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655130263913205025509405 620673848967451884566027)
                    ·
                      rfl

theorem cell22_1813137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_1813137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813137 prefixEnd_1813137 := by exact prefixLift 1813137
  have htrace : WordTrace (prefixWord ++ tailWord_1813137) baseStart_1813137 baseEnd_1813137 := by
    simpa [prefixWord, tailWord_1813137, baseEnd_1813137] using wordTrace_append hprefix tailTrace_1813137
  have hstable : (prefixWord ++ tailWord_1813137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813137).length < 2 ^ (prefixWord ++ tailWord_1813137).sum := by decide
  have hdescent : baseEnd_1813137 < baseStart_1813137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813188 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1813188 : Nat := 118140960795 + 1813188 * 2 ^ 59
def prefixEnd_1813188 : Nat := 4983230072969 + 3 ^ 40 * 1813188 * 2
def baseEnd_1813188 : Nat := 620691307309704751540871

theorem tailTrace_1813188 : CollatzResearch.WordTrace tailWord_1813188 prefixEnd_1813188 620691307309704751540871 := by
  unfold tailWord_1813188
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066199677568509350796109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44088266236758012467728145 33066199677568509350796109)
  ·
    refine ⟨12399824879088191006548541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33066199677568509350796109 12399824879088191006548541)
    ·
      refine ⟨4649934329658071627455703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12399824879088191006548541 4649934329658071627455703)
      ·
        refine ⟨6974901494487107441183555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649934329658071627455703 6974901494487107441183555)
        ·
          refine ⟨10462352241730661161775333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974901494487107441183555 10462352241730661161775333)
          ·
            refine ⟨1961691045324498967832875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10462352241730661161775333 1961691045324498967832875)
            ·
              refine ⟨2942536567986748451749313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961691045324498967832875 2942536567986748451749313)
              ·
                refine ⟨2206902425990061338811985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942536567986748451749313 2206902425990061338811985)
                ·
                  refine ⟨1655176819492546004108989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206902425990061338811985 1655176819492546004108989)
                  ·
                    refine ⟨620691307309704751540871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655176819492546004108989 620691307309704751540871)
                    ·
                      rfl

theorem cell22_1813188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1813188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813188 prefixEnd_1813188 := by exact prefixLift 1813188
  have htrace : WordTrace (prefixWord ++ tailWord_1813188) baseStart_1813188 baseEnd_1813188 := by
    simpa [prefixWord, tailWord_1813188, baseEnd_1813188] using wordTrace_append hprefix tailTrace_1813188
  have hstable : (prefixWord ++ tailWord_1813188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813188).length < 2 ^ (prefixWord ++ tailWord_1813188).sum := by decide
  have hdescent : baseEnd_1813188 < baseStart_1813188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813205 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_1813205 : Nat := 118140960795 + 1813205 * 2 ^ 59
def prefixEnd_1813205 : Nat := 4983230072969 + 3 ^ 40 * 1813205 * 2
def baseEnd_1813205 : Nat := 620697126757122373865819

theorem tailTrace_1813205 : CollatzResearch.WordTrace tailWord_1813205 prefixEnd_1813205 620697126757122373865819 := by
  unfold tailWord_1813205
  simp only [CollatzResearch.WordTrace]
  refine ⟨66133019396075430604961069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44088679597383620403307379 66133019396075430604961069)
  ·
    refine ⟨24799882273528286476860401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66133019396075430604961069 24799882273528286476860401)
    ·
      refine ⟨18599911705146214857645301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24799882273528286476860401 18599911705146214857645301)
      ·
        refine ⟨1743741722357457642904247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18599911705146214857645301 1743741722357457642904247)
        ·
          refine ⟨2615612583536186464356371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743741722357457642904247 2615612583536186464356371)
          ·
            refine ⟨3923418875304279696534557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615612583536186464356371 3923418875304279696534557)
            ·
              refine ⟨1471282078239104886200459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3923418875304279696534557 1471282078239104886200459)
              ·
                refine ⟨2206923117358657329300689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471282078239104886200459 2206923117358657329300689)
                ·
                  refine ⟨1655192338018992996975517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206923117358657329300689 1655192338018992996975517)
                  ·
                    refine ⟨620697126757122373865819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655192338018992996975517 620697126757122373865819)
                    ·
                      rfl

theorem cell22_1813205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_1813205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813205 prefixEnd_1813205 := by exact prefixLift 1813205
  have htrace : WordTrace (prefixWord ++ tailWord_1813205) baseStart_1813205 baseEnd_1813205 := by
    simpa [prefixWord, tailWord_1813205, baseEnd_1813205] using wordTrace_append hprefix tailTrace_1813205
  have hstable : (prefixWord ++ tailWord_1813205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813205).length < 2 ^ (prefixWord ++ tailWord_1813205).sum := by decide
  have hdescent : baseEnd_1813205 < baseStart_1813205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813276 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1813276 : Nat := 118140960795 + 1813276 * 2 ^ 59
def prefixEnd_1813276 : Nat := 4983230072969 + 3 ^ 40 * 1813276 * 2
def baseEnd_1813276 : Nat := 620721431508101855340601

theorem tailTrace_1813276 : CollatzResearch.WordTrace tailWord_1813276 prefixEnd_1813276 620721431508101855340601 := by
  unfold tailWord_1813276
  simp only [CollatzResearch.WordTrace]
  refine ⟨33067804489409104865397841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44090405985878806487197121 33067804489409104865397841)
  ·
    refine ⟨24800853367056828649048381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33067804489409104865397841 24800853367056828649048381)
    ·
      refine ⟨9300320012646310743393143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24800853367056828649048381 9300320012646310743393143)
      ·
        refine ⟨13950480018969466115089715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300320012646310743393143 13950480018969466115089715)
        ·
          refine ⟨20925720028454199172634573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13950480018969466115089715 20925720028454199172634573)
          ·
            refine ⟨7847145010670324689737965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20925720028454199172634573 7847145010670324689737965)
            ·
              refine ⟨2942679379001371758651737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7847145010670324689737965 2942679379001371758651737)
              ·
                refine ⟨2207009534251028818988803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942679379001371758651737 2207009534251028818988803)
                ·
                  refine ⟨3310514301376543228483205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207009534251028818988803 3310514301376543228483205)
                  ·
                    refine ⟨620721431508101855340601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310514301376543228483205 620721431508101855340601)
                    ·
                      rfl

theorem cell22_1813276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1813276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813276 prefixEnd_1813276 := by exact prefixLift 1813276
  have htrace : WordTrace (prefixWord ++ tailWord_1813276) baseStart_1813276 baseEnd_1813276 := by
    simpa [prefixWord, tailWord_1813276, baseEnd_1813276] using wordTrace_append hprefix tailTrace_1813276
  have hstable : (prefixWord ++ tailWord_1813276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813276).length < 2 ^ (prefixWord ++ tailWord_1813276).sum := by decide
  have hdescent : baseEnd_1813276 < baseStart_1813276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813304 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_1813304 : Nat := 118140960795 + 1813304 * 2 ^ 59
def prefixEnd_1813304 : Nat := 4983230072969 + 3 ^ 40 * 1813304 * 2
def baseEnd_1813304 : Nat := 620731016480319115640515

theorem tailTrace_1813304 : CollatzResearch.WordTrace tailWord_1813304 prefixEnd_1813304 620731016480319115640515 := by
  unfold tailWord_1813304
  simp only [CollatzResearch.WordTrace]
  refine ⟨33068315111358385256407483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44091086815144513675209977 33068315111358385256407483)
  ·
    refine ⟨49602472667037577884611225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33068315111358385256407483 49602472667037577884611225)
    ·
      refine ⟨37201854500278183413458419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49602472667037577884611225 37201854500278183413458419)
      ·
        refine ⟨55802781750417275120187629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37201854500278183413458419 55802781750417275120187629)
        ·
          refine ⟨20926043156406478170070361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55802781750417275120187629 20926043156406478170070361)
          ·
            refine ⟨15694532367304858627552771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20926043156406478170070361 15694532367304858627552771)
            ·
              refine ⟨23541798550957287941329157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15694532367304858627552771 23541798550957287941329157)
              ·
                refine ⟨4414087228304491488999217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23541798550957287941329157 4414087228304491488999217)
                ·
                  refine ⟨3310565421228368616749413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414087228304491488999217 3310565421228368616749413)
                  ·
                    refine ⟨620731016480319115640515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310565421228368616749413 620731016480319115640515)
                    ·
                      rfl

theorem cell22_1813304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_1813304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813304 prefixEnd_1813304 := by exact prefixLift 1813304
  have htrace : WordTrace (prefixWord ++ tailWord_1813304) baseStart_1813304 baseEnd_1813304 := by
    simpa [prefixWord, tailWord_1813304, baseEnd_1813304] using wordTrace_append hprefix tailTrace_1813304
  have hstable : (prefixWord ++ tailWord_1813304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813304).length < 2 ^ (prefixWord ++ tailWord_1813304).sum := by decide
  have hdescent : baseEnd_1813304 < baseStart_1813304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813379 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_1813379 : Nat := 118140960795 + 1813379 * 2 ^ 59
def prefixEnd_1813379 : Nat := 4983230072969 + 3 ^ 40 * 1813379 * 2
def baseEnd_1813379 : Nat := 620756690513043920015285

theorem tailTrace_1813379 : CollatzResearch.WordTrace tailWord_1813379 prefixEnd_1813379 620756690513043920015285 := by
  unfold tailWord_1813379
  simp only [CollatzResearch.WordTrace]
  refine ⟨66139365697445058321795191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44092910464963372214530127 66139365697445058321795191)
  ·
    refine ⟨99209048546167587482692787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66139365697445058321795191 99209048546167587482692787)
    ·
      refine ⟨148813572819251381224039181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99209048546167587482692787 148813572819251381224039181)
      ·
        refine ⟨55805089807219267959014693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148813572819251381224039181 55805089807219267959014693)
        ·
          refine ⟨10463454338853612742315255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55805089807219267959014693 10463454338853612742315255)
          ·
            refine ⟨15695181508280419113472883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10463454338853612742315255 15695181508280419113472883)
            ·
              refine ⟨23542772262420628670209325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695181508280419113472883 23542772262420628670209325)
              ·
                refine ⟨8828539598407735751328497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23542772262420628670209325 8828539598407735751328497)
                ·
                  refine ⟨6621404698805801813496373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8828539598407735751328497 6621404698805801813496373)
                  ·
                    refine ⟨620756690513043920015285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6621404698805801813496373 620756690513043920015285)
                    ·
                      rfl

theorem cell22_1813379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_1813379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813379 prefixEnd_1813379 := by exact prefixLift 1813379
  have htrace : WordTrace (prefixWord ++ tailWord_1813379) baseStart_1813379 baseEnd_1813379 := by
    simpa [prefixWord, tailWord_1813379, baseEnd_1813379] using wordTrace_append hprefix tailTrace_1813379
  have hstable : (prefixWord ++ tailWord_1813379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813379).length < 2 ^ (prefixWord ++ tailWord_1813379).sum := by decide
  have hdescent : baseEnd_1813379 < baseStart_1813379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813402 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_1813402 : Nat := 118140960795 + 1813402 * 2 ^ 59
def prefixEnd_1813402 : Nat := 4983230072969 + 3 ^ 40 * 1813402 * 2
def baseEnd_1813402 : Nat := 620764563883079526690215

theorem tailTrace_1813402 : CollatzResearch.WordTrace tailWord_1813402 prefixEnd_1813402 620764563883079526690215 := by
  unfold tailWord_1813402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535051144090433312470615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44093469717574488833254973 16535051144090433312470615)
  ·
    refine ⟨24802576716135649968705923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16535051144090433312470615 24802576716135649968705923)
    ·
      refine ⟨37203865074203474953058885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24802576716135649968705923 37203865074203474953058885)
      ·
        refine ⟨6975724701413151553698541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37203865074203474953058885 6975724701413151553698541)
        ·
          refine ⟨2615896763029931832636953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6975724701413151553698541 2615896763029931832636953)
          ·
            refine ⟨1961922572272448874477715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615896763029931832636953 1961922572272448874477715)
            ·
              refine ⟨2942883858408673311716573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961922572272448874477715 2942883858408673311716573)
              ·
                refine ⟨1103581446903252491893715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2942883858408673311716573 1103581446903252491893715)
                ·
                  refine ⟨1655372170354878737840573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103581446903252491893715 1655372170354878737840573)
                  ·
                    refine ⟨620764563883079526690215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655372170354878737840573 620764563883079526690215)
                    ·
                      rfl

theorem cell22_1813402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_1813402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813402 prefixEnd_1813402 := by exact prefixLift 1813402
  have htrace : WordTrace (prefixWord ++ tailWord_1813402) baseStart_1813402 baseEnd_1813402 := by
    simpa [prefixWord, tailWord_1813402, baseEnd_1813402] using wordTrace_append hprefix tailTrace_1813402
  have hstable : (prefixWord ++ tailWord_1813402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813402).length < 2 ^ (prefixWord ++ tailWord_1813402).sum := by decide
  have hdescent : baseEnd_1813402 < baseStart_1813402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813411 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 1, 4]
def baseStart_1813411 : Nat := 118140960795 + 1813411 * 2 ^ 59
def prefixEnd_1813411 : Nat := 4983230072969 + 3 ^ 40 * 1813411 * 2
def baseEnd_1813411 : Nat := 620767644767006503215187

theorem tailTrace_1813411 : CollatzResearch.WordTrace tailWord_1813411 prefixEnd_1813411 620767644767006503215187 := by
  unfold tailWord_1813411
  simp only [CollatzResearch.WordTrace]
  refine ⟨66140532833329127786960087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44093688555552751857973391 66140532833329127786960087)
  ·
    refine ⟨99210799249993691680440131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66140532833329127786960087 99210799249993691680440131)
    ·
      refine ⟨148816198874990537520660197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99210799249993691680440131 148816198874990537520660197)
      ·
        refine ⟨27903037289060725785123787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148816198874990537520660197 27903037289060725785123787)
        ·
          refine ⟨41854555933591088677685681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27903037289060725785123787 41854555933591088677685681)
          ·
            refine ⟨31390916950193316508264261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41854555933591088677685681 31390916950193316508264261)
            ·
              refine ⟨5885796928161246845299549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31390916950193316508264261 5885796928161246845299549)
              ·
                refine ⟨2207173848060467566987331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5885796928161246845299549 2207173848060467566987331)
                ·
                  refine ⟨3310760772090701350480997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207173848060467566987331 3310760772090701350480997)
                  ·
                    refine ⟨620767644767006503215187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310760772090701350480997 620767644767006503215187)
                    ·
                      rfl

theorem cell22_1813411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 4].length) (baseStart_1813411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813411 prefixEnd_1813411 := by exact prefixLift 1813411
  have htrace : WordTrace (prefixWord ++ tailWord_1813411) baseStart_1813411 baseEnd_1813411 := by
    simpa [prefixWord, tailWord_1813411, baseEnd_1813411] using wordTrace_append hprefix tailTrace_1813411
  have hstable : (prefixWord ++ tailWord_1813411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813411).length < 2 ^ (prefixWord ++ tailWord_1813411).sum := by decide
  have hdescent : baseEnd_1813411 < baseStart_1813411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813439 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_1813439 : Nat := 118140960795 + 1813439 * 2 ^ 59
def prefixEnd_1813439 : Nat := 4983230072969 + 3 ^ 40 * 1813439 * 2
def baseEnd_1813439 : Nat := 620777229739223763515101

theorem tailTrace_1813439 : CollatzResearch.WordTrace tailWord_1813439 prefixEnd_1813439 620777229739223763515101 := by
  unfold tailWord_1813439
  simp only [CollatzResearch.WordTrace]
  refine ⟨66141554077227688568979371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44094369384818459045986247 66141554077227688568979371)
  ·
    refine ⟨99212331115841532853469057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66141554077227688568979371 99212331115841532853469057)
    ·
      refine ⟨74409248336881149640101793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99212331115841532853469057 74409248336881149640101793)
      ·
        refine ⟨55806936252660862230076345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74409248336881149640101793 55806936252660862230076345)
        ·
          refine ⟨41855202189495646672557259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55806936252660862230076345 41855202189495646672557259)
          ·
            refine ⟨62782803284243470008835889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41855202189495646672557259 62782803284243470008835889)
            ·
              refine ⟨47087102463182602506626917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62782803284243470008835889 47087102463182602506626917)
              ·
                refine ⟨8828831711846737969992547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47087102463182602506626917 8828831711846737969992547)
                ·
                  refine ⟨13243247567770106954988821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8828831711846737969992547 13243247567770106954988821)
                  ·
                    refine ⟨620777229739223763515101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13243247567770106954988821 620777229739223763515101)
                    ·
                      rfl

theorem cell22_1813439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_1813439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813439 prefixEnd_1813439 := by exact prefixLift 1813439
  have htrace : WordTrace (prefixWord ++ tailWord_1813439) baseStart_1813439 baseEnd_1813439 := by
    simpa [prefixWord, tailWord_1813439, baseEnd_1813439] using wordTrace_append hprefix tailTrace_1813439
  have hstable : (prefixWord ++ tailWord_1813439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813439).length < 2 ^ (prefixWord ++ tailWord_1813439).sum := by decide
  have hdescent : baseEnd_1813439 < baseStart_1813439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813458 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1813458 : Nat := 118140960795 + 1813458 * 2 ^ 59
def prefixEnd_1813458 : Nat := 4983230072969 + 3 ^ 40 * 1813458 * 2
def baseEnd_1813458 : Nat := 620783733827514047290043

theorem tailTrace_1813458 : CollatzResearch.WordTrace tailWord_1813458 prefixEnd_1813458 620783733827514047290043 := by
  unfold tailWord_1813458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535561766039713703480257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44094831376105903209280685 16535561766039713703480257)
  ·
    refine ⟨12401671324529785277610193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16535561766039713703480257 12401671324529785277610193)
    ·
      refine ⟨9301253493397338958207645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12401671324529785277610193 9301253493397338958207645)
      ·
        refine ⟨3487970060024002109327867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9301253493397338958207645 3487970060024002109327867)
        ·
          refine ⟨5231955090036003163991801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487970060024002109327867 5231955090036003163991801)
          ·
            refine ⟨3923966317527002372993851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5231955090036003163991801 3923966317527002372993851)
            ·
              refine ⟨5885949476290503559490777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923966317527002372993851 5885949476290503559490777)
              ·
                refine ⟨4414462107217877669618083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885949476290503559490777 4414462107217877669618083)
                ·
                  refine ⟨6621693160826816504427125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414462107217877669618083 6621693160826816504427125)
                  ·
                    refine ⟨620783733827514047290043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6621693160826816504427125 620783733827514047290043)
                    ·
                      rfl

theorem cell22_1813458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1813458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813458 prefixEnd_1813458 := by exact prefixLift 1813458
  have htrace : WordTrace (prefixWord ++ tailWord_1813458) baseStart_1813458 baseEnd_1813458 := by
    simpa [prefixWord, tailWord_1813458, baseEnd_1813458] using wordTrace_append hprefix tailTrace_1813458
  have hstable : (prefixWord ++ tailWord_1813458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813458).length < 2 ^ (prefixWord ++ tailWord_1813458).sum := by decide
  have hdescent : baseEnd_1813458 < baseStart_1813458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813462 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1813462 : Nat := 118140960795 + 1813462 * 2 ^ 59
def prefixEnd_1813462 : Nat := 4983230072969 + 3 ^ 40 * 1813462 * 2
def baseEnd_1813462 : Nat := 620785103109259370190031

theorem tailTrace_1813462 : CollatzResearch.WordTrace tailWord_1813462 prefixEnd_1813462 620785103109259370190031 := by
  unfold tailWord_1813462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133899559759022718566665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44094928637429575664711093 4133899559759022718566665)
  ·
    refine ⟨3100424669819267038924999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4133899559759022718566665 3100424669819267038924999)
    ·
      refine ⟨4650637004728900558387499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100424669819267038924999 4650637004728900558387499)
      ·
        refine ⟨6975955507093350837581249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650637004728900558387499 6975955507093350837581249)
        ·
          refine ⟨5231966630320013128185937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6975955507093350837581249 5231966630320013128185937)
          ·
            refine ⟨3923974972740009846139453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5231966630320013128185937 3923974972740009846139453)
            ·
              refine ⟨1471490614777503692302295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3923974972740009846139453 1471490614777503692302295)
              ·
                refine ⟨2207235922166255538453443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471490614777503692302295 2207235922166255538453443)
                ·
                  refine ⟨3310853883249383307680165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207235922166255538453443 3310853883249383307680165)
                  ·
                    refine ⟨620785103109259370190031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310853883249383307680165 620785103109259370190031)
                    ·
                      rfl

theorem cell22_1813462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1813462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813462 prefixEnd_1813462 := by exact prefixLift 1813462
  have htrace : WordTrace (prefixWord ++ tailWord_1813462) baseStart_1813462 baseEnd_1813462 := by
    simpa [prefixWord, tailWord_1813462, baseEnd_1813462] using wordTrace_append hprefix tailTrace_1813462
  have hstable : (prefixWord ++ tailWord_1813462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813462).length < 2 ^ (prefixWord ++ tailWord_1813462).sum := by decide
  have hdescent : baseEnd_1813462 < baseStart_1813462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813471 : List Nat := [1, 1, 2, 3, 6, 9]
def baseStart_1813471 : Nat := 118140960795 + 1813471 * 2 ^ 59
def prefixEnd_1813471 : Nat := 4983230072969 + 3 ^ 40 * 1813471 * 2
def baseEnd_1813471 : Nat := 7664051654236868477963

theorem tailTrace_1813471 : CollatzResearch.WordTrace tailWord_1813471 prefixEnd_1813471 7664051654236868477963 := by
  unfold tailWord_1813471
  simp only [CollatzResearch.WordTrace]
  refine ⟨66142721213111758034144267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44095147475407838689429511 66142721213111758034144267)
  ·
    refine ⟨99214081819667637051216401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66142721213111758034144267 99214081819667637051216401)
    ·
      refine ⟨74410561364750727788412301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99214081819667637051216401 74410561364750727788412301)
      ·
        refine ⟨27903960511781522920654613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74410561364750727788412301 27903960511781522920654613)
        ·
          refine ⟨1307998148989758886905685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27903960511781522920654613 1307998148989758886905685)
          ·
            refine ⟨7664051654236868477963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1307998148989758886905685 7664051654236868477963)
            ·
              rfl

theorem cell22_1813471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 9].length) (baseStart_1813471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813471 prefixEnd_1813471 := by exact prefixLift 1813471
  have htrace : WordTrace (prefixWord ++ tailWord_1813471) baseStart_1813471 baseEnd_1813471 := by
    simpa [prefixWord, tailWord_1813471, baseEnd_1813471] using wordTrace_append hprefix tailTrace_1813471
  have hstable : (prefixWord ++ tailWord_1813471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813471).length < 2 ^ (prefixWord ++ tailWord_1813471).sum := by decide
  have hdescent : baseEnd_1813471 < baseStart_1813471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813499 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 9]
def baseStart_1813499 : Nat := 118140960795 + 1813499 * 2 ^ 59
def prefixEnd_1813499 : Nat := 4983230072969 + 3 ^ 40 * 1813499 * 2
def baseEnd_1813499 : Nat := 206932589655134535671639

theorem tailTrace_1813499 : CollatzResearch.WordTrace tailWord_1813499 prefixEnd_1813499 206932589655134535671639 := by
  unfold tailWord_1813499
  simp only [CollatzResearch.WordTrace]
  refine ⟨66143742457010318816163551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44095828304673545877442367 66143742457010318816163551)
  ·
    refine ⟨99215613685515478224245327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66143742457010318816163551 99215613685515478224245327)
    ·
      refine ⟨148823420528273217336367991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99215613685515478224245327 148823420528273217336367991)
      ·
        refine ⟨223235130792409826004551987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148823420528273217336367991 223235130792409826004551987)
        ·
          refine ⟨334852696188614739006827981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223235130792409826004551987 334852696188614739006827981)
          ·
            refine ⟨125569761070730527127560493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334852696188614739006827981 125569761070730527127560493)
            ·
              refine ⟨47088660401523947672835185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125569761070730527127560493 47088660401523947672835185)
              ·
                refine ⟨35316495301142960754626389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47088660401523947672835185 35316495301142960754626389)
                ·
                  refine ⟨206932589655134535671639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35316495301142960754626389 206932589655134535671639)
                  ·
                    rfl

theorem cell22_1813499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_1813499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813499 prefixEnd_1813499 := by exact prefixLift 1813499
  have htrace : WordTrace (prefixWord ++ tailWord_1813499) baseStart_1813499 baseEnd_1813499 := by
    simpa [prefixWord, tailWord_1813499, baseEnd_1813499] using wordTrace_append hprefix tailTrace_1813499
  have hstable : (prefixWord ++ tailWord_1813499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813499).length < 2 ^ (prefixWord ++ tailWord_1813499).sum := by decide
  have hdescent : baseEnd_1813499 < baseStart_1813499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813533 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 7]
def baseStart_1813533 : Nat := 118140960795 + 1813533 * 2 ^ 59
def prefixEnd_1813533 : Nat := 4983230072969 + 3 ^ 40 * 1813533 * 2
def baseEnd_1813533 : Nat := 206936469286746283888271

theorem tailTrace_1813533 : CollatzResearch.WordTrace tailWord_1813533 prefixEnd_1813533 206936469286746283888271 := by
  unfold tailWord_1813533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66144982538887142622901253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44096655025924761748600835 66144982538887142622901253)
  ·
    refine ⟨12402184226041339241793985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66144982538887142622901253 12402184226041339241793985)
    ·
      refine ⟨9301638169531004431345489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12402184226041339241793985 9301638169531004431345489)
      ·
        refine ⟨6976228627148253323509117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9301638169531004431345489 6976228627148253323509117)
        ·
          refine ⟨2616085735180594996315919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6976228627148253323509117 2616085735180594996315919)
          ·
            refine ⟨3924128602770892494473879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616085735180594996315919 3924128602770892494473879)
            ·
              refine ⟨5886192904156338741710819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924128602770892494473879 5886192904156338741710819)
              ·
                refine ⟨8829289356234508112566229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886192904156338741710819 8829289356234508112566229)
                ·
                  refine ⟨206936469286746283888271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8829289356234508112566229 206936469286746283888271)
                  ·
                    rfl

theorem cell22_1813533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_1813533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813533 prefixEnd_1813533 := by exact prefixLift 1813533
  have htrace : WordTrace (prefixWord ++ tailWord_1813533) baseStart_1813533 baseEnd_1813533 := by
    simpa [prefixWord, tailWord_1813533, baseEnd_1813533] using wordTrace_append hprefix tailTrace_1813533
  have hstable : (prefixWord ++ tailWord_1813533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813533).length < 2 ^ (prefixWord ++ tailWord_1813533).sum := by decide
  have hdescent : baseEnd_1813533 < baseStart_1813533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813550 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_1813550 : Nat := 118140960795 + 1813550 * 2 ^ 59
def prefixEnd_1813550 : Nat := 4983230072969 + 3 ^ 40 * 1813550 * 2
def baseEnd_1813550 : Nat := 206938409102552157996587

theorem tailTrace_1813550 : CollatzResearch.WordTrace tailWord_1813550 prefixEnd_1813550 206938409102552157996587 := by
  unfold tailWord_1813550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8268200322478194315783763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44097068386550369684180069 8268200322478194315783763)
  ·
    refine ⟨12402300483717291473675645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8268200322478194315783763 12402300483717291473675645)
    ·
      refine ⟨4650862681393984302628367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12402300483717291473675645 4650862681393984302628367)
      ·
        refine ⟨6976294022090976453942551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650862681393984302628367 6976294022090976453942551)
        ·
          refine ⟨10464441033136464680913827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976294022090976453942551 10464441033136464680913827)
          ·
            refine ⟨15696661549704697021370741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10464441033136464680913827 15696661549704697021370741)
            ·
              refine ⟨1471562020284815345753507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15696661549704697021370741 1471562020284815345753507)
              ·
                refine ⟨2207343030427223018630261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471562020284815345753507 2207343030427223018630261)
                ·
                  refine ⟨206938409102552157996587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2207343030427223018630261 206938409102552157996587)
                  ·
                    rfl

theorem cell22_1813550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_1813550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813550 prefixEnd_1813550 := by exact prefixLift 1813550
  have htrace : WordTrace (prefixWord ++ tailWord_1813550) baseStart_1813550 baseEnd_1813550 := by
    simpa [prefixWord, tailWord_1813550, baseEnd_1813550] using wordTrace_append hprefix tailTrace_1813550
  have hstable : (prefixWord ++ tailWord_1813550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813550).length < 2 ^ (prefixWord ++ tailWord_1813550).sum := by decide
  have hdescent : baseEnd_1813550 < baseStart_1813550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813576 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_1813576 : Nat := 118140960795 + 1813576 * 2 ^ 59
def prefixEnd_1813576 : Nat := 4983230072969 + 3 ^ 40 * 1813576 * 2
def baseEnd_1813576 : Nat := 620824127639001072839681

theorem tailTrace_1813576 : CollatzResearch.WordTrace tailWord_1813576 prefixEnd_1813576 620824127639001072839681 := by
  unfold tailWord_1813576
  simp only [CollatzResearch.WordTrace]
  refine ⟨33073275438865680483358291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44097700585154240644477721 33073275438865680483358291)
  ·
    refine ⟨49609913158298520725037437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33073275438865680483358291 49609913158298520725037437)
    ·
      refine ⟨18603717434361945271889039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49609913158298520725037437 18603717434361945271889039)
      ·
        refine ⟨27905576151542917907833559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18603717434361945271889039 27905576151542917907833559)
        ·
          refine ⟨41858364227314376861750339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27905576151542917907833559 41858364227314376861750339)
          ·
            refine ⟨62787546340971565292625509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41858364227314376861750339 62787546340971565292625509)
            ·
              refine ⟨11772664938932168492367283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62787546340971565292625509 11772664938932168492367283)
              ·
                refine ⟨17658997408398252738550925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11772664938932168492367283 17658997408398252738550925)
                ·
                  refine ⟨6622124028149344776956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17658997408398252738550925 6622124028149344776956597)
                  ·
                    refine ⟨620824127639001072839681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6622124028149344776956597 620824127639001072839681)
                    ·
                      rfl

theorem cell22_1813576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_1813576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813576 prefixEnd_1813576 := by exact prefixLift 1813576
  have htrace : WordTrace (prefixWord ++ tailWord_1813576) baseStart_1813576 baseEnd_1813576 := by
    simpa [prefixWord, tailWord_1813576, baseEnd_1813576] using wordTrace_append hprefix tailTrace_1813576
  have hstable : (prefixWord ++ tailWord_1813576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813576).length < 2 ^ (prefixWord ++ tailWord_1813576).sum := by decide
  have hdescent : baseEnd_1813576 < baseStart_1813576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813625 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_1813625 : Nat := 118140960795 + 1813625 * 2 ^ 59
def prefixEnd_1813625 : Nat := 4983230072969 + 3 ^ 40 * 1813625 * 2
def baseEnd_1813625 : Nat := 620840901340381278364531

theorem tailTrace_1813625 : CollatzResearch.WordTrace tailWord_1813625 prefixEnd_1813625 620840901340381278364531 := by
  unfold tailWord_1813625
  simp only [CollatzResearch.WordTrace]
  refine ⟨66148338054553842335250329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44098892036369228223500219 66148338054553842335250329)
  ·
    refine ⟨49611253540915381751437747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66148338054553842335250329 49611253540915381751437747)
    ·
      refine ⟨74416880311373072627156621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49611253540915381751437747 74416880311373072627156621)
      ·
        refine ⟨27906330116764902235183733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74416880311373072627156621 27906330116764902235183733)
        ·
          refine ⟨2616218448446709584548475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27906330116764902235183733 2616218448446709584548475)
          ·
            refine ⟨3924327672670064376822713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616218448446709584548475 3924327672670064376822713)
            ·
              refine ⟨2943245754502548282617035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924327672670064376822713 2943245754502548282617035)
              ·
                refine ⟨4414868631753822423925553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943245754502548282617035 4414868631753822423925553)
                ·
                  refine ⟨3311151473815366817944165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414868631753822423925553 3311151473815366817944165)
                  ·
                    refine ⟨620840901340381278364531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311151473815366817944165 620840901340381278364531)
                    ·
                      rfl

theorem cell22_1813625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_1813625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813625 prefixEnd_1813625 := by exact prefixLift 1813625
  have htrace : WordTrace (prefixWord ++ tailWord_1813625) baseStart_1813625 baseEnd_1813625 := by
    simpa [prefixWord, tailWord_1813625, baseEnd_1813625] using wordTrace_append hprefix tailTrace_1813625
  have hstable : (prefixWord ++ tailWord_1813625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813625).length < 2 ^ (prefixWord ++ tailWord_1813625).sum := by decide
  have hdescent : baseEnd_1813625 < baseStart_1813625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813651 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 7]
def baseStart_1813651 : Nat := 118140960795 + 1813651 * 2 ^ 59
def prefixEnd_1813651 : Nat := 4983230072969 + 3 ^ 40 * 1813651 * 2
def baseEnd_1813651 : Nat := 206949933890575292404817

theorem tailTrace_1813651 : CollatzResearch.WordTrace tailWord_1813651 prefixEnd_1813651 206949933890575292404817 := by
  unfold tailWord_1813651
  simp only [CollatzResearch.WordTrace]
  refine ⟨66149286352459648775696807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44099524234973099183797871 66149286352459648775696807)
  ·
    refine ⟨99223929528689473163545211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66149286352459648775696807 99223929528689473163545211)
    ·
      refine ⟨148835894293034209745317817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99223929528689473163545211 148835894293034209745317817)
      ·
        refine ⟨111626920719775657308988363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148835894293034209745317817 111626920719775657308988363)
        ·
          refine ⟨167440381079663485963482545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111626920719775657308988363 167440381079663485963482545)
          ·
            refine ⟨125580285809747614472611909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167440381079663485963482545 125580285809747614472611909)
            ·
              refine ⟨23546303589327677713614733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125580285809747614472611909 23546303589327677713614733)
              ·
                refine ⟨8829863845997879142605525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23546303589327677713614733 8829863845997879142605525)
                ·
                  refine ⟨206949933890575292404817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8829863845997879142605525 206949933890575292404817)
                  ·
                    rfl

theorem cell22_1813651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_1813651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813651 prefixEnd_1813651 := by exact prefixLift 1813651
  have htrace : WordTrace (prefixWord ++ tailWord_1813651) baseStart_1813651 baseEnd_1813651 := by
    simpa [prefixWord, tailWord_1813651, baseEnd_1813651] using wordTrace_append hprefix tailTrace_1813651
  have hstable : (prefixWord ++ tailWord_1813651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813651).length < 2 ^ (prefixWord ++ tailWord_1813651).sum := by decide
  have hdescent : baseEnd_1813651 < baseStart_1813651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813747 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 4]
def baseStart_1813747 : Nat := 118140960795 + 1813747 * 2 ^ 59
def prefixEnd_1813747 : Nat := 4983230072969 + 3 ^ 40 * 1813747 * 2
def baseEnd_1813747 : Nat := 206960888144537875604719

theorem tailTrace_1813747 : CollatzResearch.WordTrace tailWord_1813747 prefixEnd_1813747 206960888144537875604719 := by
  unfold tailWord_1813747
  simp only [CollatzResearch.WordTrace]
  refine ⟨66152787760111857171191495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44101858506741238114127663 66152787760111857171191495)
  ·
    refine ⟨99229181640167785756787243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66152787760111857171191495 99229181640167785756787243)
    ·
      refine ⟨148843772460251678635180865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99229181640167785756787243 148843772460251678635180865)
      ·
        refine ⟨111632829345188758976385649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148843772460251678635180865 111632829345188758976385649)
        ·
          refine ⟨83724622008891569232289237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111632829345188758976385649 83724622008891569232289237)
          ·
            refine ⟨1962295828333396153881779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83724622008891569232289237 1962295828333396153881779)
            ·
              refine ⟨2943443742500094230822669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962295828333396153881779 2943443742500094230822669)
              ·
                refine ⟨1103791403437535336558501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2943443742500094230822669 1103791403437535336558501)
                ·
                  refine ⟨206960888144537875604719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103791403437535336558501 206960888144537875604719)
                  ·
                    rfl

theorem cell22_1813747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 4].length) (baseStart_1813747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813747 prefixEnd_1813747 := by exact prefixLift 1813747
  have htrace : WordTrace (prefixWord ++ tailWord_1813747) baseStart_1813747 baseEnd_1813747 := by
    simpa [prefixWord, tailWord_1813747, baseEnd_1813747] using wordTrace_append hprefix tailTrace_1813747
  have hstable : (prefixWord ++ tailWord_1813747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813747).length < 2 ^ (prefixWord ++ tailWord_1813747).sum := by decide
  have hdescent : baseEnd_1813747 < baseStart_1813747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813764 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 4]
def baseStart_1813764 : Nat := 118140960795 + 1813764 * 2 ^ 59
def prefixEnd_1813764 : Nat := 4983230072969 + 3 ^ 40 * 1813764 * 2
def baseEnd_1813764 : Nat := 206962827960343749713035

theorem tailTrace_1813764 : CollatzResearch.WordTrace tailWord_1813764 prefixEnd_1813764 206962827960343749713035 := by
  unfold tailWord_1813764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33076703900525134537280173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44102271867366846049706897 33076703900525134537280173)
  ·
    refine ⟨12403763962696925451480065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33076703900525134537280173 12403763962696925451480065)
    ·
      refine ⟨9302822972022694088610049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12403763962696925451480065 9302822972022694088610049)
      ·
        refine ⟨6977117229017020566457537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9302822972022694088610049 6977117229017020566457537)
        ·
          refine ⟨5232837921762765424843153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6977117229017020566457537 5232837921762765424843153)
          ·
            refine ⟨3924628441322074068632365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5232837921762765424843153 3924628441322074068632365)
            ·
              refine ⟨1471735665495777775737137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3924628441322074068632365 1471735665495777775737137)
              ·
                refine ⟨1103801749121833331802853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471735665495777775737137 1103801749121833331802853)
                ·
                  refine ⟨206962827960343749713035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103801749121833331802853 206962827960343749713035)
                  ·
                    rfl

theorem cell22_1813764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_1813764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813764 prefixEnd_1813764 := by exact prefixLift 1813764
  have htrace : WordTrace (prefixWord ++ tailWord_1813764) baseStart_1813764 baseEnd_1813764 := by
    simpa [prefixWord, tailWord_1813764, baseEnd_1813764] using wordTrace_append hprefix tailTrace_1813764
  have hstable : (prefixWord ++ tailWord_1813764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813764).length < 2 ^ (prefixWord ++ tailWord_1813764).sum := by decide
  have hdescent : baseEnd_1813764 < baseStart_1813764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813807 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 1, 3]
def baseStart_1813807 : Nat := 118140960795 + 1813807 * 2 ^ 59
def prefixEnd_1813807 : Nat := 4983230072969 + 3 ^ 40 * 1813807 * 2
def baseEnd_1813807 : Nat := 620903203659793470313973

theorem tailTrace_1813807 : CollatzResearch.WordTrace tailWord_1813807 prefixEnd_1813807 620903203659793470313973 := by
  unfold tailWord_1813807
  simp only [CollatzResearch.WordTrace]
  refine ⟨66154976139894487418375675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44103317426596324945583783 66154976139894487418375675)
  ·
    refine ⟨99232464209841731127563513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66154976139894487418375675 99232464209841731127563513)
    ·
      refine ⟨74424348157381298345672635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99232464209841731127563513 74424348157381298345672635)
      ·
        refine ⟨111636522236071947518508953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74424348157381298345672635 111636522236071947518508953)
        ·
          refine ⟨83727391677053960638881715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111636522236071947518508953 83727391677053960638881715)
          ·
            refine ⟨125591087515580940958322573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83727391677053960638881715 125591087515580940958322573)
            ·
              refine ⟨47096657818342852859370965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125591087515580940958322573 47096657818342852859370965)
              ·
                refine ⟨1103827917617410613891507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47096657818342852859370965 1103827917617410613891507)
                ·
                  refine ⟨1655741876426115920837261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103827917617410613891507 1655741876426115920837261)
                  ·
                    refine ⟨620903203659793470313973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655741876426115920837261 620903203659793470313973)
                    ·
                      rfl

theorem cell22_1813807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_1813807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813807 prefixEnd_1813807 := by exact prefixLift 1813807
  have htrace : WordTrace (prefixWord ++ tailWord_1813807) baseStart_1813807 baseEnd_1813807 := by
    simpa [prefixWord, tailWord_1813807, baseEnd_1813807] using wordTrace_append hprefix tailTrace_1813807
  have hstable : (prefixWord ++ tailWord_1813807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813807).length < 2 ^ (prefixWord ++ tailWord_1813807).sum := by decide
  have hdescent : baseEnd_1813807 < baseStart_1813807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813820 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_1813820 : Nat := 118140960795 + 1813820 * 2 ^ 59
def prefixEnd_1813820 : Nat := 4983230072969 + 3 ^ 40 * 1813820 * 2
def baseEnd_1813820 : Nat := 206969217941821923246311

theorem tailTrace_1813820 : CollatzResearch.WordTrace tailWord_1813820 prefixEnd_1813820 206969217941821923246311 := by
  unfold tailWord_1813820
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077725144423695319299457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44103633525898260425732609 33077725144423695319299457)
  ·
    refine ⟨24808293858317771489474593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33077725144423695319299457 24808293858317771489474593)
    ·
      refine ⟨18606220393738328617105945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24808293858317771489474593 18606220393738328617105945)
      ·
        refine ⟨13954665295303746462829459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18606220393738328617105945 13954665295303746462829459)
        ·
          refine ⟨20931997942955619694244189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954665295303746462829459 20931997942955619694244189)
          ·
            refine ⟨7849499228608357385341571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20931997942955619694244189 7849499228608357385341571)
            ·
              refine ⟨11774248842912536078012357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849499228608357385341571 11774248842912536078012357)
              ·
                refine ⟨2207671658046100514627317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11774248842912536078012357 2207671658046100514627317)
                ·
                  refine ⟨206969217941821923246311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2207671658046100514627317 206969217941821923246311)
                  ·
                    rfl

theorem cell22_1813820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_1813820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813820 prefixEnd_1813820 := by exact prefixLift 1813820
  have htrace : WordTrace (prefixWord ++ tailWord_1813820) baseStart_1813820 baseEnd_1813820 := by
    simpa [prefixWord, tailWord_1813820, baseEnd_1813820] using wordTrace_append hprefix tailTrace_1813820
  have hstable : (prefixWord ++ tailWord_1813820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813820).length < 2 ^ (prefixWord ++ tailWord_1813820).sum := by decide
  have hdescent : baseEnd_1813820 < baseStart_1813820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813850 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_1813850 : Nat := 118140960795 + 1813850 * 2 ^ 59
def prefixEnd_1813850 : Nat := 4983230072969 + 3 ^ 40 * 1813850 * 2
def baseEnd_1813850 : Nat := 620917923438555691488841

theorem tailTrace_1813850 : CollatzResearch.WordTrace tailWord_1813850 prefixEnd_1813850 620917923438555691488841 := by
  unfold tailWord_1813850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16539136119684676440547751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44104362985825803841460669 16539136119684676440547751)
  ·
    refine ⟨24808704179527014660821627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16539136119684676440547751 24808704179527014660821627)
    ·
      refine ⟨37213056269290521991232441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24808704179527014660821627 37213056269290521991232441)
      ·
        refine ⟨27909792201967891493424331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37213056269290521991232441 27909792201967891493424331)
        ·
          refine ⟨41864688302951837240136497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27909792201967891493424331 41864688302951837240136497)
          ·
            refine ⟨31398516227213877930102373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41864688302951837240136497 31398516227213877930102373)
            ·
              refine ⟨5887221792602602111894195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31398516227213877930102373 5887221792602602111894195)
              ·
                refine ⟨8830832688903903167841293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887221792602602111894195 8830832688903903167841293)
                ·
                  refine ⟨3311562258338963687940485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830832688903903167841293 3311562258338963687940485)
                  ·
                    refine ⟨620917923438555691488841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311562258338963687940485 620917923438555691488841)
                    ·
                      rfl

theorem cell22_1813850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_1813850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813850 prefixEnd_1813850 := by exact prefixLift 1813850
  have htrace : WordTrace (prefixWord ++ tailWord_1813850) baseStart_1813850 baseEnd_1813850 := by
    simpa [prefixWord, tailWord_1813850, baseEnd_1813850] using wordTrace_append hprefix tailTrace_1813850
  have hstable : (prefixWord ++ tailWord_1813850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813850).length < 2 ^ (prefixWord ++ tailWord_1813850).sum := by decide
  have hdescent : baseEnd_1813850 < baseStart_1813850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813895 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1813895 : Nat := 118140960795 + 1813895 * 2 ^ 59
def prefixEnd_1813895 : Nat := 4983230072969 + 3 ^ 40 * 1813895 * 2
def baseEnd_1813895 : Nat := 620933327858190574113703

theorem tailTrace_1813895 : CollatzResearch.WordTrace tailWord_1813895 prefixEnd_1813895 620933327858190574113703 := by
  unfold tailWord_1813895
  simp only [CollatzResearch.WordTrace]
  refine ⟨66158185763575678447579139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44105457175717118965052759 66158185763575678447579139)
  ·
    refine ⟨99237278645363517671368709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66158185763575678447579139 99237278645363517671368709)
    ·
      refine ⟨18606989746005659563381633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99237278645363517671368709 18606989746005659563381633)
      ·
        refine ⟨13955242309504244672536225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18606989746005659563381633 13955242309504244672536225)
        ·
          refine ⟨10466431732128183504402169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13955242309504244672536225 10466431732128183504402169)
          ·
            refine ⟨7849823799096137628301627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10466431732128183504402169 7849823799096137628301627)
            ·
              refine ⟨11774735698644206442452441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849823799096137628301627 11774735698644206442452441)
              ·
                refine ⟨8831051773983154831839331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774735698644206442452441 8831051773983154831839331)
                ·
                  refine ⟨13246577660974732247758997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8831051773983154831839331 13246577660974732247758997)
                  ·
                    refine ⟨620933327858190574113703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13246577660974732247758997 620933327858190574113703)
                    ·
                      rfl

theorem cell22_1813895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1813895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813895 prefixEnd_1813895 := by exact prefixLift 1813895
  have htrace : WordTrace (prefixWord ++ tailWord_1813895) baseStart_1813895 baseEnd_1813895 := by
    simpa [prefixWord, tailWord_1813895, baseEnd_1813895] using wordTrace_append hprefix tailTrace_1813895
  have hstable : (prefixWord ++ tailWord_1813895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813895).length < 2 ^ (prefixWord ++ tailWord_1813895).sum := by decide
  have hdescent : baseEnd_1813895 < baseStart_1813895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813948 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_1813948 : Nat := 118140960795 + 1813948 * 2 ^ 59
def prefixEnd_1813948 : Nat := 4983230072969 + 3 ^ 40 * 1813948 * 2
def baseEnd_1813948 : Nat := 620951470841316102538541

theorem tailTrace_1813948 : CollatzResearch.WordTrace tailWord_1813948 prefixEnd_1813948 620951470841316102538541 := by
  unfold tailWord_1813948
  simp only [CollatzResearch.WordTrace]
  refine ⟨33080059416191834249629249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44106745888255778999505665 33080059416191834249629249)
  ·
    refine ⟨24810044562143875687221937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33080059416191834249629249 24810044562143875687221937)
    ·
      refine ⟨18607533421607906765416453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24810044562143875687221937 18607533421607906765416453)
      ·
        refine ⟨3488912516551482518515585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18607533421607906765416453 3488912516551482518515585)
        ·
          refine ⟨2616684387413611888886689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488912516551482518515585 2616684387413611888886689)
          ·
            refine ⟨1962513290560208916665017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616684387413611888886689 1962513290560208916665017)
            ·
              refine ⟨1471884967920156687498763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962513290560208916665017 1471884967920156687498763)
              ·
                refine ⟨2207827451880235031248145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471884967920156687498763 2207827451880235031248145)
                ·
                  refine ⟨1655870588910176273436109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2207827451880235031248145 1655870588910176273436109)
                  ·
                    refine ⟨620951470841316102538541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655870588910176273436109 620951470841316102538541)
                    ·
                      rfl

theorem cell22_1813948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_1813948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813948 prefixEnd_1813948 := by exact prefixLift 1813948
  have htrace : WordTrace (prefixWord ++ tailWord_1813948) baseStart_1813948 baseEnd_1813948 := by
    simpa [prefixWord, tailWord_1813948, baseEnd_1813948] using wordTrace_append hprefix tailTrace_1813948
  have hstable : (prefixWord ++ tailWord_1813948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813948).length < 2 ^ (prefixWord ++ tailWord_1813948).sum := by decide
  have hdescent : baseEnd_1813948 < baseStart_1813948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813989 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 5]
def baseStart_1813989 : Nat := 118140960795 + 1813989 * 2 ^ 59
def prefixEnd_1813989 : Nat := 4983230072969 + 3 ^ 40 * 1813989 * 2
def baseEnd_1813989 : Nat := 206988501993068554087805

theorem tailTrace_1813989 : CollatzResearch.WordTrace tailWord_1813989 prefixEnd_1813989 206988501993068554087805 := by
  unfold tailWord_1813989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66161614225235132501501021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44107742816823421667667347 66161614225235132501501021)
  ·
    refine ⟨24810605334463174688062883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66161614225235132501501021 24810605334463174688062883)
    ·
      refine ⟨37215908001694762032094325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24810605334463174688062883 37215908001694762032094325)
      ·
        refine ⟨3488991375158883940508843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37215908001694762032094325 3488991375158883940508843)
        ·
          refine ⟨5233487062738325910763265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488991375158883940508843 5233487062738325910763265)
          ·
            refine ⟨3925115297053744433072449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233487062738325910763265 3925115297053744433072449)
            ·
              refine ⟨2943836472790308324804337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925115297053744433072449 2943836472790308324804337)
              ·
                refine ⟨2207877354592731243603253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943836472790308324804337 2207877354592731243603253)
                ·
                  refine ⟨206988501993068554087805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2207877354592731243603253 206988501993068554087805)
                  ·
                    rfl

theorem cell22_1813989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_1813989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1813989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1813989 prefixEnd_1813989 := by exact prefixLift 1813989
  have htrace : WordTrace (prefixWord ++ tailWord_1813989) baseStart_1813989 baseEnd_1813989 := by
    simpa [prefixWord, tailWord_1813989, baseEnd_1813989] using wordTrace_append hprefix tailTrace_1813989
  have hstable : (prefixWord ++ tailWord_1813989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813989).length < 2 ^ (prefixWord ++ tailWord_1813989).sum := by decide
  have hdescent : baseEnd_1813989 < baseStart_1813989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814047 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 2, 4]
def baseStart_1814047 : Nat := 118140960795 + 1814047 * 2 ^ 59
def prefixEnd_1814047 : Nat := 4983230072969 + 3 ^ 40 * 1814047 * 2
def baseEnd_1814047 : Nat := 620985360564512844313237

theorem tailTrace_1814047 : CollatzResearch.WordTrace tailWord_1814047 prefixEnd_1814047 620985360564512844313237 := by
  unfold tailWord_1814047
  simp only [CollatzResearch.WordTrace]
  refine ⟨66163729659025008407112395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44109153106016672271408263 66163729659025008407112395)
  ·
    refine ⟨99245594488537512610668593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66163729659025008407112395 99245594488537512610668593)
    ·
      refine ⟨74434195866403134458001445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99245594488537512610668593 74434195866403134458001445)
      ·
        refine ⟨13956411724950587710875271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74434195866403134458001445 13956411724950587710875271)
        ·
          refine ⟨20934617587425881566312907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13956411724950587710875271 20934617587425881566312907)
          ·
            refine ⟨31401926381138822349469361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20934617587425881566312907 31401926381138822349469361)
            ·
              refine ⟨23551444785854116762102021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31401926381138822349469361 23551444785854116762102021)
              ·
                refine ⟨4415895897347646892894129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23551444785854116762102021 4415895897347646892894129)
                ·
                  refine ⟨3311921923010735169670597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415895897347646892894129 3311921923010735169670597)
                  ·
                    refine ⟨620985360564512844313237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311921923010735169670597 620985360564512844313237)
                    ·
                      rfl

theorem cell22_1814047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_1814047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814047 prefixEnd_1814047 := by exact prefixLift 1814047
  have htrace : WordTrace (prefixWord ++ tailWord_1814047) baseStart_1814047 baseEnd_1814047 := by
    simpa [prefixWord, tailWord_1814047, baseEnd_1814047] using wordTrace_append hprefix tailTrace_1814047
  have hstable : (prefixWord ++ tailWord_1814047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814047).length < 2 ^ (prefixWord ++ tailWord_1814047).sum := by decide
  have hdescent : baseEnd_1814047 < baseStart_1814047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814049 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1814049 : Nat := 118140960795 + 1814049 * 2 ^ 59
def prefixEnd_1814049 : Nat := 4983230072969 + 3 ^ 40 * 1814049 * 2
def baseEnd_1814049 : Nat := 620986045205385505763231

theorem tailTrace_1814049 : CollatzResearch.WordTrace tailWord_1814049 prefixEnd_1814049 620986045205385505763231 := by
  unfold tailWord_1814049
  simp only [CollatzResearch.WordTrace]
  refine ⟨66163802605017762748685201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44109201736678508499123467 66163802605017762748685201)
  ·
    refine ⟨49622851953763322061513901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66163802605017762748685201 49622851953763322061513901)
    ·
      refine ⟨18608569482661245773067713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49622851953763322061513901 18608569482661245773067713)
      ·
        refine ⟨13956427111995934329800785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18608569482661245773067713 13956427111995934329800785)
        ·
          refine ⟨10467320333996950747350589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13956427111995934329800785 10467320333996950747350589)
          ·
            refine ⟨3925245125248856530256471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10467320333996950747350589 3925245125248856530256471)
            ·
              refine ⟨5887867687873284795384707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925245125248856530256471 5887867687873284795384707)
              ·
                refine ⟨8831801531809927193077061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887867687873284795384707 8831801531809927193077061)
                ·
                  refine ⟨1655962787214361348701949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8831801531809927193077061 1655962787214361348701949)
                  ·
                    refine ⟨620986045205385505763231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1655962787214361348701949 620986045205385505763231)
                    ·
                      rfl

theorem cell22_1814049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1814049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814049 prefixEnd_1814049 := by exact prefixLift 1814049
  have htrace : WordTrace (prefixWord ++ tailWord_1814049) baseStart_1814049 baseEnd_1814049 := by
    simpa [prefixWord, tailWord_1814049, baseEnd_1814049] using wordTrace_append hprefix tailTrace_1814049
  have hstable : (prefixWord ++ tailWord_1814049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814049).length < 2 ^ (prefixWord ++ tailWord_1814049).sum := by decide
  have hdescent : baseEnd_1814049 < baseStart_1814049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814079 : List Nat := [1, 1, 2, 2, 3, 5, 2, 6]
def baseStart_1814079 : Nat := 118140960795 + 1814079 * 2 ^ 59
def prefixEnd_1814079 : Nat := 4983230072969 + 3 ^ 40 * 1814079 * 2
def baseEnd_1814079 : Nat := 68999590535386158612571

theorem tailTrace_1814079 : CollatzResearch.WordTrace tailWord_1814079 prefixEnd_1814079 68999590535386158612571 := by
  unfold tailWord_1814079
  simp only [CollatzResearch.WordTrace]
  refine ⟨66164896794909077872277291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44109931196606051914851527 66164896794909077872277291)
  ·
    refine ⟨99247345192363616808415937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66164896794909077872277291 99247345192363616808415937)
    ·
      refine ⟨74435508894272712606311953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99247345192363616808415937 74435508894272712606311953)
      ·
        refine ⟨55826631670704534454733965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74435508894272712606311953 55826631670704534454733965)
        ·
          refine ⟨20934986876514200420525237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55826631670704534454733965 20934986876514200420525237)
          ·
            refine ⟨1962655019673206289424241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20934986876514200420525237 1962655019673206289424241)
            ·
              refine ⟨1471991264754904717068181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962655019673206289424241 1471991264754904717068181)
              ·
                refine ⟨68999590535386158612571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1471991264754904717068181 68999590535386158612571)
                ·
                  rfl

theorem cell22_1814079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 6].length) (baseStart_1814079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814079 prefixEnd_1814079 := by exact prefixLift 1814079
  have htrace : WordTrace (prefixWord ++ tailWord_1814079) baseStart_1814079 baseEnd_1814079 := by
    simpa [prefixWord, tailWord_1814079, baseEnd_1814079] using wordTrace_append hprefix tailTrace_1814079
  have hstable : (prefixWord ++ tailWord_1814079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814079).length < 2 ^ (prefixWord ++ tailWord_1814079).sum := by decide
  have hdescent : baseEnd_1814079 < baseStart_1814079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814102 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1814102 : Nat := 118140960795 + 1814102 * 2 ^ 59
def prefixEnd_1814102 : Nat := 4983230072969 + 3 ^ 40 * 1814102 * 2
def baseEnd_1814102 : Nat := 207001396062837011396023

theorem tailTrace_1814102 : CollatzResearch.WordTrace tailWord_1814102 prefixEnd_1814102 207001396062837011396023 := by
  unfold tailWord_1814102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135358479614109550022785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44110490449217168533576373 4135358479614109550022785)
  ·
    refine ⟨3101518859710582162517089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4135358479614109550022785 3101518859710582162517089)
    ·
      refine ⟨2326139144782936621887817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3101518859710582162517089 2326139144782936621887817)
      ·
        refine ⟨1744604358587202466415863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326139144782936621887817 1744604358587202466415863)
        ·
          refine ⟨2616906537880803699623795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744604358587202466415863 2616906537880803699623795)
          ·
            refine ⟨3925359806821205549435693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616906537880803699623795 3925359806821205549435693)
            ·
              refine ⟨1472009927557952081038385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3925359806821205549435693 1472009927557952081038385)
              ·
                refine ⟨1104007445668464060778789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472009927557952081038385 1104007445668464060778789)
                ·
                  refine ⟨207001396062837011396023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104007445668464060778789 207001396062837011396023)
                  ·
                    rfl

theorem cell22_1814102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1814102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814102 prefixEnd_1814102 := by exact prefixLift 1814102
  have htrace : WordTrace (prefixWord ++ tailWord_1814102) baseStart_1814102 baseEnd_1814102 := by
    simpa [prefixWord, tailWord_1814102, baseEnd_1814102] using wordTrace_append hprefix tailTrace_1814102
  have hstable : (prefixWord ++ tailWord_1814102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814102).length < 2 ^ (prefixWord ++ tailWord_1814102).sum := by decide
  have hdescent : baseEnd_1814102 < baseStart_1814102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814162 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1814162 : Nat := 118140960795 + 1814162 * 2 ^ 59
def prefixEnd_1814162 : Nat := 4983230072969 + 3 ^ 40 * 1814162 * 2
def baseEnd_1814162 : Nat := 621024727414690877687885

theorem tailTrace_1814162 : CollatzResearch.WordTrace tailWord_1814162 prefixEnd_1814162 621024727414690877687885 := by
  unfold tailWord_1814162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16541981013402095761887185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44111949369072255365032493 16541981013402095761887185)
  ·
    refine ⟨12406485760051571821415389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16541981013402095761887185 12406485760051571821415389)
    ·
      refine ⟨4652432160019339433030771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12406485760051571821415389 4652432160019339433030771)
      ·
        refine ⟨6978648240029009149546157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652432160019339433030771 6978648240029009149546157)
        ·
          refine ⟨2616993090010878431079809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6978648240029009149546157 2616993090010878431079809)
          ·
            refine ⟨1962744817508158823309857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616993090010878431079809 1962744817508158823309857)
            ·
              refine ⟨1472058613131119117482393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962744817508158823309857 1472058613131119117482393)
              ·
                refine ⟨1104043959848339338111795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472058613131119117482393 1104043959848339338111795)
                ·
                  refine ⟨1656065939772509007167693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104043959848339338111795 1656065939772509007167693)
                  ·
                    refine ⟨621024727414690877687885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1656065939772509007167693 621024727414690877687885)
                    ·
                      rfl

theorem cell22_1814162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1814162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814162 prefixEnd_1814162 := by exact prefixLift 1814162
  have htrace : WordTrace (prefixWord ++ tailWord_1814162) baseStart_1814162 baseEnd_1814162 := by
    simpa [prefixWord, tailWord_1814162, baseEnd_1814162] using wordTrace_append hprefix tailTrace_1814162
  have hstable : (prefixWord ++ tailWord_1814162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814162).length < 2 ^ (prefixWord ++ tailWord_1814162).sum := by decide
  have hdescent : baseEnd_1814162 < baseStart_1814162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814199 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1814199 : Nat := 118140960795 + 1814199 * 2 ^ 59
def prefixEnd_1814199 : Nat := 4983230072969 + 3 ^ 40 * 1814199 * 2
def baseEnd_1814199 : Nat := 621037393270835114512771

theorem tailTrace_1814199 : CollatzResearch.WordTrace tailWord_1814199 prefixEnd_1814199 621037393270835114512771 := by
  unfold tailWord_1814199
  simp only [CollatzResearch.WordTrace]
  refine ⟨66169273554474338366645651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44112849036316225577763767 66169273554474338366645651)
  ·
    refine ⟨99253910331711507549968477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66169273554474338366645651 99253910331711507549968477)
    ·
      refine ⟨37220216374391815331238179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99253910331711507549968477 37220216374391815331238179)
      ·
        refine ⟨55830324561587722996857269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37220216374391815331238179 55830324561587722996857269)
        ·
          refine ⟨5234092927648849030955369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55830324561587722996857269 5234092927648849030955369)
          ·
            refine ⟨3925569695736636773216527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234092927648849030955369 3925569695736636773216527)
            ·
              refine ⟨5888354543604955159824791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925569695736636773216527 5888354543604955159824791)
              ·
                refine ⟨8832531815407432739737187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888354543604955159824791 8832531815407432739737187)
                ·
                  refine ⟨13248797723111149109605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832531815407432739737187 13248797723111149109605781)
                  ·
                    refine ⟨621037393270835114512771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13248797723111149109605781 621037393270835114512771)
                    ·
                      rfl

theorem cell22_1814199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1814199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814199 prefixEnd_1814199 := by exact prefixLift 1814199
  have htrace : WordTrace (prefixWord ++ tailWord_1814199) baseStart_1814199 baseEnd_1814199 := by
    simpa [prefixWord, tailWord_1814199, baseEnd_1814199] using wordTrace_append hprefix tailTrace_1814199
  have hstable : (prefixWord ++ tailWord_1814199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814199).length < 2 ^ (prefixWord ++ tailWord_1814199).sum := by decide
  have hdescent : baseEnd_1814199 < baseStart_1814199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814227 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_1814227 : Nat := 118140960795 + 1814227 * 2 ^ 59
def prefixEnd_1814227 : Nat := 4983230072969 + 3 ^ 40 * 1814227 * 2
def baseEnd_1814227 : Nat := 621046978243052374812685

theorem tailTrace_1814227 : CollatzResearch.WordTrace tailWord_1814227 prefixEnd_1814227 621046978243052374812685 := by
  unfold tailWord_1814227
  simp only [CollatzResearch.WordTrace]
  refine ⟨66170294798372899148664935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44113529865581932765776623 66170294798372899148664935)
  ·
    refine ⟨99255442197559348722997403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66170294798372899148664935 99255442197559348722997403)
    ·
      refine ⟨148883163296339023084496105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99255442197559348722997403 148883163296339023084496105)
      ·
        refine ⟨111662372472254267313372079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148883163296339023084496105 111662372472254267313372079)
        ·
          refine ⟨167493558708381400970058119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111662372472254267313372079 167493558708381400970058119)
          ·
            refine ⟨251240338062572101455087179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167493558708381400970058119 251240338062572101455087179)
            ·
              refine ⟨376860507093858152182630769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251240338062572101455087179 376860507093858152182630769)
              ·
                refine ⟨282645380320393614136973077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376860507093858152182630769 282645380320393614136973077)
                ·
                  refine ⟨13249002202518450662670613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282645380320393614136973077 13249002202518450662670613)
                  ·
                    refine ⟨621046978243052374812685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13249002202518450662670613 621046978243052374812685)
                    ·
                      rfl

theorem cell22_1814227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_1814227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814227 prefixEnd_1814227 := by exact prefixLift 1814227
  have htrace : WordTrace (prefixWord ++ tailWord_1814227) baseStart_1814227 baseEnd_1814227 := by
    simpa [prefixWord, tailWord_1814227, baseEnd_1814227] using wordTrace_append hprefix tailTrace_1814227
  have hstable : (prefixWord ++ tailWord_1814227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814227).length < 2 ^ (prefixWord ++ tailWord_1814227).sum := by decide
  have hdescent : baseEnd_1814227 < baseStart_1814227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814263 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 1, 3]
def baseStart_1814263 : Nat := 118140960795 + 1814263 * 2 ^ 59
def prefixEnd_1814263 : Nat := 4983230072969 + 3 ^ 40 * 1814263 * 2
def baseEnd_1814263 : Nat := 621059301778760280912575

theorem tailTrace_1814263 : CollatzResearch.WordTrace tailWord_1814263 prefixEnd_1814263 621059301778760280912575 := by
  unfold tailWord_1814263
  simp only [CollatzResearch.WordTrace]
  refine ⟨66171607826242477296975443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44114405217494984864650295 66171607826242477296975443)
  ·
    refine ⟨99257411739363715945463165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66171607826242477296975443 99257411739363715945463165)
    ·
      refine ⟨37221529402261393479548687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99257411739363715945463165 37221529402261393479548687)
      ·
        refine ⟨55832294103392090219323031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37221529402261393479548687 55832294103392090219323031)
        ·
          refine ⟨83748441155088135328984547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55832294103392090219323031 83748441155088135328984547)
          ·
            refine ⟨125622661732632202993476821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83748441155088135328984547 125622661732632202993476821)
            ·
              refine ⟨2944281134358567257659613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125622661732632202993476821 2944281134358567257659613)
              ·
                refine ⟨1104105425384462721622355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2944281134358567257659613 1104105425384462721622355)
                ·
                  refine ⟨1656158138076694082433533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104105425384462721622355 1656158138076694082433533)
                  ·
                    refine ⟨621059301778760280912575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1656158138076694082433533 621059301778760280912575)
                    ·
                      rfl

theorem cell22_1814263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_1814263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814263 prefixEnd_1814263 := by exact prefixLift 1814263
  have htrace : WordTrace (prefixWord ++ tailWord_1814263) baseStart_1814263 baseEnd_1814263 := by
    simpa [prefixWord, tailWord_1814263, baseEnd_1814263] using wordTrace_append hprefix tailTrace_1814263
  have hstable : (prefixWord ++ tailWord_1814263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814263).length < 2 ^ (prefixWord ++ tailWord_1814263).sum := by decide
  have hdescent : baseEnd_1814263 < baseStart_1814263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814280 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 1, 3]
def baseStart_1814280 : Nat := 118140960795 + 1814280 * 2 ^ 59
def prefixEnd_1814280 : Nat := 4983230072969 + 3 ^ 40 * 1814280 * 2
def baseEnd_1814280 : Nat := 621065121226177903237523

theorem tailTrace_1814280 : CollatzResearch.WordTrace tailWord_1814280 prefixEnd_1814280 621065121226177903237523 := by
  unfold tailWord_1814280
  simp only [CollatzResearch.WordTrace]
  refine ⟨33086113933590444600172147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44114818578120592800229529 33086113933590444600172147)
  ·
    refine ⟨49629170900385666900258221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33086113933590444600172147 49629170900385666900258221)
    ·
      refine ⟨18610939087644625087596833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49629170900385666900258221 18610939087644625087596833)
      ·
        refine ⟨13958204315733468815697625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18610939087644625087596833 13958204315733468815697625)
        ·
          refine ⟨10468653236800101611773219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13958204315733468815697625 10468653236800101611773219)
          ·
            refine ⟨15702979855200152417659829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468653236800101611773219 15702979855200152417659829)
            ·
              refine ⟨1472154361425014289155609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15702979855200152417659829 1472154361425014289155609)
              ·
                refine ⟨1104115771068760716866707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472154361425014289155609 1104115771068760716866707)
                ·
                  refine ⟨1656173656603141075300061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104115771068760716866707 1656173656603141075300061)
                  ·
                    refine ⟨621065121226177903237523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1656173656603141075300061 621065121226177903237523)
                    ·
                      rfl

theorem cell22_1814280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_1814280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814280 prefixEnd_1814280 := by exact prefixLift 1814280
  have htrace : WordTrace (prefixWord ++ tailWord_1814280) baseStart_1814280 baseEnd_1814280 := by
    simpa [prefixWord, tailWord_1814280, baseEnd_1814280] using wordTrace_append hprefix tailTrace_1814280
  have hstable : (prefixWord ++ tailWord_1814280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814280).length < 2 ^ (prefixWord ++ tailWord_1814280).sum := by decide
  have hdescent : baseEnd_1814280 < baseStart_1814280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814289 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1814289 : Nat := 118140960795 + 1814289 * 2 ^ 59
def prefixEnd_1814289 : Nat := 4983230072969 + 3 ^ 40 * 1814289 * 2
def baseEnd_1814289 : Nat := 621068202110104879762495

theorem tailTrace_1814289 : CollatzResearch.WordTrace tailWord_1814289 prefixEnd_1814289 621068202110104879762495 := by
  unfold tailWord_1814289
  simp only [CollatzResearch.WordTrace]
  refine ⟨66172556124148283737421921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44115037416098855824947947 66172556124148283737421921)
  ·
    refine ⟨49629417093111212803066441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66172556124148283737421921 49629417093111212803066441)
    ·
      refine ⟨37222062819833409602299831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49629417093111212803066441 37222062819833409602299831)
      ·
        refine ⟨55833094229750114403449747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37222062819833409602299831 55833094229750114403449747)
        ·
          refine ⟨83749641344625171605174621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55833094229750114403449747 83749641344625171605174621)
          ·
            refine ⟨31406115504234439351940483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83749641344625171605174621 31406115504234439351940483)
            ·
              refine ⟨47109173256351659027910725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31406115504234439351940483 47109173256351659027910725)
              ·
                refine ⟨8832969985565936067733261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47109173256351659027910725 8832969985565936067733261)
                ·
                  refine ⟨3312363744587226025399973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8832969985565936067733261 3312363744587226025399973)
                  ·
                    refine ⟨621068202110104879762495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312363744587226025399973 621068202110104879762495)
                    ·
                      rfl

theorem cell22_1814289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1814289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814289 prefixEnd_1814289 := by exact prefixLift 1814289
  have htrace : WordTrace (prefixWord ++ tailWord_1814289) baseStart_1814289 baseEnd_1814289 := by
    simpa [prefixWord, tailWord_1814289, baseEnd_1814289] using wordTrace_append hprefix tailTrace_1814289
  have hstable : (prefixWord ++ tailWord_1814289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814289).length < 2 ^ (prefixWord ++ tailWord_1814289).sum := by decide
  have hdescent : baseEnd_1814289 < baseStart_1814289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814293 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 5]
def baseStart_1814293 : Nat := 118140960795 + 1814293 * 2 ^ 59
def prefixEnd_1814293 : Nat := 4983230072969 + 3 ^ 40 * 1814293 * 2
def baseEnd_1814293 : Nat := 207023190463950067554161

theorem tailTrace_1814293 : CollatzResearch.WordTrace tailWord_1814293 prefixEnd_1814293 207023190463950067554161 := by
  unfold tailWord_1814293
  simp only [CollatzResearch.WordTrace]
  refine ⟨66172702016133792420567533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44115134677422528280378355 66172702016133792420567533)
  ·
    refine ⟨24814763256050172157712825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66172702016133792420567533 24814763256050172157712825)
    ·
      refine ⟨18611072442037629118284619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24814763256050172157712825 18611072442037629118284619)
      ·
        refine ⟨27916608663056443677426929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18611072442037629118284619 27916608663056443677426929)
        ·
          refine ⟨20937456497292332758070197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27916608663056443677426929 20937456497292332758070197)
          ·
            refine ⟨1962886546621156196069081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20937456497292332758070197 1962886546621156196069081)
            ·
              refine ⟨1472164909965867147051811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962886546621156196069081 1472164909965867147051811)
              ·
                refine ⟨2208247364948800720577717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472164909965867147051811 2208247364948800720577717)
                ·
                  refine ⟨207023190463950067554161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2208247364948800720577717 207023190463950067554161)
                  ·
                    rfl

theorem cell22_1814293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_1814293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814293 prefixEnd_1814293 := by exact prefixLift 1814293
  have htrace : WordTrace (prefixWord ++ tailWord_1814293) baseStart_1814293 baseEnd_1814293 := by
    simpa [prefixWord, tailWord_1814293, baseEnd_1814293] using wordTrace_append hprefix tailTrace_1814293
  have hstable : (prefixWord ++ tailWord_1814293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814293).length < 2 ^ (prefixWord ++ tailWord_1814293).sum := by decide
  have hdescent : baseEnd_1814293 < baseStart_1814293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814304 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_1814304 : Nat := 118140960795 + 1814304 * 2 ^ 59
def prefixEnd_1814304 : Nat := 4983230072969 + 3 ^ 40 * 1814304 * 2
def baseEnd_1814304 : Nat := 207024445638883280212483

theorem tailTrace_1814304 : CollatzResearch.WordTrace tailWord_1814304 prefixEnd_1814304 207024445638883280212483 := by
  unfold tailWord_1814304
  simp only [CollatzResearch.WordTrace]
  refine ⟨33086551609546970649608983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44115402146062627532811977 33086551609546970649608983)
  ·
    refine ⟨49629827414320455974413475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33086551609546970649608983 49629827414320455974413475)
    ·
      refine ⟨74444741121480683961620213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49629827414320455974413475 74444741121480683961620213)
      ·
        refine ⟨6979194480138814121401895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74444741121480683961620213 6979194480138814121401895)
        ·
          refine ⟨10468791720208221182102843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979194480138814121401895 10468791720208221182102843)
          ·
            refine ⟨15703187580312331773154265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468791720208221182102843 15703187580312331773154265)
            ·
              refine ⟨11777390685234248829865699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15703187580312331773154265 11777390685234248829865699)
              ·
                refine ⟨17666086027851373244798549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777390685234248829865699 17666086027851373244798549)
                ·
                  refine ⟨207024445638883280212483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17666086027851373244798549 207024445638883280212483)
                  ·
                    rfl

theorem cell22_1814304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_1814304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814304 prefixEnd_1814304 := by exact prefixLift 1814304
  have htrace : WordTrace (prefixWord ++ tailWord_1814304) baseStart_1814304 baseEnd_1814304 := by
    simpa [prefixWord, tailWord_1814304, baseEnd_1814304] using wordTrace_append hprefix tailTrace_1814304
  have hstable : (prefixWord ++ tailWord_1814304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814304).length < 2 ^ (prefixWord ++ tailWord_1814304).sum := by decide
  have hdescent : baseEnd_1814304 < baseStart_1814304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814306 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1814306 : Nat := 118140960795 + 1814306 * 2 ^ 59
def prefixEnd_1814306 : Nat := 4983230072969 + 3 ^ 40 * 1814306 * 2
def baseEnd_1814306 : Nat := 621074021557522502087443

theorem tailTrace_1814306 : CollatzResearch.WordTrace tailWord_1814306 prefixEnd_1814306 621074021557522502087443 := by
  unfold tailWord_1814306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16543294041271673910197693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44115450776724463760527181 16543294041271673910197693)
  ·
    refine ⟨6203735265476877716324135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16543294041271673910197693 6203735265476877716324135)
    ·
      refine ⟨9305602898215316574486203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6203735265476877716324135 9305602898215316574486203)
      ·
        refine ⟨13958404347322974861729305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9305602898215316574486203 13958404347322974861729305)
        ·
          refine ⟨10468803260492231146296979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13958404347322974861729305 10468803260492231146296979)
          ·
            refine ⟨15703204890738346719445469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468803260492231146296979 15703204890738346719445469)
            ·
              refine ⟨5888701834026880019792051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15703204890738346719445469 5888701834026880019792051)
              ·
                refine ⟨8833052751040320029688077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888701834026880019792051 8833052751040320029688077)
                ·
                  refine ⟨3312394781640120011133029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8833052751040320029688077 3312394781640120011133029)
                  ·
                    refine ⟨621074021557522502087443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312394781640120011133029 621074021557522502087443)
                    ·
                      rfl

theorem cell22_1814306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1814306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814306 prefixEnd_1814306 := by exact prefixLift 1814306
  have htrace : WordTrace (prefixWord ++ tailWord_1814306) baseStart_1814306 baseEnd_1814306 := by
    simpa [prefixWord, tailWord_1814306, baseEnd_1814306] using wordTrace_append hprefix tailTrace_1814306
  have hstable : (prefixWord ++ tailWord_1814306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814306).length < 2 ^ (prefixWord ++ tailWord_1814306).sum := by decide
  have hdescent : baseEnd_1814306 < baseStart_1814306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814319 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 1, 5]
def baseStart_1814319 : Nat := 118140960795 + 1814319 * 2 ^ 59
def prefixEnd_1814319 : Nat := 4983230072969 + 3 ^ 40 * 1814319 * 2
def baseEnd_1814319 : Nat := 621078471723194801512403

theorem tailTrace_1814319 : CollatzResearch.WordTrace tailWord_1814319 prefixEnd_1814319 621078471723194801512403 := by
  unfold tailWord_1814319
  simp only [CollatzResearch.WordTrace]
  refine ⟨66173650314039598861014011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44115766876026399240676007 66173650314039598861014011)
  ·
    refine ⟨99260475471059398291521017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66173650314039598861014011 99260475471059398291521017)
    ·
      refine ⟨74445356603294548718640763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99260475471059398291521017 74445356603294548718640763)
      ·
        refine ⟨111668034904941823077961145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74445356603294548718640763 111668034904941823077961145)
        ·
          refine ⟨83751026178706367308470859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111668034904941823077961145 83751026178706367308470859)
          ·
            refine ⟨125626539268059550962706289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83751026178706367308470859 125626539268059550962706289)
            ·
              refine ⟨94219904451044663222029717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125626539268059550962706289 94219904451044663222029717)
              ·
                refine ⟨4416558021142718588532643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94219904451044663222029717 4416558021142718588532643)
                ·
                  refine ⟨6624837031714077882798965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416558021142718588532643 6624837031714077882798965)
                  ·
                    refine ⟨621078471723194801512403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6624837031714077882798965 621078471723194801512403)
                    ·
                      rfl

theorem cell22_1814319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_1814319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814319 prefixEnd_1814319 := by exact prefixLift 1814319
  have htrace : WordTrace (prefixWord ++ tailWord_1814319) baseStart_1814319 baseEnd_1814319 := by
    simpa [prefixWord, tailWord_1814319, baseEnd_1814319] using wordTrace_append hprefix tailTrace_1814319
  have hstable : (prefixWord ++ tailWord_1814319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814319).length < 2 ^ (prefixWord ++ tailWord_1814319).sum := by decide
  have hdescent : baseEnd_1814319 < baseStart_1814319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814353 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_1814353 : Nat := 118140960795 + 1814353 * 2 ^ 59
def prefixEnd_1814353 : Nat := 4983230072969 + 3 ^ 40 * 1814353 * 2
def baseEnd_1814353 : Nat := 621090110618030046162299

theorem tailTrace_1814353 : CollatzResearch.WordTrace tailWord_1814353 prefixEnd_1814353 621090110618030046162299 := by
  unfold tailWord_1814353
  simp only [CollatzResearch.WordTrace]
  refine ⟨66174890395916422667751713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44116593597277615111834475 66174890395916422667751713)
  ·
    refine ⟨49631167796937317000813785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66174890395916422667751713 49631167796937317000813785)
    ·
      refine ⟨37223375847702987750610339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49631167796937317000813785 37223375847702987750610339)
      ·
        refine ⟨55835063771554481625915509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37223375847702987750610339 55835063771554481625915509)
        ·
          refine ⟨5234537228583232652429579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55835063771554481625915509 5234537228583232652429579)
          ·
            refine ⟨7851805842874848978644369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234537228583232652429579 7851805842874848978644369)
            ·
              refine ⟨5888854382156136733983277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7851805842874848978644369 5888854382156136733983277)
              ·
                refine ⟨2208320393308551275243729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5888854382156136733983277 2208320393308551275243729)
                ·
                  refine ⟨1656240294981413456432797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2208320393308551275243729 1656240294981413456432797)
                  ·
                    refine ⟨621090110618030046162299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1656240294981413456432797 621090110618030046162299)
                    ·
                      rfl

theorem cell22_1814353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_1814353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814353 prefixEnd_1814353 := by exact prefixLift 1814353
  have htrace : WordTrace (prefixWord ++ tailWord_1814353) baseStart_1814353 baseEnd_1814353 := by
    simpa [prefixWord, tailWord_1814353, baseEnd_1814353] using wordTrace_append hprefix tailTrace_1814353
  have hstable : (prefixWord ++ tailWord_1814353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814353).length < 2 ^ (prefixWord ++ tailWord_1814353).sum := by decide
  have hdescent : baseEnd_1814353 < baseStart_1814353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814368 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_1814368 : Nat := 118140960795 + 1814368 * 2 ^ 59
def prefixEnd_1814368 : Nat := 4983230072969 + 3 ^ 40 * 1814368 * 2
def baseEnd_1814368 : Nat := 621095245424575007037253

theorem tailTrace_1814368 : CollatzResearch.WordTrace tailWord_1814368 prefixEnd_1814368 621095245424575007037253 := by
  unfold tailWord_1814368
  simp only [CollatzResearch.WordTrace]
  refine ⟨33087718745431040114773879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44116958327241386819698505 33087718745431040114773879)
  ·
    refine ⟨49631578118146560172160819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33087718745431040114773879 49631578118146560172160819)
    ·
      refine ⟨74447367177219840258241229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49631578118146560172160819 74447367177219840258241229)
      ·
        refine ⟨27917762691457440096840461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74447367177219840258241229 27917762691457440096840461)
        ·
          refine ⟨10469161009296540036315173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27917762691457440096840461 10469161009296540036315173)
          ·
            refine ⟨1962967689243101256809095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10469161009296540036315173 1962967689243101256809095)
            ·
              refine ⟨2944451533864651885213643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962967689243101256809095 2944451533864651885213643)
              ·
                refine ⟨4416677300796977827820465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944451533864651885213643 4416677300796977827820465)
                ·
                  refine ⟨3312507975597733370865349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4416677300796977827820465 3312507975597733370865349)
                  ·
                    refine ⟨621095245424575007037253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312507975597733370865349 621095245424575007037253)
                    ·
                      rfl

theorem cell22_1814368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_1814368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814368 prefixEnd_1814368 := by exact prefixLift 1814368
  have htrace : WordTrace (prefixWord ++ tailWord_1814368) baseStart_1814368 baseEnd_1814368 := by
    simpa [prefixWord, tailWord_1814368, baseEnd_1814368] using wordTrace_append hprefix tailTrace_1814368
  have hstable : (prefixWord ++ tailWord_1814368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814368).length < 2 ^ (prefixWord ++ tailWord_1814368).sum := by decide
  have hdescent : baseEnd_1814368 < baseStart_1814368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814471 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1814471 : Nat := 118140960795 + 1814471 * 2 ^ 59
def prefixEnd_1814471 : Nat := 4983230072969 + 3 ^ 40 * 1814471 * 2
def baseEnd_1814471 : Nat := 621130504429517071711937

theorem tailTrace_1814471 : CollatzResearch.WordTrace tailWord_1814471 prefixEnd_1814471 621130504429517071711937 := by
  unfold tailWord_1814471
  simp only [CollatzResearch.WordTrace]
  refine ⟨66179194209488928820547267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44119462806325952547031511 66179194209488928820547267)
  ·
    refine ⟨99268791314233393230820901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66179194209488928820547267 99268791314233393230820901)
    ·
      refine ⟨18612898371418761230778919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99268791314233393230820901 18612898371418761230778919)
      ·
        refine ⟨27919347557128141846168379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18612898371418761230778919 27919347557128141846168379)
        ·
          refine ⟨41879021335692212769252569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27919347557128141846168379 41879021335692212769252569)
          ·
            refine ⟨31409266001769159576939427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41879021335692212769252569 31409266001769159576939427)
            ·
              refine ⟨47113899002653739365409141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31409266001769159576939427 47113899002653739365409141)
              ·
                refine ⟨4416928031498788065507107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47113899002653739365409141 4416928031498788065507107)
                ·
                  refine ⟨6625392047248182098260661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416928031498788065507107 6625392047248182098260661)
                  ·
                    refine ⟨621130504429517071711937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6625392047248182098260661 621130504429517071711937)
                    ·
                      rfl

theorem cell22_1814471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1814471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814471 prefixEnd_1814471 := by exact prefixLift 1814471
  have htrace : WordTrace (prefixWord ++ tailWord_1814471) baseStart_1814471 baseEnd_1814471 := by
    simpa [prefixWord, tailWord_1814471, baseEnd_1814471] using wordTrace_append hprefix tailTrace_1814471
  have hstable : (prefixWord ++ tailWord_1814471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814471).length < 2 ^ (prefixWord ++ tailWord_1814471).sum := by decide
  have hdescent : baseEnd_1814471 < baseStart_1814471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814533 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_1814533 : Nat := 118140960795 + 1814533 * 2 ^ 59
def prefixEnd_1814533 : Nat := 4983230072969 + 3 ^ 40 * 1814533 * 2
def baseEnd_1814533 : Nat := 621151728296569576661747

theorem tailTrace_1814533 : CollatzResearch.WordTrace tailWord_1814533 prefixEnd_1814533 621151728296569576661747 := by
  unfold tailWord_1814533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66181455535264313409304253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44120970356842875606202835 66181455535264313409304253)
  ·
    refine ⟨24818045825724117528489095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66181455535264313409304253 24818045825724117528489095)
    ·
      refine ⟨37227068738586176292733643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24818045825724117528489095 37227068738586176292733643)
      ·
        refine ⟨55840603107879264439100465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37227068738586176292733643 55840603107879264439100465)
        ·
          refine ⟨41880452330909448329325349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55840603107879264439100465 41880452330909448329325349)
          ·
            refine ⟨7852584812045521561748503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41880452330909448329325349 7852584812045521561748503)
            ·
              refine ⟨11778877218068282342622755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852584812045521561748503 11778877218068282342622755)
              ·
                refine ⟨17668315827102423513934133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778877218068282342622755 17668315827102423513934133)
                ·
                  refine ⟨1656404608790852204431325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17668315827102423513934133 1656404608790852204431325)
                  ·
                    refine ⟨621151728296569576661747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1656404608790852204431325 621151728296569576661747)
                    ·
                      rfl

theorem cell22_1814533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_1814533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814533 prefixEnd_1814533 := by exact prefixLift 1814533
  have htrace : WordTrace (prefixWord ++ tailWord_1814533) baseStart_1814533 baseEnd_1814533 := by
    simpa [prefixWord, tailWord_1814533, baseEnd_1814533] using wordTrace_append hprefix tailTrace_1814533
  have hstable : (prefixWord ++ tailWord_1814533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814533).length < 2 ^ (prefixWord ++ tailWord_1814533).sum := by decide
  have hdescent : baseEnd_1814533 < baseStart_1814533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814541 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1814541 : Nat := 118140960795 + 1814541 * 2 ^ 59
def prefixEnd_1814541 : Nat := 4983230072969 + 3 ^ 40 * 1814541 * 2
def baseEnd_1814541 : Nat := 207051488953353407487241

theorem tailTrace_1814541 : CollatzResearch.WordTrace tailWord_1814541 prefixEnd_1814541 207051488953353407487241 := by
  unfold tailWord_1814541
  simp only [CollatzResearch.WordTrace]
  refine ⟨66181747319235330775595477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44121164879490220517063651 66181747319235330775595477)
  ·
    refine ⟨1551134702794578065053019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66181747319235330775595477 1551134702794578065053019)
    ·
      refine ⟨2326702054191867097579529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551134702794578065053019 2326702054191867097579529)
      ·
        refine ⟨1745026540643900323184647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326702054191867097579529 1745026540643900323184647)
        ·
          refine ⟨2617539810965850484776971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745026540643900323184647 2617539810965850484776971)
          ·
            refine ⟨3926309716448775727165457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617539810965850484776971 3926309716448775727165457)
            ·
              refine ⟨2944732287336581795374093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926309716448775727165457 2944732287336581795374093)
              ·
                refine ⟨1104274607751218173265285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2944732287336581795374093 1104274607751218173265285)
                ·
                  refine ⟨207051488953353407487241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104274607751218173265285 207051488953353407487241)
                  ·
                    rfl

theorem cell22_1814541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1814541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814541 prefixEnd_1814541 := by exact prefixLift 1814541
  have htrace : WordTrace (prefixWord ++ tailWord_1814541) baseStart_1814541 baseEnd_1814541 := by
    simpa [prefixWord, tailWord_1814541, baseEnd_1814541] using wordTrace_append hprefix tailTrace_1814541
  have hstable : (prefixWord ++ tailWord_1814541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814541).length < 2 ^ (prefixWord ++ tailWord_1814541).sum := by decide
  have hdescent : baseEnd_1814541 < baseStart_1814541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814578 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1814578 : Nat := 118140960795 + 1814578 * 2 ^ 59
def prefixEnd_1814578 : Nat := 4983230072969 + 3 ^ 40 * 1814578 * 2
def baseEnd_1814578 : Nat := 621167132716204459286609

theorem tailTrace_1814578 : CollatzResearch.WordTrace tailWord_1814578 prefixEnd_1814578 621167132716204459286609 := by
  unfold tailWord_1814578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16545774205025321523673097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44122064546734190729794925 16545774205025321523673097)
  ·
    refine ⟨12409330653768991142754823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16545774205025321523673097 12409330653768991142754823)
    ·
      refine ⟨18613995980653486714132235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409330653768991142754823 18613995980653486714132235)
      ·
        refine ⟨27920993970980230071198353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18613995980653486714132235 27920993970980230071198353)
        ·
          refine ⟨20940745478235172553398765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27920993970980230071198353 20940745478235172553398765)
          ·
            refine ⟨7852779554338189707524537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20940745478235172553398765 7852779554338189707524537)
            ·
              refine ⟨5889584665753642280643403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852779554338189707524537 5889584665753642280643403)
              ·
                refine ⟨8834376998630463420965105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889584665753642280643403 8834376998630463420965105)
                ·
                  refine ⟨6625782748972847565723829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8834376998630463420965105 6625782748972847565723829)
                  ·
                    refine ⟨621167132716204459286609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6625782748972847565723829 621167132716204459286609)
                    ·
                      rfl

theorem cell22_1814578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1814578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814578 prefixEnd_1814578 := by exact prefixLift 1814578
  have htrace : WordTrace (prefixWord ++ tailWord_1814578) baseStart_1814578 baseEnd_1814578 := by
    simpa [prefixWord, tailWord_1814578, baseEnd_1814578] using wordTrace_append hprefix tailTrace_1814578
  have hstable : (prefixWord ++ tailWord_1814578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814578).length < 2 ^ (prefixWord ++ tailWord_1814578).sum := by decide
  have hdescent : baseEnd_1814578 < baseStart_1814578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814653 : List Nat := [1, 4, 1, 1, 3, 2, 2, 8]
def baseStart_1814653 : Nat := 118140960795 + 1814653 * 2 ^ 59
def prefixEnd_1814653 : Nat := 4983230072969 + 3 ^ 40 * 1814653 * 2
def baseEnd_1814653 : Nat := 69021422972103251517931

theorem tailTrace_1814653 : CollatzResearch.WordTrace tailWord_1814653 prefixEnd_1814653 69021422972103251517931 := by
  unfold tailWord_1814653
  simp only [CollatzResearch.WordTrace]
  refine ⟨66185832294829573903672613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44123888196553049269115075 66185832294829573903672613)
  ·
    refine ⟨12409843555280545106938615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66185832294829573903672613 12409843555280545106938615)
    ·
      refine ⟨18614765332920817660407923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409843555280545106938615 18614765332920817660407923)
      ·
        refine ⟨27922147999381226490611885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18614765332920817660407923 27922147999381226490611885)
        ·
          refine ⟨10470805499767959933979457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27922147999381226490611885 10470805499767959933979457)
          ·
            refine ⟨7853104124825969950484593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10470805499767959933979457 7853104124825969950484593)
            ·
              refine ⟨5889828093619477462863445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7853104124825969950484593 5889828093619477462863445)
              ·
                refine ⟨69021422972103251517931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5889828093619477462863445 69021422972103251517931)
                ·
                  rfl

theorem cell22_1814653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 8].length) (baseStart_1814653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814653 prefixEnd_1814653 := by exact prefixLift 1814653
  have htrace : WordTrace (prefixWord ++ tailWord_1814653) baseStart_1814653 baseEnd_1814653 := by
    simpa [prefixWord, tailWord_1814653, baseEnd_1814653] using wordTrace_append hprefix tailTrace_1814653
  have hstable : (prefixWord ++ tailWord_1814653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814653).length < 2 ^ (prefixWord ++ tailWord_1814653).sum := by decide
  have hdescent : baseEnd_1814653 < baseStart_1814653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814670 : List Nat := [4, 1, 1, 3, 4, 9]
def baseStart_1814670 : Nat := 118140960795 + 1814670 * 2 ^ 59
def prefixEnd_1814670 : Nat := 4983230072969 + 3 ^ 40 * 1814670 * 2
def baseEnd_1814670 : Nat := 7669118841930208468967

theorem tailTrace_1814670 : CollatzResearch.WordTrace tailWord_1814670 prefixEnd_1814670 7669118841930208468967 := by
  unfold tailWord_1814670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8273306541970998225880183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44124301557178657204694309 8273306541970998225880183)
  ·
    refine ⟨12409959812956497338820275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8273306541970998225880183 12409959812956497338820275)
    ·
      refine ⟨18614939719434746008230413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409959812956497338820275 18614939719434746008230413)
      ·
        refine ⟨6980602394788029753086405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18614939719434746008230413 6980602394788029753086405)
        ·
          refine ⟨1308862949022755578703701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6980602394788029753086405 1308862949022755578703701)
          ·
            refine ⟨7669118841930208468967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1308862949022755578703701 7669118841930208468967)
            ·
              rfl

theorem cell22_1814670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 9].length) (baseStart_1814670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814670 prefixEnd_1814670 := by exact prefixLift 1814670
  have htrace : WordTrace (prefixWord ++ tailWord_1814670) baseStart_1814670 baseEnd_1814670 := by
    simpa [prefixWord, tailWord_1814670, baseEnd_1814670] using wordTrace_append hprefix tailTrace_1814670
  have hstable : (prefixWord ++ tailWord_1814670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814670).length < 2 ^ (prefixWord ++ tailWord_1814670).sum := by decide
  have hdescent : baseEnd_1814670 < baseStart_1814670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814713 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_1814713 : Nat := 118140960795 + 1814713 * 2 ^ 59
def prefixEnd_1814713 : Nat := 4983230072969 + 3 ^ 40 * 1814713 * 2
def baseEnd_1814713 : Nat := 621213345975109107161195

theorem tailTrace_1814713 : CollatzResearch.WordTrace tailWord_1814713 prefixEnd_1814713 621213345975109107161195 := by
  unfold tailWord_1814713
  simp only [CollatzResearch.WordTrace]
  refine ⟨66188020674612204150856793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44125347116408136100571195 66188020674612204150856793)
  ·
    refine ⟨49641015505959153113142595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66188020674612204150856793 49641015505959153113142595)
    ·
      refine ⟨74461523258938729669713893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49641015505959153113142595 74461523258938729669713893)
      ·
        refine ⟨13961535611051011813071355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74461523258938729669713893 13961535611051011813071355)
        ·
          refine ⟨20942303416576517719607033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13961535611051011813071355 20942303416576517719607033)
          ·
            refine ⟨15706727562432388289705275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20942303416576517719607033 15706727562432388289705275)
            ·
              refine ⟨23560091343648582434557913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15706727562432388289705275 23560091343648582434557913)
              ·
                refine ⟨17670068507736436825918435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23560091343648582434557913 17670068507736436825918435)
                ·
                  refine ⟨26505102761604655238877653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17670068507736436825918435 26505102761604655238877653)
                  ·
                    refine ⟨621213345975109107161195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26505102761604655238877653 621213345975109107161195)
                    ·
                      rfl

theorem cell22_1814713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_1814713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814713 prefixEnd_1814713 := by exact prefixLift 1814713
  have htrace : WordTrace (prefixWord ++ tailWord_1814713) baseStart_1814713 baseEnd_1814713 := by
    simpa [prefixWord, tailWord_1814713, baseEnd_1814713] using wordTrace_append hprefix tailTrace_1814713
  have hstable : (prefixWord ++ tailWord_1814713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814713).length < 2 ^ (prefixWord ++ tailWord_1814713).sum := by decide
  have hdescent : baseEnd_1814713 < baseStart_1814713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814732 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 7]
def baseStart_1814732 : Nat := 118140960795 + 1814732 * 2 ^ 59
def prefixEnd_1814732 : Nat := 4983230072969 + 3 ^ 40 * 1814732 * 2
def baseEnd_1814732 : Nat := 207073283354466463645379

theorem tailTrace_1814732 : CollatzResearch.WordTrace tailWord_1814732 prefixEnd_1814732 207073283354466463645379 := by
  unfold tailWord_1814732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094356830771685197899225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44125809107695580263865633 33094356830771685197899225)
  ·
    refine ⟨24820767623078763898424419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33094356830771685197899225 24820767623078763898424419)
    ·
      refine ⟨37231151434618145847636629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24820767623078763898424419 37231151434618145847636629)
      ·
        refine ⟨1745210223497725586607967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37231151434618145847636629 1745210223497725586607967)
        ·
          refine ⟨2617815335246588379911951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745210223497725586607967 2617815335246588379911951)
          ·
            refine ⟨3926723002869882569867927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617815335246588379911951 3926723002869882569867927)
            ·
              refine ⟨5890084504304823854801891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926723002869882569867927 5890084504304823854801891)
              ·
                refine ⟨8835126756457235782202837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890084504304823854801891 8835126756457235782202837)
                ·
                  refine ⟨207073283354466463645379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8835126756457235782202837 207073283354466463645379)
                  ·
                    rfl

theorem cell22_1814732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_1814732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814732 prefixEnd_1814732 := by exact prefixLift 1814732
  have htrace : WordTrace (prefixWord ++ tailWord_1814732) baseStart_1814732 baseEnd_1814732 := by
    simpa [prefixWord, tailWord_1814732, baseEnd_1814732] using wordTrace_append hprefix tailTrace_1814732
  have hstable : (prefixWord ++ tailWord_1814732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814732).length < 2 ^ (prefixWord ++ tailWord_1814732).sum := by decide
  have hdescent : baseEnd_1814732 < baseStart_1814732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814749 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1814749 : Nat := 118140960795 + 1814749 * 2 ^ 59
def prefixEnd_1814749 : Nat := 4983230072969 + 3 ^ 40 * 1814749 * 2
def baseEnd_1814749 : Nat := 207075223170272337753695

theorem tailTrace_1814749 : CollatzResearch.WordTrace tailWord_1814749 prefixEnd_1814749 207075223170272337753695 := by
  unfold tailWord_1814749
  simp only [CollatzResearch.WordTrace]
  refine ⟨66189333702481782299167301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44126222468321188199444867 66189333702481782299167301)
  ·
    refine ⟨12410500069215334181093869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66189333702481782299167301 12410500069215334181093869)
    ·
      refine ⟨4653937525955750317910201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12410500069215334181093869 4653937525955750317910201)
      ·
        refine ⟨3490453144466812738432651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653937525955750317910201 3490453144466812738432651)
        ·
          refine ⟨5235679716700219107648977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490453144466812738432651 5235679716700219107648977)
          ·
            refine ⟨3926759787525164330736733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5235679716700219107648977 3926759787525164330736733)
            ·
              refine ⟨1472534920321936624026275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3926759787525164330736733 1472534920321936624026275)
              ·
                refine ⟨2208802380482904936039413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472534920321936624026275 2208802380482904936039413)
                ·
                  refine ⟨207075223170272337753695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2208802380482904936039413 207075223170272337753695)
                  ·
                    rfl

theorem cell22_1814749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1814749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814749 prefixEnd_1814749 := by exact prefixLift 1814749
  have htrace : WordTrace (prefixWord ++ tailWord_1814749) baseStart_1814749 baseEnd_1814749 := by
    simpa [prefixWord, tailWord_1814749, baseEnd_1814749] using wordTrace_append hprefix tailTrace_1814749
  have hstable : (prefixWord ++ tailWord_1814749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814749).length < 2 ^ (prefixWord ++ tailWord_1814749).sum := by decide
  have hdescent : baseEnd_1814749 < baseStart_1814749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814760 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_1814760 : Nat := 118140960795 + 1814760 * 2 ^ 59
def prefixEnd_1814760 : Nat := 4983230072969 + 3 ^ 40 * 1814760 * 2
def baseEnd_1814760 : Nat := 207076478345205550412017

theorem tailTrace_1814760 : CollatzResearch.WordTrace tailWord_1814760 prefixEnd_1814760 207076478345205550412017 := by
  unfold tailWord_1814760
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094867452720965588908867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44126489936961287451878489 33094867452720965588908867)
  ·
    refine ⟨49642301179081448383363301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33094867452720965588908867 49642301179081448383363301)
    ·
      refine ⟨9307931471077771571880619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49642301179081448383363301 9307931471077771571880619)
      ·
        refine ⟨13961897206616657357820929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9307931471077771571880619 13961897206616657357820929)
        ·
          refine ⟨10471422904962493018365697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13961897206616657357820929 10471422904962493018365697)
          ·
            refine ⟨7853567178721869763774273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10471422904962493018365697 7853567178721869763774273)
            ·
              refine ⟨5890175384041402322830705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7853567178721869763774273 5890175384041402322830705)
              ·
                refine ⟨4417631538031051742123029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890175384041402322830705 4417631538031051742123029)
                ·
                  refine ⟨207076478345205550412017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4417631538031051742123029 207076478345205550412017)
                  ·
                    rfl

theorem cell22_1814760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_1814760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814760 prefixEnd_1814760 := by exact prefixLift 1814760
  have htrace : WordTrace (prefixWord ++ tailWord_1814760) baseStart_1814760 baseEnd_1814760 := by
    simpa [prefixWord, tailWord_1814760, baseEnd_1814760] using wordTrace_append hprefix tailTrace_1814760
  have hstable : (prefixWord ++ tailWord_1814760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814760).length < 2 ^ (prefixWord ++ tailWord_1814760).sum := by decide
  have hdescent : baseEnd_1814760 < baseStart_1814760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814762 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1814762 : Nat := 118140960795 + 1814762 * 2 ^ 59
def prefixEnd_1814762 : Nat := 4983230072969 + 3 ^ 40 * 1814762 * 2
def baseEnd_1814762 : Nat := 621230119676489312686045

theorem tailTrace_1814762 : CollatzResearch.WordTrace tailWord_1814762 prefixEnd_1814762 621230119676489312686045 := by
  unfold tailWord_1814762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16547451962858671379847635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44126538567623123679593693 16547451962858671379847635)
  ·
    refine ⟨24821177944288007069771453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16547451962858671379847635 24821177944288007069771453)
    ·
      refine ⟨9307941729108002651164295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24821177944288007069771453 9307941729108002651164295)
      ·
        refine ⟨13961912593662003976746443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9307941729108002651164295 13961912593662003976746443)
        ·
          refine ⟨20942868890493005965119665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13961912593662003976746443 20942868890493005965119665)
          ·
            refine ⟨15707151667869754473839749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20942868890493005965119665 15707151667869754473839749)
            ·
              refine ⟨2945090937725578963844953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15707151667869754473839749 2945090937725578963844953)
              ·
                refine ⟨2208818203294184222883715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945090937725578963844953 2208818203294184222883715)
                ·
                  refine ⟨3313227304941276334325573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208818203294184222883715 3313227304941276334325573)
                  ·
                    refine ⟨621230119676489312686045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313227304941276334325573 621230119676489312686045)
                    ·
                      rfl

theorem cell22_1814762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1814762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814762 prefixEnd_1814762 := by exact prefixLift 1814762
  have htrace : WordTrace (prefixWord ++ tailWord_1814762) baseStart_1814762 baseEnd_1814762 := by
    simpa [prefixWord, tailWord_1814762, baseEnd_1814762] using wordTrace_append hprefix tailTrace_1814762
  have hstable : (prefixWord ++ tailWord_1814762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814762).length < 2 ^ (prefixWord ++ tailWord_1814762).sum := by decide
  have hdescent : baseEnd_1814762 < baseStart_1814762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814792 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_1814792 : Nat := 118140960795 + 1814792 * 2 ^ 59
def prefixEnd_1814792 : Nat := 4983230072969 + 3 ^ 40 * 1814792 * 2
def baseEnd_1814792 : Nat := 621240389289579234435953

theorem tailTrace_1814792 : CollatzResearch.WordTrace tailWord_1814792 prefixEnd_1814792 621240389289579234435953 := by
  unfold tailWord_1814792
  simp only [CollatzResearch.WordTrace]
  refine ⟨33095451020663000321491315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44127268027550667095321753 33095451020663000321491315)
  ·
    refine ⟨49643176530994500482236973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33095451020663000321491315 49643176530994500482236973)
    ·
      refine ⟨18616191199122937680838865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49643176530994500482236973 18616191199122937680838865)
      ·
        refine ⟨13962143399342203260629149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18616191199122937680838865 13962143399342203260629149)
        ·
          refine ⟨5235803774753326222735931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13962143399342203260629149 5235803774753326222735931)
          ·
            refine ⟨7853705662129989334103897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235803774753326222735931 7853705662129989334103897)
            ·
              refine ⟨5890279246597492000577923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7853705662129989334103897 5890279246597492000577923)
              ·
                refine ⟨8835418869896238000866885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890279246597492000577923 8835418869896238000866885)
                ·
                  refine ⟨1656641038105544625162541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8835418869896238000866885 1656641038105544625162541)
                  ·
                    refine ⟨621240389289579234435953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1656641038105544625162541 621240389289579234435953)
                    ·
                      rfl

theorem cell22_1814792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_1814792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814792 prefixEnd_1814792 := by exact prefixLift 1814792
  have htrace : WordTrace (prefixWord ++ tailWord_1814792) baseStart_1814792 baseEnd_1814792 := by
    simpa [prefixWord, tailWord_1814792, baseEnd_1814792] using wordTrace_append hprefix tailTrace_1814792
  have hstable : (prefixWord ++ tailWord_1814792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814792).length < 2 ^ (prefixWord ++ tailWord_1814792).sum := by decide
  have hdescent : baseEnd_1814792 < baseStart_1814792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814824 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1814824 : Nat := 118140960795 + 1814824 * 2 ^ 59
def prefixEnd_1814824 : Nat := 4983230072969 + 3 ^ 40 * 1814824 * 2
def baseEnd_1814824 : Nat := 621251343543541817635855

theorem tailTrace_1814824 : CollatzResearch.WordTrace tailWord_1814824 prefixEnd_1814824 621251343543541817635855 := by
  unfold tailWord_1814824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33096034588605035054073763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44128046118140046738765017 33096034588605035054073763)
  ·
    refine ⟨49644051882907552581110645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33096034588605035054073763 49644051882907552581110645)
    ·
      refine ⟨4654129864022583054479123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49644051882907552581110645 4654129864022583054479123)
      ·
        refine ⟨6981194796033874581718685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654129864022583054479123 6981194796033874581718685)
        ·
          refine ⟨2617948048512702968144507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6981194796033874581718685 2617948048512702968144507)
          ·
            refine ⟨3926922072769054452216761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617948048512702968144507 3926922072769054452216761)
            ·
              refine ⟨2945191554576790839162571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926922072769054452216761 2945191554576790839162571)
              ·
                refine ⟨4417787331865186258743857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945191554576790839162571 4417787331865186258743857)
                ·
                  refine ⟨3313340498898889694057893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4417787331865186258743857 3313340498898889694057893)
                  ·
                    refine ⟨621251343543541817635855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313340498898889694057893 621251343543541817635855)
                    ·
                      rfl

theorem cell22_1814824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1814824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814824 prefixEnd_1814824 := by exact prefixLift 1814824
  have htrace : WordTrace (prefixWord ++ tailWord_1814824) baseStart_1814824 baseEnd_1814824 := by
    simpa [prefixWord, tailWord_1814824, baseEnd_1814824] using wordTrace_append hprefix tailTrace_1814824
  have hstable : (prefixWord ++ tailWord_1814824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814824).length < 2 ^ (prefixWord ++ tailWord_1814824).sum := by decide
  have hdescent : baseEnd_1814824 < baseStart_1814824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814865 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1814865 : Nat := 118140960795 + 1814865 * 2 ^ 59
def prefixEnd_1814865 : Nat := 4983230072969 + 3 ^ 40 * 1814865 * 2
def baseEnd_1814865 : Nat := 621265378681431377360729

theorem tailTrace_1814865 : CollatzResearch.WordTrace tailWord_1814865 prefixEnd_1814865 621265378681431377360729 := by
  unfold tailWord_1814865
  simp only [CollatzResearch.WordTrace]
  refine ⟨66193564570061534110390049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44129043046707689406926699 66193564570061534110390049)
  ·
    refine ⟨49645173427546150582792537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66193564570061534110390049 49645173427546150582792537)
    ·
      refine ⟨37233880070659612937094403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49645173427546150582792537 37233880070659612937094403)
      ·
        refine ⟨55850820105989419405641605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37233880070659612937094403 55850820105989419405641605)
        ·
          refine ⟨10472028769873016138557801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55850820105989419405641605 10472028769873016138557801)
          ·
            refine ⟨7854021577404762103918351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10472028769873016138557801 7854021577404762103918351)
            ·
              refine ⟨11781032366107143155877527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854021577404762103918351 11781032366107143155877527)
              ·
                refine ⟨17671548549160714733816291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11781032366107143155877527 17671548549160714733816291)
                ·
                  refine ⟨26507322823741072100724437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17671548549160714733816291 26507322823741072100724437)
                  ·
                    refine ⟨621265378681431377360729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26507322823741072100724437 621265378681431377360729)
                    ·
                      rfl

theorem cell22_1814865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1814865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1814865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1814865 prefixEnd_1814865 := by exact prefixLift 1814865
  have htrace : WordTrace (prefixWord ++ tailWord_1814865) baseStart_1814865 baseEnd_1814865 := by
    simpa [prefixWord, tailWord_1814865, baseEnd_1814865] using wordTrace_append hprefix tailTrace_1814865
  have hstable : (prefixWord ++ tailWord_1814865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814865).length < 2 ^ (prefixWord ++ tailWord_1814865).sum := by decide
  have hdescent : baseEnd_1814865 < baseStart_1814865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815032 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_1815032 : Nat := 118140960795 + 1815032 * 2 ^ 59
def prefixEnd_1815032 : Nat := 4983230072969 + 3 ^ 40 * 1815032 * 2
def baseEnd_1815032 : Nat := 621322546194298608435217

theorem tailTrace_1815032 : CollatzResearch.WordTrace tailWord_1815032 prefixEnd_1815032 621322546194298608435217 := by
  unfold tailWord_1815032
  simp only [CollatzResearch.WordTrace]
  refine ⟨33099827780228260815859675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44133103706971014421146233 33099827780228260815859675)
  ·
    refine ⟨49649741670342391223789513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33099827780228260815859675 49649741670342391223789513)
    ·
      refine ⟨37237306252756793417842135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49649741670342391223789513 37237306252756793417842135)
      ·
        refine ⟨55855959379135190126763203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37237306252756793417842135 55855959379135190126763203)
        ·
          refine ⟨83783939068702785190144805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55855959379135190126763203 83783939068702785190144805)
          ·
            refine ⟨15709488575381772223152151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83783939068702785190144805 15709488575381772223152151)
            ·
              refine ⟨23564232863072658334728227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15709488575381772223152151 23564232863072658334728227)
              ·
                refine ⟨35346349294608987502092341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23564232863072658334728227 35346349294608987502092341)
                ·
                  refine ⟨3313720246369592578321157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35346349294608987502092341 3313720246369592578321157)
                  ·
                    refine ⟨621322546194298608435217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313720246369592578321157 621322546194298608435217)
                    ·
                      rfl

theorem cell22_1815032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_1815032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815032 prefixEnd_1815032 := by exact prefixLift 1815032
  have htrace : WordTrace (prefixWord ++ tailWord_1815032) baseStart_1815032 baseEnd_1815032 := by
    simpa [prefixWord, tailWord_1815032, baseEnd_1815032] using wordTrace_append hprefix tailTrace_1815032
  have hstable : (prefixWord ++ tailWord_1815032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815032).length < 2 ^ (prefixWord ++ tailWord_1815032).sum := by decide
  have hdescent : baseEnd_1815032 < baseStart_1815032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815066 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_1815066 : Nat := 118140960795 + 1815066 * 2 ^ 59
def prefixEnd_1815066 : Nat := 4983230072969 + 3 ^ 40 * 1815066 * 2
def baseEnd_1815066 : Nat := 621334185089133853085113

theorem tailTrace_1815066 : CollatzResearch.WordTrace tailWord_1815066 prefixEnd_1815066 621334185089133853085113 := by
  unfold tailWord_1815066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550223910583336359614263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44133930428222230292304701 16550223910583336359614263)
  ·
    refine ⟨24825335865875004539421395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16550223910583336359614263 24825335865875004539421395)
    ·
      refine ⟨37238003798812506809132093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825335865875004539421395 37238003798812506809132093)
      ·
        refine ⟨13964251424554690053424535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37238003798812506809132093 13964251424554690053424535)
        ·
          refine ⟨20946377136832035080136803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13964251424554690053424535 20946377136832035080136803)
          ·
            refine ⟨31419565705248052620205205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20946377136832035080136803 31419565705248052620205205)
            ·
              refine ⟨1472792142433502466572119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31419565705248052620205205 1472792142433502466572119)
              ·
                refine ⟨2209188213650253699858179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472792142433502466572119 2209188213650253699858179)
                ·
                  refine ⟨3313782320475380549787269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209188213650253699858179 3313782320475380549787269)
                  ·
                    refine ⟨621334185089133853085113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313782320475380549787269 621334185089133853085113)
                    ·
                      rfl

theorem cell22_1815066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_1815066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815066 prefixEnd_1815066 := by exact prefixLift 1815066
  have htrace : WordTrace (prefixWord ++ tailWord_1815066) baseStart_1815066 baseEnd_1815066 := by
    simpa [prefixWord, tailWord_1815066, baseEnd_1815066] using wordTrace_append hprefix tailTrace_1815066
  have hstable : (prefixWord ++ tailWord_1815066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815066).length < 2 ^ (prefixWord ++ tailWord_1815066).sum := by decide
  have hdescent : baseEnd_1815066 < baseStart_1815066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815109 : List Nat := [1, 3, 1, 1, 1, 5, 4, 6]
def baseStart_1815109 : Nat := 118140960795 + 1815109 * 2 ^ 59
def prefixEnd_1815109 : Nat := 4983230072969 + 3 ^ 40 * 1815109 * 2
def baseEnd_1815109 : Nat := 69038767207544008251109

theorem tailTrace_1815109 : CollatzResearch.WordTrace tailWord_1815109 prefixEnd_1815109 69038767207544008251109 := by
  unfold tailWord_1815109
  simp only [CollatzResearch.WordTrace]
  refine ⟨66202463981177563782272381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44134975987451709188181587 66202463981177563782272381)
  ·
    refine ⟨24825923992941586418352143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66202463981177563782272381 24825923992941586418352143)
    ·
      refine ⟨37238885989412379627528215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825923992941586418352143 37238885989412379627528215)
      ·
        refine ⟨55858328984118569441292323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37238885989412379627528215 55858328984118569441292323)
        ·
          refine ⟨83787493476177854161938485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55858328984118569441292323 83787493476177854161938485)
          ·
            refine ⟨7855077513391673827681733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83787493476177854161938485 7855077513391673827681733)
            ·
              refine ⟨1472827033760938842690325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7855077513391673827681733 1472827033760938842690325)
              ·
                refine ⟨69038767207544008251109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1472827033760938842690325 69038767207544008251109)
                ·
                  rfl

theorem cell22_1815109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 6].length) (baseStart_1815109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815109 prefixEnd_1815109 := by exact prefixLift 1815109
  have htrace : WordTrace (prefixWord ++ tailWord_1815109) baseStart_1815109 baseEnd_1815109 := by
    simpa [prefixWord, tailWord_1815109, baseEnd_1815109] using wordTrace_append hprefix tailTrace_1815109
  have hstable : (prefixWord ++ tailWord_1815109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815109).length < 2 ^ (prefixWord ++ tailWord_1815109).sum := by decide
  have hdescent : baseEnd_1815109 < baseStart_1815109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815188 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1815188 : Nat := 118140960795 + 1815188 * 2 ^ 59
def prefixEnd_1815188 : Nat := 4983230072969 + 3 ^ 40 * 1815188 * 2
def baseEnd_1815188 : Nat := 207125316060788733844913

theorem tailTrace_1815188 : CollatzResearch.WordTrace tailWord_1815188 prefixEnd_1815188 207125316060788733844913 := by
  unfold tailWord_1815188
  simp only [CollatzResearch.WordTrace]
  refine ⟨33102672673945680137199109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44136896898594240182932145 33102672673945680137199109)
  ·
    refine ⟨6206751126364815025724833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33102672673945680137199109 6206751126364815025724833)
    ·
      refine ⟨4655063344773611269293625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6206751126364815025724833 4655063344773611269293625)
      ·
        refine ⟨3491297508580208451970219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4655063344773611269293625 3491297508580208451970219)
        ·
          refine ⟨5236946262870312677955329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491297508580208451970219 5236946262870312677955329)
          ·
            refine ⟨3927709697152734508466497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5236946262870312677955329 3927709697152734508466497)
            ·
              refine ⟨2945782272864550881349873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3927709697152734508466497 2945782272864550881349873)
              ·
                refine ⟨2209336704648413161012405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945782272864550881349873 2209336704648413161012405)
                ·
                  refine ⟨207125316060788733844913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209336704648413161012405 207125316060788733844913)
                  ·
                    rfl

theorem cell22_1815188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1815188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815188 prefixEnd_1815188 := by exact prefixLift 1815188
  have htrace : WordTrace (prefixWord ++ tailWord_1815188) baseStart_1815188 baseEnd_1815188 := by
    simpa [prefixWord, tailWord_1815188, baseEnd_1815188] using wordTrace_append hprefix tailTrace_1815188
  have hstable : (prefixWord ++ tailWord_1815188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815188).length < 2 ^ (prefixWord ++ tailWord_1815188).sum := by decide
  have hdescent : baseEnd_1815188 < baseStart_1815188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815265 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 2, 3]
def baseStart_1815265 : Nat := 118140960795 + 1815265 * 2 ^ 59
def prefixEnd_1815265 : Nat := 4983230072969 + 3 ^ 40 * 1815265 * 2
def baseEnd_1815265 : Nat := 621402306855963667359503

theorem tailTrace_1815265 : CollatzResearch.WordTrace tailWord_1815265 prefixEnd_1815265 621402306855963667359503 := by
  unfold tailWord_1815265
  simp only [CollatzResearch.WordTrace]
  refine ⟨66208153768612402424951249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44138769179074934949967499 66208153768612402424951249)
  ·
    refine ⟨49656115326459301818713437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66208153768612402424951249 49656115326459301818713437)
    ·
      refine ⟨18621043247422238182017539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49656115326459301818713437 18621043247422238182017539)
      ·
        refine ⟨27931564871133357273026309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18621043247422238182017539 27931564871133357273026309)
        ·
          refine ⟨5237168413337504488692433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27931564871133357273026309 5237168413337504488692433)
          ·
            refine ⟨3927876310003128366519325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5237168413337504488692433 3927876310003128366519325)
            ·
              refine ⟨1472953616251173137444747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3927876310003128366519325 1472953616251173137444747)
              ·
                refine ⟨2209430424376759706167121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472953616251173137444747 2209430424376759706167121)
                ·
                  refine ⟨1657072818282569779625341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209430424376759706167121 1657072818282569779625341)
                  ·
                    refine ⟨621402306855963667359503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657072818282569779625341 621402306855963667359503)
                    ·
                      rfl

theorem cell22_1815265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_1815265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815265 prefixEnd_1815265 := by exact prefixLift 1815265
  have htrace : WordTrace (prefixWord ++ tailWord_1815265) baseStart_1815265 baseEnd_1815265 := by
    simpa [prefixWord, tailWord_1815265, baseEnd_1815265] using wordTrace_append hprefix tailTrace_1815265
  have hstable : (prefixWord ++ tailWord_1815265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815265).length < 2 ^ (prefixWord ++ tailWord_1815265).sum := by decide
  have hdescent : baseEnd_1815265 < baseStart_1815265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815278 : List Nat := [4, 1, 2, 1, 1, 5, 2, 6]
def baseStart_1815278 : Nat := 118140960795 + 1815278 * 2 ^ 59
def prefixEnd_1815278 : Nat := 4983230072969 + 3 ^ 40 * 1815278 * 2
def baseEnd_1815278 : Nat := 69045195224626218531607

theorem tailTrace_1815278 : CollatzResearch.WordTrace tailWord_1815278 prefixEnd_1815278 69045195224626218531607 := by
  unfold tailWord_1815278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276078489695663205646811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44139085278376870430116325 8276078489695663205646811)
  ·
    refine ⟨12414117734543494808470217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8276078489695663205646811 12414117734543494808470217)
    ·
      refine ⟨9310588300907621106352663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12414117734543494808470217 9310588300907621106352663)
      ·
        refine ⟨13965882451361431659528995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310588300907621106352663 13965882451361431659528995)
        ·
          refine ⟨20948823677042147489293493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13965882451361431659528995 20948823677042147489293493)
          ·
            refine ⟨1963952219722701327121265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20948823677042147489293493 1963952219722701327121265)
            ·
              refine ⟨1472964164792025995340949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963952219722701327121265 1472964164792025995340949)
              ·
                refine ⟨69045195224626218531607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1472964164792025995340949 69045195224626218531607)
                ·
                  rfl

theorem cell22_1815278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_1815278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815278 prefixEnd_1815278 := by exact prefixLift 1815278
  have htrace : WordTrace (prefixWord ++ tailWord_1815278) baseStart_1815278 baseEnd_1815278 := by
    simpa [prefixWord, tailWord_1815278, baseEnd_1815278] using wordTrace_append hprefix tailTrace_1815278
  have hstable : (prefixWord ++ tailWord_1815278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815278).length < 2 ^ (prefixWord ++ tailWord_1815278).sum := by decide
  have hdescent : baseEnd_1815278 < baseStart_1815278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815284 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1815284 : Nat := 118140960795 + 1815284 * 2 ^ 59
def prefixEnd_1815284 : Nat := 4983230072969 + 3 ^ 40 * 1815284 * 2
def baseEnd_1815284 : Nat := 207136270314751317044815

theorem tailTrace_1815284 : CollatzResearch.WordTrace tailWord_1815284 prefixEnd_1815284 207136270314751317044815 := by
  unfold tailWord_1815284
  simp only [CollatzResearch.WordTrace]
  refine ⟨33104423377771784334946453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44139231170362379113261937 33104423377771784334946453)
  ·
    refine ⟨1551769845833052390700615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33104423377771784334946453 1551769845833052390700615)
    ·
      refine ⟨2327654768749578586050923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551769845833052390700615 2327654768749578586050923)
      ·
        refine ⟨3491482153124367879076385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327654768749578586050923 3491482153124367879076385)
        ·
          refine ⟨2618611614843275909307289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3491482153124367879076385 2618611614843275909307289)
          ·
            refine ⟨1963958711132456931980467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618611614843275909307289 1963958711132456931980467)
            ·
              refine ⟨2945938066698685397970701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963958711132456931980467 2945938066698685397970701)
              ·
                refine ⟨1104726775012007024239013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2945938066698685397970701 1104726775012007024239013)
                ·
                  refine ⟨207136270314751317044815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104726775012007024239013 207136270314751317044815)
                  ·
                    rfl

theorem cell22_1815284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1815284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815284 prefixEnd_1815284 := by exact prefixLift 1815284
  have htrace : WordTrace (prefixWord ++ tailWord_1815284) baseStart_1815284 baseEnd_1815284 := by
    simpa [prefixWord, tailWord_1815284, baseEnd_1815284] using wordTrace_append hprefix tailTrace_1815284
  have hstable : (prefixWord ++ tailWord_1815284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815284).length < 2 ^ (prefixWord ++ tailWord_1815284).sum := by decide
  have hdescent : baseEnd_1815284 < baseStart_1815284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815306 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_1815306 : Nat := 118140960795 + 1815306 * 2 ^ 59
def prefixEnd_1815306 : Nat := 4983230072969 + 3 ^ 40 * 1815306 * 2
def baseEnd_1815306 : Nat := 207138780664617742361459

theorem tailTrace_1815306 : CollatzResearch.WordTrace tailWord_1815306 prefixEnd_1815306 207138780664617742361459 := by
  unfold tailWord_1815306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16552412290365966606798443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44139766107642577618129181 16552412290365966606798443)
  ·
    refine ⟨24828618435548949910197665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16552412290365966606798443 24828618435548949910197665)
    ·
      refine ⟨18621463826661712432648249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24828618435548949910197665 18621463826661712432648249)
      ·
        refine ⟨13966097869996284324486187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18621463826661712432648249 13966097869996284324486187)
        ·
          refine ⟨20949146804994426486729281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966097869996284324486187 20949146804994426486729281)
          ·
            refine ⟨15711860103745819865046961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20949146804994426486729281 15711860103745819865046961)
            ·
              refine ⟨11783895077809364898785221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15711860103745819865046961 11783895077809364898785221)
              ·
                refine ⟨2209480327089255918522229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11783895077809364898785221 2209480327089255918522229)
                ·
                  refine ⟨207138780664617742361459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209480327089255918522229 207138780664617742361459)
                  ·
                    rfl

theorem cell22_1815306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_1815306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815306 prefixEnd_1815306 := by exact prefixLift 1815306
  have htrace : WordTrace (prefixWord ++ tailWord_1815306) baseStart_1815306 baseEnd_1815306 := by
    simpa [prefixWord, tailWord_1815306, baseEnd_1815306] using wordTrace_append hprefix tailTrace_1815306
  have hstable : (prefixWord ++ tailWord_1815306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815306).length < 2 ^ (prefixWord ++ tailWord_1815306).sum := by decide
  have hdescent : baseEnd_1815306 < baseStart_1815306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815361 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1815361 : Nat := 118140960795 + 1815361 * 2 ^ 59
def prefixEnd_1815361 : Nat := 4983230072969 + 3 ^ 40 * 1815361 * 2
def baseEnd_1815361 : Nat := 621435169617851416959209

theorem tailTrace_1815361 : CollatzResearch.WordTrace tailWord_1815361 prefixEnd_1815361 621435169617851416959209 := by
  unfold tailWord_1815361
  simp only [CollatzResearch.WordTrace]
  refine ⟨66211655176264610820445937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44141103450843073880297291 66211655176264610820445937)
  ·
    refine ⟨49658741382198458115334453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66211655176264610820445937 49658741382198458115334453)
    ·
      refine ⟨4655507004581105448312605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49658741382198458115334453 4655507004581105448312605)
      ·
        refine ⟨1745815126717914543117227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4655507004581105448312605 1745815126717914543117227)
        ·
          refine ⟨2618722690076871814675841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745815126717914543117227 2618722690076871814675841)
          ·
            refine ⟨1964042017557653861006881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618722690076871814675841 1964042017557653861006881)
            ·
              refine ⟨1473031513168240395755161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964042017557653861006881 1473031513168240395755161)
              ·
                refine ⟨1104773634876180296816371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473031513168240395755161 1104773634876180296816371)
                ·
                  refine ⟨1657160452314270445224557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104773634876180296816371 1657160452314270445224557)
                  ·
                    refine ⟨621435169617851416959209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657160452314270445224557 621435169617851416959209)
                    ·
                      rfl

theorem cell22_1815361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1815361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815361 prefixEnd_1815361 := by exact prefixLift 1815361
  have htrace : WordTrace (prefixWord ++ tailWord_1815361) baseStart_1815361 baseEnd_1815361 := by
    simpa [prefixWord, tailWord_1815361, baseEnd_1815361] using wordTrace_append hprefix tailTrace_1815361
  have hstable : (prefixWord ++ tailWord_1815361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815361).length < 2 ^ (prefixWord ++ tailWord_1815361).sum := by decide
  have hdescent : baseEnd_1815361 < baseStart_1815361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815368 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 4]
def baseStart_1815368 : Nat := 118140960795 + 1815368 * 2 ^ 59
def prefixEnd_1815368 : Nat := 4983230072969 + 3 ^ 40 * 1815368 * 2
def baseEnd_1815368 : Nat := 207145855286968577344729

theorem tailTrace_1815368 : CollatzResearch.WordTrace tailWord_1815368 prefixEnd_1815368 207145855286968577344729 := by
  unfold tailWord_1815368
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105955243619625507975379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44141273658159500677300505 33105955243619625507975379)
  ·
    refine ⟨49658932865429438261963069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33105955243619625507975379 49658932865429438261963069)
    ·
      refine ⟨18622099824536039348236151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49658932865429438261963069 18622099824536039348236151)
      ·
        refine ⟨27933149736804059022354227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18622099824536039348236151 27933149736804059022354227)
        ·
          refine ⟨41899724605206088533531341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27933149736804059022354227 41899724605206088533531341)
          ·
            refine ⟨15712396726952283200074253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41899724605206088533531341 15712396726952283200074253)
            ·
              refine ⟨5892148772607106200027845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15712396726952283200074253 5892148772607106200027845)
              ·
                refine ⟨1104777894863832412505221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5892148772607106200027845 1104777894863832412505221)
                ·
                  refine ⟨207145855286968577344729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104777894863832412505221 207145855286968577344729)
                  ·
                    rfl

theorem cell22_1815368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_1815368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815368 prefixEnd_1815368 := by exact prefixLift 1815368
  have htrace : WordTrace (prefixWord ++ tailWord_1815368) baseStart_1815368 baseEnd_1815368 := by
    simpa [prefixWord, tailWord_1815368, baseEnd_1815368] using wordTrace_append hprefix tailTrace_1815368
  have hstable : (prefixWord ++ tailWord_1815368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815368).length < 2 ^ (prefixWord ++ tailWord_1815368).sum := by decide
  have hdescent : baseEnd_1815368 < baseStart_1815368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815381 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1815381 : Nat := 118140960795 + 1815381 * 2 ^ 59
def prefixEnd_1815381 : Nat := 4983230072969 + 3 ^ 40 * 1815381 * 2
def baseEnd_1815381 : Nat := 621442016026578031459147

theorem tailTrace_1815381 : CollatzResearch.WordTrace tailWord_1815381 prefixEnd_1815381 621442016026578031459147 := by
  unfold tailWord_1815381
  simp only [CollatzResearch.WordTrace]
  refine ⟨66212384636192154236173997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44141589757461436157449331 66212384636192154236173997)
  ·
    refine ⟨24829644238572057838565249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66212384636192154236173997 24829644238572057838565249)
    ·
      refine ⟨18622233178929043378923937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24829644238572057838565249 18622233178929043378923937)
      ·
        refine ⟨13966674884196782534192953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18622233178929043378923937 13966674884196782534192953)
        ·
          refine ⟨10475006163147586900644715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13966674884196782534192953 10475006163147586900644715)
          ·
            refine ⟨15712509244721380350967073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10475006163147586900644715 15712509244721380350967073)
            ·
              refine ⟨11784381933541035263225305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15712509244721380350967073 11784381933541035263225305)
              ·
                refine ⟨8838286450155776447418979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11784381933541035263225305 8838286450155776447418979)
                ·
                  refine ⟨13257429675233664671128469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8838286450155776447418979 13257429675233664671128469)
                  ·
                    refine ⟨621442016026578031459147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13257429675233664671128469 621442016026578031459147)
                    ·
                      rfl

theorem cell22_1815381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1815381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815381 prefixEnd_1815381 := by exact prefixLift 1815381
  have htrace : WordTrace (prefixWord ++ tailWord_1815381) baseStart_1815381 baseEnd_1815381 := by
    simpa [prefixWord, tailWord_1815381, baseEnd_1815381] using wordTrace_append hprefix tailTrace_1815381
  have hstable : (prefixWord ++ tailWord_1815381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815381).length < 2 ^ (prefixWord ++ tailWord_1815381).sum := by decide
  have hdescent : baseEnd_1815381 < baseStart_1815381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815383 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1815383 : Nat := 118140960795 + 1815383 * 2 ^ 59
def prefixEnd_1815383 : Nat := 4983230072969 + 3 ^ 40 * 1815383 * 2
def baseEnd_1815383 : Nat := 621442700667450692909141

theorem tailTrace_1815383 : CollatzResearch.WordTrace tailWord_1815383 prefixEnd_1815383 621442700667450692909141 := by
  unfold tailWord_1815383
  simp only [CollatzResearch.WordTrace]
  refine ⟨66212457582184908577746803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44141638388123272385164535 66212457582184908577746803)
  ·
    refine ⟨99318686373277362866620205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66212457582184908577746803 99318686373277362866620205)
    ·
      refine ⟨37244507389979011074982577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99318686373277362866620205 37244507389979011074982577)
      ·
        refine ⟨27933380542484258306236933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37244507389979011074982577 27933380542484258306236933)
        ·
          refine ⟨5237508851715798432419425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27933380542484258306236933 5237508851715798432419425)
          ·
            refine ⟨3928131638786848824314569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5237508851715798432419425 3928131638786848824314569)
            ·
              refine ⟨2946098729090136618235927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928131638786848824314569 2946098729090136618235927)
              ·
                refine ⟨4419148093635204927353891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946098729090136618235927 4419148093635204927353891)
                ·
                  refine ⟨6628722140452807391030837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419148093635204927353891 6628722140452807391030837)
                  ·
                    refine ⟨621442700667450692909141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6628722140452807391030837 621442700667450692909141)
                    ·
                      rfl

theorem cell22_1815383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1815383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815383 prefixEnd_1815383 := by exact prefixLift 1815383
  have htrace : WordTrace (prefixWord ++ tailWord_1815383) baseStart_1815383 baseEnd_1815383 := by
    simpa [prefixWord, tailWord_1815383, baseEnd_1815383] using wordTrace_append hprefix tailTrace_1815383
  have hstable : (prefixWord ++ tailWord_1815383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815383).length < 2 ^ (prefixWord ++ tailWord_1815383).sum := by decide
  have hdescent : baseEnd_1815383 < baseStart_1815383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815456 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_1815456 : Nat := 118140960795 + 1815456 * 2 ^ 59
def prefixEnd_1815456 : Nat := 4983230072969 + 3 ^ 40 * 1815456 * 2
def baseEnd_1815456 : Nat := 621467690059302835833917

theorem tailTrace_1815456 : CollatzResearch.WordTrace tailWord_1815456 prefixEnd_1815456 621467690059302835833917 := by
  unfold tailWord_1815456
  simp only [CollatzResearch.WordTrace]
  refine ⟨33107560055460221022577111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44143413407280294696769481 33107560055460221022577111)
  ·
    refine ⟨49661340083190331533865667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33107560055460221022577111 49661340083190331533865667)
    ·
      refine ⟨74492010124785497300798501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49661340083190331533865667 74492010124785497300798501)
      ·
        refine ⟨13967251898397280743899719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74492010124785497300798501 13967251898397280743899719)
        ·
          refine ⟨20950877847595921115849579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13967251898397280743899719 20950877847595921115849579)
          ·
            refine ⟨31426316771393881673774369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20950877847595921115849579 31426316771393881673774369)
            ·
              refine ⟨23569737578545411255330777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31426316771393881673774369 23569737578545411255330777)
              ·
                refine ⟨17677303183909058441498083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23569737578545411255330777 17677303183909058441498083)
                ·
                  refine ⟨26515954775863587662247125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17677303183909058441498083 26515954775863587662247125)
                  ·
                    refine ⟨621467690059302835833917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26515954775863587662247125 621467690059302835833917)
                    ·
                      rfl

theorem cell22_1815456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_1815456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815456 prefixEnd_1815456 := by exact prefixLift 1815456
  have htrace : WordTrace (prefixWord ++ tailWord_1815456) baseStart_1815456 baseEnd_1815456 := by
    simpa [prefixWord, tailWord_1815456, baseEnd_1815456] using wordTrace_append hprefix tailTrace_1815456
  have hstable : (prefixWord ++ tailWord_1815456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815456).length < 2 ^ (prefixWord ++ tailWord_1815456).sum := by decide
  have hdescent : baseEnd_1815456 < baseStart_1815456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815458 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1815458 : Nat := 118140960795 + 1815458 * 2 ^ 59
def prefixEnd_1815458 : Nat := 4983230072969 + 3 ^ 40 * 1815458 * 2
def baseEnd_1815458 : Nat := 207156124900058499094637

theorem tailTrace_1815458 : CollatzResearch.WordTrace tailWord_1815458 prefixEnd_1815458 207156124900058499094637 := by
  unfold tailWord_1815458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553798264228299096681757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44143462037942130924484685 16553798264228299096681757)
  ·
    refine ⟨6207674349085612161255659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16553798264228299096681757 6207674349085612161255659)
    ·
      refine ⟨9311511523628418241883489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207674349085612161255659 9311511523628418241883489)
      ·
        refine ⟨6983633642721313681412617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9311511523628418241883489 6983633642721313681412617)
        ·
          refine ⟨5237725232040985261059463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983633642721313681412617 5237725232040985261059463)
          ·
            refine ⟨7856587848061477891589195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237725232040985261059463 7856587848061477891589195)
            ·
              refine ⟨11784881772092216837383793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856587848061477891589195 11784881772092216837383793)
              ·
                refine ⟨8838661329069162628037845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11784881772092216837383793 8838661329069162628037845)
                ·
                  refine ⟨207156124900058499094637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8838661329069162628037845 207156124900058499094637)
                  ·
                    rfl

theorem cell22_1815458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1815458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815458 prefixEnd_1815458 := by exact prefixLift 1815458
  have htrace : WordTrace (prefixWord ++ tailWord_1815458) baseStart_1815458 baseEnd_1815458 := by
    simpa [prefixWord, tailWord_1815458, baseEnd_1815458] using wordTrace_append hprefix tailTrace_1815458
  have hstable : (prefixWord ++ tailWord_1815458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815458).length < 2 ^ (prefixWord ++ tailWord_1815458).sum := by decide
  have hdescent : baseEnd_1815458 < baseStart_1815458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815492 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 5]
def baseStart_1815492 : Nat := 118140960795 + 1815492 * 2 ^ 59
def prefixEnd_1815492 : Nat := 4983230072969 + 3 ^ 40 * 1815492 * 2
def baseEnd_1815492 : Nat := 207160004531670247311269

theorem tailTrace_1815492 : CollatzResearch.WordTrace tailWord_1815492 prefixEnd_1815492 207160004531670247311269 := by
  unfold tailWord_1815492
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108216569395010096732365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44144288759193346795643153 33108216569395010096732365)
  ·
    refine ⟨12415581213523128786274637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33108216569395010096732365 12415581213523128786274637)
    ·
      refine ⟨4655842955071173294852989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12415581213523128786274637 4655842955071173294852989)
      ·
        refine ⟨1745941108151689985569871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4655842955071173294852989 1745941108151689985569871)
        ·
          refine ⟨2618911662227534978354807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745941108151689985569871 2618911662227534978354807)
          ·
            refine ⟨3928367493341302467532211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618911662227534978354807 3928367493341302467532211)
            ·
              refine ⟨5892551240011953701298317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3928367493341302467532211 5892551240011953701298317)
              ·
                refine ⟨2209706715004482637986869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5892551240011953701298317 2209706715004482637986869)
                ·
                  refine ⟨207160004531670247311269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209706715004482637986869 207160004531670247311269)
                  ·
                    rfl

theorem cell22_1815492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_1815492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815492 prefixEnd_1815492 := by exact prefixLift 1815492
  have htrace : WordTrace (prefixWord ++ tailWord_1815492) baseStart_1815492 baseEnd_1815492 := by
    simpa [prefixWord, tailWord_1815492, baseEnd_1815492] using wordTrace_append hprefix tailTrace_1815492
  have hstable : (prefixWord ++ tailWord_1815492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815492).length < 2 ^ (prefixWord ++ tailWord_1815492).sum := by decide
  have hdescent : baseEnd_1815492 < baseStart_1815492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815535 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 2, 3]
def baseStart_1815535 : Nat := 118140960795 + 1815535 * 2 ^ 59
def prefixEnd_1815535 : Nat := 4983230072969 + 3 ^ 40 * 1815535 * 2
def baseEnd_1815535 : Nat := 621494733373772963108675

theorem tailTrace_1815535 : CollatzResearch.WordTrace tailWord_1815535 prefixEnd_1815535 621494733373772963108675 := by
  unfold tailWord_1815535
  simp only [CollatzResearch.WordTrace]
  refine ⟨66218001477634238537280059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44145334318422825691520039 66218001477634238537280059)
  ·
    refine ⟨99327002216451357805920089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66218001477634238537280059 99327002216451357805920089)
    ·
      refine ⟨74495251662338518354440067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99327002216451357805920089 74495251662338518354440067)
      ·
        refine ⟨111742877493507777531660101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74495251662338518354440067 111742877493507777531660101)
        ·
          refine ⟨20951789530032708287186269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111742877493507777531660101 20951789530032708287186269)
          ·
            refine ⟨7856921073762265607694851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20951789530032708287186269 7856921073762265607694851)
            ·
              refine ⟨11785381610643398411542277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856921073762265607694851 11785381610643398411542277)
              ·
                refine ⟨2209759051995637202164177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11785381610643398411542277 2209759051995637202164177)
                ·
                  refine ⟨1657319288996727901623133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209759051995637202164177 1657319288996727901623133)
                  ·
                    refine ⟨621494733373772963108675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657319288996727901623133 621494733373772963108675)
                    ·
                      rfl

theorem cell22_1815535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_1815535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815535 prefixEnd_1815535 := by exact prefixLift 1815535
  have htrace : WordTrace (prefixWord ++ tailWord_1815535) baseStart_1815535 baseEnd_1815535 := by
    simpa [prefixWord, tailWord_1815535, baseEnd_1815535] using wordTrace_append hprefix tailTrace_1815535
  have hstable : (prefixWord ++ tailWord_1815535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815535).length < 2 ^ (prefixWord ++ tailWord_1815535).sum := by decide
  have hdescent : baseEnd_1815535 < baseStart_1815535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815537 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 4]
def baseStart_1815537 : Nat := 118140960795 + 1815537 * 2 ^ 59
def prefixEnd_1815537 : Nat := 4983230072969 + 3 ^ 40 * 1815537 * 2
def baseEnd_1815537 : Nat := 207165139338215208186223

theorem tailTrace_1815537 : CollatzResearch.WordTrace tailWord_1815537 prefixEnd_1815537 207165139338215208186223 := by
  unfold tailWord_1815537
  simp only [CollatzResearch.WordTrace]
  refine ⟨66218074423626992878852865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44145382949084661919235243 66218074423626992878852865)
  ·
    refine ⟨49663555817720244659139649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66218074423626992878852865 49663555817720244659139649)
    ·
      refine ⟨37247666863290183494354737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49663555817720244659139649 37247666863290183494354737)
      ·
        refine ⟨27935750147467637620766053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37247666863290183494354737 27935750147467637620766053)
        ·
          refine ⟨5237953152650182053893635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27935750147467637620766053 5237953152650182053893635)
          ·
            refine ⟨7856929728975273080840453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237953152650182053893635 7856929728975273080840453)
            ·
              refine ⟨1473174324182863702657585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7856929728975273080840453 1473174324182863702657585)
              ·
                refine ⟨1104880743137147776993189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473174324182863702657585 1104880743137147776993189)
                ·
                  refine ⟨207165139338215208186223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104880743137147776993189 207165139338215208186223)
                  ·
                    rfl

theorem cell22_1815537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_1815537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815537 prefixEnd_1815537 := by exact prefixLift 1815537
  have htrace : WordTrace (prefixWord ++ tailWord_1815537) baseStart_1815537 baseEnd_1815537 := by
    simpa [prefixWord, tailWord_1815537, baseEnd_1815537] using wordTrace_append hprefix tailTrace_1815537
  have hstable : (prefixWord ++ tailWord_1815537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815537).length < 2 ^ (prefixWord ++ tailWord_1815537).sum := by decide
  have hdescent : baseEnd_1815537 < baseStart_1815537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815548 : List Nat := [2, 2, 2, 1, 2, 3, 3, 7]
def baseStart_1815548 : Nat := 118140960795 + 1815548 * 2 ^ 59
def prefixEnd_1815548 : Nat := 4983230072969 + 3 ^ 40 * 1815548 * 2
def baseEnd_1815548 : Nat := 69055464837716140281515

theorem tailTrace_1815548 : CollatzResearch.WordTrace tailWord_1815548 prefixEnd_1815548 69055464837716140281515 := by
  unfold tailWord_1815548
  simp only [CollatzResearch.WordTrace]
  refine ⟨33109237813293570878751649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44145650417724761171668865 33109237813293570878751649)
  ·
    refine ⟨24831928359970178159063737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33109237813293570878751649 24831928359970178159063737)
    ·
      refine ⟨18623946269977633619297803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24831928359970178159063737 18623946269977633619297803)
      ·
        refine ⟨27935919404966450428946705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18623946269977633619297803 27935919404966450428946705)
        ·
          refine ⟨20951939553724837821710029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27935919404966450428946705 20951939553724837821710029)
          ·
            refine ⟨7856977332646814183141261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20951939553724837821710029 7856977332646814183141261)
            ·
              refine ⟨2946366499742555318677973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7856977332646814183141261 2946366499742555318677973)
              ·
                refine ⟨69055464837716140281515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2946366499742555318677973 69055464837716140281515)
                ·
                  rfl

theorem cell22_1815548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_1815548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815548 prefixEnd_1815548 := by exact prefixLift 1815548
  have htrace : WordTrace (prefixWord ++ tailWord_1815548) baseStart_1815548 baseEnd_1815548 := by
    simpa [prefixWord, tailWord_1815548, baseEnd_1815548] using wordTrace_append hprefix tailTrace_1815548
  have hstable : (prefixWord ++ tailWord_1815548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815548).length < 2 ^ (prefixWord ++ tailWord_1815548).sum := by decide
  have hdescent : baseEnd_1815548 < baseStart_1815548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815640 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_1815640 : Nat := 118140960795 + 1815640 * 2 ^ 59
def prefixEnd_1815640 : Nat := 4983230072969 + 3 ^ 40 * 1815640 * 2
def baseEnd_1815640 : Nat := 621530677019587689233353

theorem tailTrace_1815640 : CollatzResearch.WordTrace tailWord_1815640 prefixEnd_1815640 621530677019587689233353 := by
  unfold tailWord_1815640
  simp only [CollatzResearch.WordTrace]
  refine ⟨33110915571126920734926187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44147887428169227646568249 33110915571126920734926187)
  ·
    refine ⟨49666373356690381102389281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33110915571126920734926187 49666373356690381102389281)
    ·
      refine ⟨37249780017517785826791961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49666373356690381102389281 37249780017517785826791961)
      ·
        refine ⟨27937335013138339370093971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37249780017517785826791961 27937335013138339370093971)
        ·
          refine ⟨41906002519707509055140957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27937335013138339370093971 41906002519707509055140957)
          ·
            refine ⟨15714750944890315895677859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41906002519707509055140957 15714750944890315895677859)
            ·
              refine ⟨23572126417335473843516789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15714750944890315895677859 23572126417335473843516789)
              ·
                refine ⟨2209886851625200672829699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23572126417335473843516789 2209886851625200672829699)
                ·
                  refine ⟨3314830277437801009244549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209886851625200672829699 3314830277437801009244549)
                  ·
                    refine ⟨621530677019587689233353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3314830277437801009244549 621530677019587689233353)
                    ·
                      rfl

theorem cell22_1815640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_1815640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815640 prefixEnd_1815640 := by exact prefixLift 1815640
  have htrace : WordTrace (prefixWord ++ tailWord_1815640) baseStart_1815640 baseEnd_1815640 := by
    simpa [prefixWord, tailWord_1815640, baseEnd_1815640] using wordTrace_append hprefix tailTrace_1815640
  have hstable : (prefixWord ++ tailWord_1815640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815640).length < 2 ^ (prefixWord ++ tailWord_1815640).sum := by decide
  have hdescent : baseEnd_1815640 < baseStart_1815640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815655 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 6]
def baseStart_1815655 : Nat := 118140960795 + 1815655 * 2 ^ 59
def prefixEnd_1815655 : Nat := 4983230072969 + 3 ^ 40 * 1815655 * 2
def baseEnd_1815655 : Nat := 207178603942044216702769

theorem tailTrace_1815655 : CollatzResearch.WordTrace tailWord_1815655 prefixEnd_1815655 207178603942044216702769 := by
  unfold tailWord_1815655
  simp only [CollatzResearch.WordTrace]
  refine ⟨66222378237199499031648419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44148252158132999354432279 66222378237199499031648419)
  ·
    refine ⟨99333567355799248547472629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66222378237199499031648419 99333567355799248547472629)
    ·
      refine ⟨9312521939606179551325559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99333567355799248547472629 9312521939606179551325559)
      ·
        refine ⟨13968782909409269326988339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312521939606179551325559 13968782909409269326988339)
        ·
          refine ⟨20953174364113903990482509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13968782909409269326988339 20953174364113903990482509)
          ·
            refine ⟨7857440386542713996430941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20953174364113903990482509 7857440386542713996430941)
            ·
              refine ⟨2946540144953517748661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7857440386542713996430941 2946540144953517748661603)
              ·
                refine ⟨4419810217430276622992405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946540144953517748661603 4419810217430276622992405)
                ·
                  refine ⟨207178603942044216702769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4419810217430276622992405 207178603942044216702769)
                  ·
                    rfl

theorem cell22_1815655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 6].length) (baseStart_1815655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815655 prefixEnd_1815655 := by exact prefixLift 1815655
  have htrace : WordTrace (prefixWord ++ tailWord_1815655) baseStart_1815655 baseEnd_1815655 := by
    simpa [prefixWord, tailWord_1815655, baseEnd_1815655] using wordTrace_append hprefix tailTrace_1815655
  have hstable : (prefixWord ++ tailWord_1815655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815655).length < 2 ^ (prefixWord ++ tailWord_1815655).sum := by decide
  have hdescent : baseEnd_1815655 < baseStart_1815655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815683 : List Nat := [1, 1, 1, 3, 3, 2, 1, 10]
def baseStart_1815683 : Nat := 118140960795 + 1815683 * 2 ^ 59
def prefixEnd_1815683 : Nat := 4983230072969 + 3 ^ 40 * 1815683 * 2
def baseEnd_1815683 : Nat := 69060599644261101156469

theorem tailTrace_1815683 : CollatzResearch.WordTrace tailWord_1815683 prefixEnd_1815683 69060599644261101156469 := by
  unfold tailWord_1815683
  simp only [CollatzResearch.WordTrace]
  refine ⟨66223399481098059813667703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44148932987398706542445135 66223399481098059813667703)
  ·
    refine ⟨99335099221647089720501555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66223399481098059813667703 99335099221647089720501555)
    ·
      refine ⟨149002648832470634580752333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99335099221647089720501555 149002648832470634580752333)
      ·
        refine ⟨55875993312176487967782125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149002648832470634580752333 55875993312176487967782125)
        ·
          refine ⟨20953497492066182987918297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55875993312176487967782125 20953497492066182987918297)
          ·
            refine ⟨15715123119049637240938723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20953497492066182987918297 15715123119049637240938723)
            ·
              refine ⟨23572684678574455861408085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15715123119049637240938723 23572684678574455861408085)
              ·
                refine ⟨69060599644261101156469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23572684678574455861408085 69060599644261101156469)
                ·
                  rfl

theorem cell22_1815683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 10].length) (baseStart_1815683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815683 prefixEnd_1815683 := by exact prefixLift 1815683
  have htrace : WordTrace (prefixWord ++ tailWord_1815683) baseStart_1815683 baseEnd_1815683 := by
    simpa [prefixWord, tailWord_1815683, baseEnd_1815683] using wordTrace_append hprefix tailTrace_1815683
  have hstable : (prefixWord ++ tailWord_1815683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815683).length < 2 ^ (prefixWord ++ tailWord_1815683).sum := by decide
  have hdescent : baseEnd_1815683 < baseStart_1815683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815704 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_1815704 : Nat := 118140960795 + 1815704 * 2 ^ 59
def prefixEnd_1815704 : Nat := 4983230072969 + 3 ^ 40 * 1815704 * 2
def baseEnd_1815704 : Nat := 621552585527512855633157

theorem tailTrace_1815704 : CollatzResearch.WordTrace tailWord_1815704 prefixEnd_1815704 621552585527512855633157 := by
  unfold tailWord_1815704
  simp only [CollatzResearch.WordTrace]
  refine ⟨33112082707010990200091083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44149443609347986933454777 33112082707010990200091083)
  ·
    refine ⟨49668124060516485300136625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33112082707010990200091083 49668124060516485300136625)
    ·
      refine ⟨37251093045387363975102469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49668124060516485300136625 37251093045387363975102469)
      ·
        refine ⟨6984579946010130745331713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37251093045387363975102469 6984579946010130745331713)
        ·
          refine ⟨5238434959507598058998785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6984579946010130745331713 5238434959507598058998785)
          ·
            refine ⟨3928826219630698544249089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238434959507598058998785 3928826219630698544249089)
            ·
              refine ⟨2946619664723023908186817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928826219630698544249089 2946619664723023908186817)
              ·
                refine ⟨2209964748542267931140113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946619664723023908186817 2209964748542267931140113)
                ·
                  refine ⟨1657473561406700948355085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209964748542267931140113 1657473561406700948355085)
                  ·
                    refine ⟨621552585527512855633157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657473561406700948355085 621552585527512855633157)
                    ·
                      rfl

theorem cell22_1815704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_1815704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815704 prefixEnd_1815704 := by exact prefixLift 1815704
  have htrace : WordTrace (prefixWord ++ tailWord_1815704) baseStart_1815704 baseEnd_1815704 := by
    simpa [prefixWord, tailWord_1815704, baseEnd_1815704] using wordTrace_append hprefix tailTrace_1815704
  have hstable : (prefixWord ++ tailWord_1815704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815704).length < 2 ^ (prefixWord ++ tailWord_1815704).sum := by decide
  have hdescent : baseEnd_1815704 < baseStart_1815704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815706 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_1815706 : Nat := 118140960795 + 1815706 * 2 ^ 59
def prefixEnd_1815706 : Nat := 4983230072969 + 3 ^ 40 * 1815706 * 2
def baseEnd_1815706 : Nat := 207184423389461839027717

theorem tailTrace_1815706 : CollatzResearch.WordTrace tailWord_1815706 prefixEnd_1815706 207184423389461839027717 := by
  unfold tailWord_1815706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556059590003683685438743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44149492240009823161169981 16556059590003683685438743)
  ·
    refine ⟨24834089385005525528158115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16556059590003683685438743 24834089385005525528158115)
    ·
      refine ⟨37251134077508288292237173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24834089385005525528158115 37251134077508288292237173)
      ·
        refine ⟨3492293819766402027397235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37251134077508288292237173 3492293819766402027397235)
        ·
          refine ⟨5238440729649603041095853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492293819766402027397235 5238440729649603041095853)
          ·
            refine ⟨1964415273618601140410945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5238440729649603041095853 1964415273618601140410945)
            ·
              refine ⟨1473311455213950855308209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964415273618601140410945 1473311455213950855308209)
              ·
                refine ⟨1104983591410463141481157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473311455213950855308209 1104983591410463141481157)
                ·
                  refine ⟨207184423389461839027717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104983591410463141481157 207184423389461839027717)
                  ·
                    rfl

theorem cell22_1815706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_1815706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815706 prefixEnd_1815706 := by exact prefixLift 1815706
  have htrace : WordTrace (prefixWord ++ tailWord_1815706) baseStart_1815706 baseEnd_1815706 := by
    simpa [prefixWord, tailWord_1815706, baseEnd_1815706] using wordTrace_append hprefix tailTrace_1815706
  have hstable : (prefixWord ++ tailWord_1815706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815706).length < 2 ^ (prefixWord ++ tailWord_1815706).sum := by decide
  have hdescent : baseEnd_1815706 < baseStart_1815706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815715 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 7, 3]
def baseStart_1815715 : Nat := 118140960795 + 1815715 * 2 ^ 59
def prefixEnd_1815715 : Nat := 4983230072969 + 3 ^ 40 * 1815715 * 2
def baseEnd_1815715 : Nat := 621556351052312493608123

theorem tailTrace_1815715 : CollatzResearch.WordTrace tailWord_1815715 prefixEnd_1815715 621556351052312493608123 := by
  unfold tailWord_1815715
  simp only [CollatzResearch.WordTrace]
  refine ⟨66224566616982129278832599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44149711077988086185888399 66224566616982129278832599)
  ·
    refine ⟨99336849925473193918248899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66224566616982129278832599 99336849925473193918248899)
    ·
      refine ⟨149005274888209790877373349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99336849925473193918248899 149005274888209790877373349)
      ·
        refine ⟨27938489041539335789507503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149005274888209790877373349 27938489041539335789507503)
        ·
          refine ⟨41907733562309003684261255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27938489041539335789507503 41907733562309003684261255)
          ·
            refine ⟨62861600343463505526391883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41907733562309003684261255 62861600343463505526391883)
            ·
              refine ⟨94292400515195258289587825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62861600343463505526391883 94292400515195258289587825)
              ·
                refine ⟨70719300386396443717190869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94292400515195258289587825 70719300386396443717190869)
                ·
                  refine ⟨1657483602806166649621661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 70719300386396443717190869 1657483602806166649621661)
                  ·
                    refine ⟨621556351052312493608123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657483602806166649621661 621556351052312493608123)
                    ·
                      rfl

theorem cell22_1815715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 3].length) (baseStart_1815715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815715 prefixEnd_1815715 := by exact prefixLift 1815715
  have htrace : WordTrace (prefixWord ++ tailWord_1815715) baseStart_1815715 baseEnd_1815715 := by
    simpa [prefixWord, tailWord_1815715, baseEnd_1815715] using wordTrace_append hprefix tailTrace_1815715
  have hstable : (prefixWord ++ tailWord_1815715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815715).length < 2 ^ (prefixWord ++ tailWord_1815715).sum := by decide
  have hdescent : baseEnd_1815715 < baseStart_1815715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815775 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 5, 4]
def baseStart_1815775 : Nat := 118140960795 + 1815775 * 2 ^ 59
def prefixEnd_1815775 : Nat := 4983230072969 + 3 ^ 40 * 1815775 * 2
def baseEnd_1815775 : Nat := 621576890278492337107939

theorem tailTrace_1815775 : CollatzResearch.WordTrace tailWord_1815775 prefixEnd_1815775 621576890278492337107939 := by
  unfold tailWord_1815775
  simp only [CollatzResearch.WordTrace]
  refine ⟨66226754996764759526016779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44151169997843173017344519 66226754996764759526016779)
  ·
    refine ⟨99340132495147139289025169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66226754996764759526016779 99340132495147139289025169)
    ·
      refine ⟨74505099371360354466768877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99340132495147139289025169 74505099371360354466768877)
      ·
        refine ⟨27939412264260132925038329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74505099371360354466768877 27939412264260132925038329)
        ·
          refine ⟨20954559198195099693778747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27939412264260132925038329 20954559198195099693778747)
          ·
            refine ⟨31431838797292649540668121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20954559198195099693778747 31431838797292649540668121)
            ·
              refine ⟨23573879097969487155501091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31431838797292649540668121 23573879097969487155501091)
              ·
                refine ⟨35360818646954230733251637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23573879097969487155501091 35360818646954230733251637)
                ·
                  refine ⟨3315076748151959131242341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35360818646954230733251637 3315076748151959131242341)
                  ·
                    refine ⟨621576890278492337107939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3315076748151959131242341 621576890278492337107939)
                    ·
                      rfl

theorem cell22_1815775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_1815775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815775 prefixEnd_1815775 := by exact prefixLift 1815775
  have htrace : WordTrace (prefixWord ++ tailWord_1815775) baseStart_1815775 baseEnd_1815775 := by
    simpa [prefixWord, tailWord_1815775, baseEnd_1815775] using wordTrace_append hprefix tailTrace_1815775
  have hstable : (prefixWord ++ tailWord_1815775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815775).length < 2 ^ (prefixWord ++ tailWord_1815775).sum := by decide
  have hdescent : baseEnd_1815775 < baseStart_1815775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815869 : List Nat := [1, 4, 1, 5, 2, 9]
def baseStart_1815869 : Nat := 118140960795 + 1815869 * 2 ^ 59
def prefixEnd_1815869 : Nat := 4983230072969 + 3 ^ 40 * 1815869 * 2
def baseEnd_1815869 : Nat := 7674186029623548459971

theorem tailTrace_1815869 : CollatzResearch.WordTrace tailWord_1815869 prefixEnd_1815869 7674186029623548459971 := by
  unfold tailWord_1815869
  simp only [CollatzResearch.WordTrace]
  refine ⟨66230183458424213579938661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44153455638949475719959107 66230183458424213579938661)
  ·
    refine ⟨12418159398454540046238499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66230183458424213579938661 12418159398454540046238499)
    ·
      refine ⟨18627239097681810069357749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12418159398454540046238499 18627239097681810069357749)
      ·
        refine ⟨1746303665407669694002289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18627239097681810069357749 1746303665407669694002289)
        ·
          refine ⟨1309727749055752270501717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746303665407669694002289 1309727749055752270501717)
          ·
            refine ⟨7674186029623548459971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1309727749055752270501717 7674186029623548459971)
            ·
              rfl

theorem cell22_1815869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 9].length) (baseStart_1815869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815869 prefixEnd_1815869 := by exact prefixLift 1815869
  have htrace : WordTrace (prefixWord ++ tailWord_1815869) baseStart_1815869 baseEnd_1815869 := by
    simpa [prefixWord, tailWord_1815869, baseEnd_1815869] using wordTrace_append hprefix tailTrace_1815869
  have hstable : (prefixWord ++ tailWord_1815869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815869).length < 2 ^ (prefixWord ++ tailWord_1815869).sum := by decide
  have hdescent : baseEnd_1815869 < baseStart_1815869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815897 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 5]
def baseStart_1815897 : Nat := 118140960795 + 1815897 * 2 ^ 59
def prefixEnd_1815897 : Nat := 4983230072969 + 3 ^ 40 * 1815897 * 2
def baseEnd_1815897 : Nat := 207206217790574895185855

theorem tailTrace_1815897 : CollatzResearch.WordTrace tailWord_1815897 prefixEnd_1815897 207206217790574895185855 := by
  unfold tailWord_1815897
  simp only [CollatzResearch.WordTrace]
  refine ⟨66231204702322774361957945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44154136468215182907971963 66231204702322774361957945)
  ·
    refine ⟨49673403526742080771468459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66231204702322774361957945 49673403526742080771468459)
    ·
      refine ⟨74510105290113121157202689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49673403526742080771468459 74510105290113121157202689)
      ·
        refine ⟨55882578967584840867902017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74510105290113121157202689 55882578967584840867902017)
        ·
          refine ⟨41911934225688630650926513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55882578967584840867902017 41911934225688630650926513)
          ·
            refine ⟨31433950669266472988194885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41911934225688630650926513 31433950669266472988194885)
            ·
              refine ⟨5893865750487463685286541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31433950669266472988194885 5893865750487463685286541)
              ·
                refine ⟨2210199656432798881982453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5893865750487463685286541 2210199656432798881982453)
                ·
                  refine ⟨207206217790574895185855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2210199656432798881982453 207206217790574895185855)
                  ·
                    rfl

theorem cell22_1815897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_1815897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815897 prefixEnd_1815897 := by exact prefixLift 1815897
  have htrace : WordTrace (prefixWord ++ tailWord_1815897) baseStart_1815897 baseEnd_1815897 := by
    simpa [prefixWord, tailWord_1815897, baseEnd_1815897] using wordTrace_append hprefix tailTrace_1815897
  have hstable : (prefixWord ++ tailWord_1815897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815897).length < 2 ^ (prefixWord ++ tailWord_1815897).sum := by decide
  have hdescent : baseEnd_1815897 < baseStart_1815897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815989 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1815989 : Nat := 118140960795 + 1815989 * 2 ^ 59
def prefixEnd_1815989 : Nat := 4983230072969 + 3 ^ 40 * 1815989 * 2
def baseEnd_1815989 : Nat := 621650146851867112257283

theorem tailTrace_1815989 : CollatzResearch.WordTrace tailWord_1815989 prefixEnd_1815989 621650146851867112257283 := by
  unfold tailWord_1815989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66234560217989474074307021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44156373478659649382871347 66234560217989474074307021)
  ·
    refine ⟨24837960081746052777865133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66234560217989474074307021 24837960081746052777865133)
    ·
      refine ⟨9314235030654769791699425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24837960081746052777865133 9314235030654769791699425)
      ·
        refine ⟨6985676272991077343774569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9314235030654769791699425 6985676272991077343774569)
        ·
          refine ⟨5239257204743308007830927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6985676272991077343774569 5239257204743308007830927)
          ·
            refine ⟨7858885807114962011746391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239257204743308007830927 7858885807114962011746391)
            ·
              refine ⟨11788328710672443017619587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858885807114962011746391 11788328710672443017619587)
              ·
                refine ⟨17682493066008664526429381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788328710672443017619587 17682493066008664526429381)
                ·
                  refine ⟨3315467449876624598705509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17682493066008664526429381 3315467449876624598705509)
                  ·
                    refine ⟨621650146851867112257283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3315467449876624598705509 621650146851867112257283)
                    ·
                      rfl

theorem cell22_1815989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1815989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815989 prefixEnd_1815989 := by exact prefixLift 1815989
  have htrace : WordTrace (prefixWord ++ tailWord_1815989) baseStart_1815989 baseEnd_1815989 := by
    simpa [prefixWord, tailWord_1815989, baseEnd_1815989] using wordTrace_append hprefix tailTrace_1815989
  have hstable : (prefixWord ++ tailWord_1815989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815989).length < 2 ^ (prefixWord ++ tailWord_1815989).sum := by decide
  have hdescent : baseEnd_1815989 < baseStart_1815989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815993 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 4]
def baseStart_1815993 : Nat := 118140960795 + 1815993 * 2 ^ 59
def prefixEnd_1815993 : Nat := 4983230072969 + 3 ^ 40 * 1815993 * 2
def baseEnd_1815993 : Nat := 207217172044537478385757

theorem tailTrace_1815993 : CollatzResearch.WordTrace tailWord_1815993 prefixEnd_1815993 207217172044537478385757 := by
  unfold tailWord_1815993
  simp only [CollatzResearch.WordTrace]
  refine ⟨66234706109974982757452633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44156470739983321838301755 66234706109974982757452633)
  ·
    refine ⟨49676029582481237068089475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66234706109974982757452633 49676029582481237068089475)
    ·
      refine ⟨74514044373721855602134213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49676029582481237068089475 74514044373721855602134213)
      ·
        refine ⟨13971383320072847925400165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74514044373721855602134213 13971383320072847925400165)
        ·
          refine ⟨2619634372513658986012531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13971383320072847925400165 2619634372513658986012531)
          ·
            refine ⟨3929451558770488479018797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619634372513658986012531 3929451558770488479018797)
            ·
              refine ⟨1473544334538933179632049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3929451558770488479018797 1473544334538933179632049)
              ·
                refine ⟨1105158250904199884724037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473544334538933179632049 1105158250904199884724037)
                ·
                  refine ⟨207217172044537478385757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105158250904199884724037 207217172044537478385757)
                  ·
                    rfl

theorem cell22_1815993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_1815993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1815993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1815993 prefixEnd_1815993 := by exact prefixLift 1815993
  have htrace : WordTrace (prefixWord ++ tailWord_1815993) baseStart_1815993 baseEnd_1815993 := by
    simpa [prefixWord, tailWord_1815993, baseEnd_1815993] using wordTrace_append hprefix tailTrace_1815993
  have hstable : (prefixWord ++ tailWord_1815993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815993).length < 2 ^ (prefixWord ++ tailWord_1815993).sum := by decide
  have hdescent : baseEnd_1815993 < baseStart_1815993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816004 : List Nat := [2, 3, 3, 2, 1, 1, 1, 9]
def baseStart_1816004 : Nat := 118140960795 + 1816004 * 2 ^ 59
def prefixEnd_1816004 : Nat := 4983230072969 + 3 ^ 40 * 1816004 * 2
def baseEnd_1816004 : Nat := 69072809073156897014693

theorem tailTrace_1816004 : CollatzResearch.WordTrace tailWord_1816004 prefixEnd_1816004 69072809073156897014693 := by
  unfold tailWord_1816004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33117553656467565818051533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44156738208623421090735377 33117553656467565818051533)
  ·
    refine ⟨12419082621175337181769325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33117553656467565818051533 12419082621175337181769325)
    ·
      refine ⟨4657155982940751443163497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12419082621175337181769325 4657155982940751443163497)
      ·
        refine ⟨3492866987205563582372623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4657155982940751443163497 3492866987205563582372623)
        ·
          refine ⟨5239300480808345373558935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492866987205563582372623 5239300480808345373558935)
          ·
            refine ⟨7858950721212518060338403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239300480808345373558935 7858950721212518060338403)
            ·
              refine ⟨11788426081818777090507605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858950721212518060338403 11788426081818777090507605)
              ·
                refine ⟨69072809073156897014693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11788426081818777090507605 69072809073156897014693)
                ·
                  rfl

theorem cell22_1816004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_1816004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816004 prefixEnd_1816004 := by exact prefixLift 1816004
  have htrace : WordTrace (prefixWord ++ tailWord_1816004) baseStart_1816004 baseEnd_1816004 := by
    simpa [prefixWord, tailWord_1816004, baseEnd_1816004] using wordTrace_append hprefix tailTrace_1816004
  have hstable : (prefixWord ++ tailWord_1816004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816004).length < 2 ^ (prefixWord ++ tailWord_1816004).sum := by decide
  have hdescent : baseEnd_1816004 < baseStart_1816004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816032 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_1816032 : Nat := 118140960795 + 1816032 * 2 ^ 59
def prefixEnd_1816032 : Nat := 4983230072969 + 3 ^ 40 * 1816032 * 2
def baseEnd_1816032 : Nat := 207221622210209777810717

theorem tailTrace_1816032 : CollatzResearch.WordTrace tailWord_1816032 prefixEnd_1816032 207221622210209777810717 := by
  unfold tailWord_1816032
  simp only [CollatzResearch.WordTrace]
  refine ⟨33118064278416846209061175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44157419037889128278748233 33118064278416846209061175)
  ·
    refine ⟨49677096417625269313591763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33118064278416846209061175 49677096417625269313591763)
    ·
      refine ⟨74515644626437903970387645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49677096417625269313591763 74515644626437903970387645)
      ·
        refine ⟨27943366734914213988895367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74515644626437903970387645 27943366734914213988895367)
        ·
          refine ⟨41915050102371320983343051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27943366734914213988895367 41915050102371320983343051)
          ·
            refine ⟨62872575153556981475014577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41915050102371320983343051 62872575153556981475014577)
            ·
              refine ⟨47154431365167736106260933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62872575153556981475014577 47154431365167736106260933)
              ·
                refine ⟨8841455880968950519923925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47154431365167736106260933 8841455880968950519923925)
                ·
                  refine ⟨207221622210209777810717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8841455880968950519923925 207221622210209777810717)
                  ·
                    rfl

theorem cell22_1816032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_1816032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816032 prefixEnd_1816032 := by exact prefixLift 1816032
  have htrace : WordTrace (prefixWord ++ tailWord_1816032) baseStart_1816032 baseEnd_1816032 := by
    simpa [prefixWord, tailWord_1816032, baseEnd_1816032] using wordTrace_append hprefix tailTrace_1816032
  have hstable : (prefixWord ++ tailWord_1816032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816032).length < 2 ^ (prefixWord ++ tailWord_1816032).sum := by decide
  have hdescent : baseEnd_1816032 < baseStart_1816032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816049 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 5]
def baseStart_1816049 : Nat := 118140960795 + 1816049 * 2 ^ 59
def prefixEnd_1816049 : Nat := 4983230072969 + 3 ^ 40 * 1816049 * 2
def baseEnd_1816049 : Nat := 207223562026015651919033

theorem tailTrace_1816049 : CollatzResearch.WordTrace tailWord_1816049 prefixEnd_1816049 207223562026015651919033 := by
  unfold tailWord_1816049
  simp only [CollatzResearch.WordTrace]
  refine ⟨66236748597772104321491201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44157832398514736214327467 66236748597772104321491201)
  ·
    refine ⟨49677561448329078241118401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66236748597772104321491201 49677561448329078241118401)
    ·
      refine ⟨37258171086246808680838801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49677561448329078241118401 37258171086246808680838801)
      ·
        refine ⟨27943628314685106510629101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37258171086246808680838801 27943628314685106510629101)
        ·
          refine ⟨10478860618006914941485913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27943628314685106510629101 10478860618006914941485913)
          ·
            refine ⟨7859145463505186206114435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10478860618006914941485913 7859145463505186206114435)
            ·
              refine ⟨11788718195257779309171653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859145463505186206114435 11788718195257779309171653)
              ·
                refine ⟨2210384661610833620469685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11788718195257779309171653 2210384661610833620469685)
                ·
                  refine ⟨207223562026015651919033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2210384661610833620469685 207223562026015651919033)
                  ·
                    rfl

theorem cell22_1816049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_1816049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816049 prefixEnd_1816049 := by exact prefixLift 1816049
  have htrace : WordTrace (prefixWord ++ tailWord_1816049) baseStart_1816049 baseEnd_1816049 := by
    simpa [prefixWord, tailWord_1816049, baseEnd_1816049] using wordTrace_append hprefix tailTrace_1816049
  have hstable : (prefixWord ++ tailWord_1816049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816049).length < 2 ^ (prefixWord ++ tailWord_1816049).sum := by decide
  have hdescent : baseEnd_1816049 < baseStart_1816049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816156 : List Nat := [2, 2, 4, 1, 2, 3, 8]
def baseStart_1816156 : Nat := 118140960795 + 1816156 * 2 ^ 59
def prefixEnd_1816156 : Nat := 4983230072969 + 3 ^ 40 * 1816156 * 2
def baseEnd_1816156 : Nat := 23026196828323494197473

theorem tailTrace_1816156 : CollatzResearch.WordTrace tailWord_1816156 prefixEnd_1816156 23026196828323494197473 := by
  unfold tailWord_1816156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33120325604192230797818161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44160434138922974397090881 33120325604192230797818161)
  ·
    refine ⟨24840244203144173098363621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33120325604192230797818161 24840244203144173098363621)
    ·
      refine ⟨4657545788089532455943179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24840244203144173098363621 4657545788089532455943179)
      ·
        refine ⟨6986318682134298683914769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657545788089532455943179 6986318682134298683914769)
        ·
          refine ⟨5239739011600724012936077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6986318682134298683914769 5239739011600724012936077)
          ·
            refine ⟨1964902129350271504851029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5239739011600724012936077 1964902129350271504851029)
            ·
              refine ⟨23026196828323494197473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1964902129350271504851029 23026196828323494197473)
              ·
                rfl

theorem cell22_1816156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 8].length) (baseStart_1816156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816156 prefixEnd_1816156 := by exact prefixLift 1816156
  have htrace : WordTrace (prefixWord ++ tailWord_1816156) baseStart_1816156 baseEnd_1816156 := by
    simpa [prefixWord, tailWord_1816156, baseEnd_1816156] using wordTrace_append hprefix tailTrace_1816156
  have hstable : (prefixWord ++ tailWord_1816156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816156).length < 2 ^ (prefixWord ++ tailWord_1816156).sum := by decide
  have hdescent : baseEnd_1816156 < baseStart_1816156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816222 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1816222 : Nat := 118140960795 + 1816222 * 2 ^ 59
def prefixEnd_1816222 : Nat := 4983230072969 + 3 ^ 40 * 1816222 * 2
def baseEnd_1816222 : Nat := 621729907513532171181569

theorem tailTrace_1816222 : CollatzResearch.WordTrace tailWord_1816222 prefixEnd_1816222 621729907513532171181569 := by
  unfold tailWord_1816222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280382303268169358442365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44162038950763569911692613 8280382303268169358442365)
  ·
    refine ⟨3105143363725563509415887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8280382303268169358442365 3105143363725563509415887)
    ·
      refine ⟨4657715045588345264123831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105143363725563509415887 4657715045588345264123831)
      ·
        refine ⟨6986572568382517896185747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657715045588345264123831 6986572568382517896185747)
        ·
          refine ⟨10479858852573776844278621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986572568382517896185747 10479858852573776844278621)
          ·
            refine ⟨3929947069715166316604483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10479858852573776844278621 3929947069715166316604483)
            ·
              refine ⟨5894920604572749474906725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929947069715166316604483 5894920604572749474906725)
              ·
                refine ⟨1105297613357390526545011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5894920604572749474906725 1105297613357390526545011)
                ·
                  refine ⟨1657946420036085789817517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105297613357390526545011 1657946420036085789817517)
                  ·
                    refine ⟨621729907513532171181569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657946420036085789817517 621729907513532171181569)
                    ·
                      rfl

theorem cell22_1816222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1816222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816222 prefixEnd_1816222 := by exact prefixLift 1816222
  have htrace : WordTrace (prefixWord ++ tailWord_1816222) baseStart_1816222 baseEnd_1816222 := by
    simpa [prefixWord, tailWord_1816222, baseEnd_1816222] using wordTrace_append hprefix tailTrace_1816222
  have hstable : (prefixWord ++ tailWord_1816222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816222).length < 2 ^ (prefixWord ++ tailWord_1816222).sum := by decide
  have hdescent : baseEnd_1816222 < baseStart_1816222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816261 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_1816261 : Nat := 118140960795 + 1816261 * 2 ^ 59
def prefixEnd_1816261 : Nat := 4983230072969 + 3 ^ 40 * 1816261 * 2
def baseEnd_1816261 : Nat := 621743258010549069456449

theorem tailTrace_1816261 : CollatzResearch.WordTrace tailWord_1816261 prefixEnd_1816261 621743258010549069456449 := by
  unfold tailWord_1816261
  simp only [CollatzResearch.WordTrace]
  refine ⟨66244480873004064528208637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44162987248669376352139091 66244480873004064528208637)
  ·
    refine ⟨24841680327376524198078239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66244480873004064528208637 24841680327376524198078239)
    ·
      refine ⟨37262520491064786297117359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24841680327376524198078239 37262520491064786297117359)
      ·
        refine ⟨55893780736597179445676039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37262520491064786297117359 55893780736597179445676039)
        ·
          refine ⟨83840671104895769168514059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55893780736597179445676039 83840671104895769168514059)
          ·
            refine ⟨125761006657343653752771089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83840671104895769168514059 125761006657343653752771089)
            ·
              refine ⟨94320754993007740314578317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125761006657343653752771089 94320754993007740314578317)
              ·
                refine ⟨35370283122377902617966869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94320754993007740314578317 35370283122377902617966869)
                ·
                  refine ⟨1657982021361464185217197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35370283122377902617966869 1657982021361464185217197)
                  ·
                    refine ⟨621743258010549069456449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1657982021361464185217197 621743258010549069456449)
                    ·
                      rfl

theorem cell22_1816261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_1816261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816261 prefixEnd_1816261 := by exact prefixLift 1816261
  have htrace : WordTrace (prefixWord ++ tailWord_1816261) baseStart_1816261 baseEnd_1816261 := by
    simpa [prefixWord, tailWord_1816261, baseEnd_1816261] using wordTrace_append hprefix tailTrace_1816261
  have hstable : (prefixWord ++ tailWord_1816261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816261).length < 2 ^ (prefixWord ++ tailWord_1816261).sum := by decide
  have hdescent : baseEnd_1816261 < baseStart_1816261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816263 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 4]
def baseStart_1816263 : Nat := 118140960795 + 1816263 * 2 ^ 59
def prefixEnd_1816263 : Nat := 4983230072969 + 3 ^ 40 * 1816263 * 2
def baseEnd_1816263 : Nat := 207247980883807243635481

theorem tailTrace_1816263 : CollatzResearch.WordTrace tailWord_1816263 prefixEnd_1816263 207247980883807243635481 := by
  unfold tailWord_1816263
  simp only [CollatzResearch.WordTrace]
  refine ⟨66244553818996818869781443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44163035879331212579854295 66244553818996818869781443)
  ·
    refine ⟨99366830728495228304672165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66244553818996818869781443 99366830728495228304672165)
    ·
      refine ⟨18631280761592855307126031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99366830728495228304672165 18631280761592855307126031)
      ·
        refine ⟨27946921142389282960689047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18631280761592855307126031 27946921142389282960689047)
        ·
          refine ⟨41920381713583924441033571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27946921142389282960689047 41920381713583924441033571)
          ·
            refine ⟨62880572570375886661550357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41920381713583924441033571 62880572570375886661550357)
            ·
              refine ⟨2947526839236369687260173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62880572570375886661550357 2947526839236369687260173)
              ·
                refine ⟨1105322564713638632722565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2947526839236369687260173 1105322564713638632722565)
                ·
                  refine ⟨207247980883807243635481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105322564713638632722565 207247980883807243635481)
                  ·
                    rfl

theorem cell22_1816263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 4].length) (baseStart_1816263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816263 prefixEnd_1816263 := by exact prefixLift 1816263
  have htrace : WordTrace (prefixWord ++ tailWord_1816263) baseStart_1816263 baseEnd_1816263 := by
    simpa [prefixWord, tailWord_1816263, baseEnd_1816263] using wordTrace_append hprefix tailTrace_1816263
  have hstable : (prefixWord ++ tailWord_1816263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816263).length < 2 ^ (prefixWord ++ tailWord_1816263).sum := by decide
  have hdescent : baseEnd_1816263 < baseStart_1816263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816306 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1816306 : Nat := 118140960795 + 1816306 * 2 ^ 59
def prefixEnd_1816306 : Nat := 4983230072969 + 3 ^ 40 * 1816306 * 2
def baseEnd_1816306 : Nat := 621758662430183952081311

theorem tailTrace_1816306 : CollatzResearch.WordTrace tailWord_1816306 prefixEnd_1816306 621758662430183952081311 := by
  unfold tailWord_1816306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16561530539460259303399193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44164081438560691475731181 16561530539460259303399193)
  ·
    refine ⟨12421147904595194477549395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16561530539460259303399193 12421147904595194477549395)
    ·
      refine ⟨18631721856892791716324093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12421147904595194477549395 18631721856892791716324093)
      ·
        refine ⟨6986895696334796893621535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18631721856892791716324093 6986895696334796893621535)
        ·
          refine ⟨10480343544502195340432303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986895696334796893621535 10480343544502195340432303)
          ·
            refine ⟨15720515316753293010648455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480343544502195340432303 15720515316753293010648455)
            ·
              refine ⟨23580772975129939515972683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15720515316753293010648455 23580772975129939515972683)
              ·
                refine ⟨35371159462694909273959025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23580772975129939515972683 35371159462694909273959025)
                ·
                  refine ⟨26528369597021181955469269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35371159462694909273959025 26528369597021181955469269)
                  ·
                    refine ⟨621758662430183952081311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26528369597021181955469269 621758662430183952081311)
                    ·
                      rfl

theorem cell22_1816306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1816306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816306 prefixEnd_1816306 := by exact prefixLift 1816306
  have htrace : WordTrace (prefixWord ++ tailWord_1816306) baseStart_1816306 baseEnd_1816306 := by
    simpa [prefixWord, tailWord_1816306, baseEnd_1816306] using wordTrace_append hprefix tailTrace_1816306
  have hstable : (prefixWord ++ tailWord_1816306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816306).length < 2 ^ (prefixWord ++ tailWord_1816306).sum := by decide
  have hdescent : baseEnd_1816306 < baseStart_1816306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816351 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_1816351 : Nat := 118140960795 + 1816351 * 2 ^ 59
def prefixEnd_1816351 : Nat := 4983230072969 + 3 ^ 40 * 1816351 * 2
def baseEnd_1816351 : Nat := 621774066849818834706173

theorem tailTrace_1816351 : CollatzResearch.WordTrace tailWord_1816351 prefixEnd_1816351 621774066849818834706173 := by
  unfold tailWord_1816351
  simp only [CollatzResearch.WordTrace]
  refine ⟨66247763442678009898984907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44165175628452006599323271 66247763442678009898984907)
  ·
    refine ⟨99371645164017014848477361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66247763442678009898984907 99371645164017014848477361)
    ·
      refine ⟨74528733873012761136358021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99371645164017014848477361 74528733873012761136358021)
      ·
        refine ⟨13974137601189892713067129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74528733873012761136358021 13974137601189892713067129)
        ·
          refine ⟨10480603200892419534800347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13974137601189892713067129 10480603200892419534800347)
          ·
            refine ⟨15720904801338629302200521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480603200892419534800347 15720904801338629302200521)
            ·
              refine ⟨11790678601003971976650391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15720904801338629302200521 11790678601003971976650391)
              ·
                refine ⟨17686017901505957964975587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11790678601003971976650391 17686017901505957964975587)
                ·
                  refine ⟨26529026852258936947463381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17686017901505957964975587 26529026852258936947463381)
                  ·
                    refine ⟨621774066849818834706173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26529026852258936947463381 621774066849818834706173)
                    ·
                      rfl

theorem cell22_1816351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_1816351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816351 prefixEnd_1816351 := by exact prefixLift 1816351
  have htrace : WordTrace (prefixWord ++ tailWord_1816351) baseStart_1816351 baseEnd_1816351 := by
    simpa [prefixWord, tailWord_1816351, baseEnd_1816351] using wordTrace_append hprefix tailTrace_1816351
  have hstable : (prefixWord ++ tailWord_1816351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816351).length < 2 ^ (prefixWord ++ tailWord_1816351).sum := by decide
  have hdescent : baseEnd_1816351 < baseStart_1816351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816353 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 5]
def baseStart_1816353 : Nat := 118140960795 + 1816353 * 2 ^ 59
def prefixEnd_1816353 : Nat := 4983230072969 + 3 ^ 40 * 1816353 * 2
def baseEnd_1816353 : Nat := 207258250496897165385389

theorem tailTrace_1816353 : CollatzResearch.WordTrace tailWord_1816353 prefixEnd_1816353 207258250496897165385389 := by
  unfold tailWord_1816353
  simp only [CollatzResearch.WordTrace]
  refine ⟨66247836388670764240557713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44165224259113842827038475 66247836388670764240557713)
  ·
    refine ⟨49685877291503073180418285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66247836388670764240557713 49685877291503073180418285)
    ·
      refine ⟨18632203984313652442656857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49685877291503073180418285 18632203984313652442656857)
      ·
        refine ⟨13974152988235239331992643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18632203984313652442656857 13974152988235239331992643)
        ·
          refine ⟨20961229482352858997988965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13974152988235239331992643 20961229482352858997988965)
          ·
            refine ⟨3930230527941161062122931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20961229482352858997988965 3930230527941161062122931)
            ·
              refine ⟨5895345791911741593184397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930230527941161062122931 5895345791911741593184397)
              ·
                refine ⟨2210754671966903097444149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5895345791911741593184397 2210754671966903097444149)
                ·
                  refine ⟨207258250496897165385389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2210754671966903097444149 207258250496897165385389)
                  ·
                    rfl

theorem cell22_1816353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_1816353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816353 prefixEnd_1816353 := by exact prefixLift 1816353
  have htrace : WordTrace (prefixWord ++ tailWord_1816353) baseStart_1816353 baseEnd_1816353 := by
    simpa [prefixWord, tailWord_1816353, baseEnd_1816353] using wordTrace_append hprefix tailTrace_1816353
  have hstable : (prefixWord ++ tailWord_1816353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816353).length < 2 ^ (prefixWord ++ tailWord_1816353).sum := by decide
  have hdescent : baseEnd_1816353 < baseStart_1816353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816428 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_1816428 : Nat := 118140960795 + 1816428 * 2 ^ 59
def prefixEnd_1816428 : Nat := 4983230072969 + 3 ^ 40 * 1816428 * 2
def baseEnd_1816428 : Nat := 621800425523416300530937

theorem tailTrace_1816428 : CollatzResearch.WordTrace tailWord_1816428 prefixEnd_1816428 621800425523416300530937 := by
  unfold tailWord_1816428
  simp only [CollatzResearch.WordTrace]
  refine ⟨33125285931699526024768969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44167047908932701366358625 33125285931699526024768969)
  ·
    refine ⟨24843964448774644518576727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33125285931699526024768969 24843964448774644518576727)
    ·
      refine ⟨37265946673161966777865091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24843964448774644518576727 37265946673161966777865091)
      ·
        refine ⟨55898920009742950166797637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37265946673161966777865091 55898920009742950166797637)
        ·
          refine ⟨10481047501826803156274557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55898920009742950166797637 10481047501826803156274557)
          ·
            refine ⟨3930392813185051183602959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10481047501826803156274557 3930392813185051183602959)
            ·
              refine ⟨5895589219777576775404439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930392813185051183602959 5895589219777576775404439)
              ·
                refine ⟨8843383829666365163106659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895589219777576775404439 8843383829666365163106659)
                ·
                  refine ⟨13265075744499547744659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843383829666365163106659 13265075744499547744659989)
                  ·
                    refine ⟨621800425523416300530937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13265075744499547744659989 621800425523416300530937)
                    ·
                      rfl

theorem cell22_1816428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_1816428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816428 prefixEnd_1816428 := by exact prefixLift 1816428
  have htrace : WordTrace (prefixWord ++ tailWord_1816428) baseStart_1816428 baseEnd_1816428 := by
    simpa [prefixWord, tailWord_1816428, baseEnd_1816428] using wordTrace_append hprefix tailTrace_1816428
  have hstable : (prefixWord ++ tailWord_1816428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816428).length < 2 ^ (prefixWord ++ tailWord_1816428).sum := by decide
  have hdescent : baseEnd_1816428 < baseStart_1816428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816430 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1816430 : Nat := 118140960795 + 1816430 * 2 ^ 59
def prefixEnd_1816430 : Nat := 4983230072969 + 3 ^ 40 * 1816430 * 2
def baseEnd_1816430 : Nat := 621801110164288961980931

theorem tailTrace_1816430 : CollatzResearch.WordTrace tailWord_1816430 prefixEnd_1816430 621801110164288961980931 := by
  unfold tailWord_1816430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281330601173975798888843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44167096539594537594073829 8281330601173975798888843)
  ·
    refine ⟨12421995901760963698333265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8281330601173975798888843 12421995901760963698333265)
    ·
      refine ⟨9316496926320722773749949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12421995901760963698333265 9316496926320722773749949)
      ·
        refine ⟨3493686347370271040156231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9316496926320722773749949 3493686347370271040156231)
        ·
          refine ⟨5240529521055406560234347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493686347370271040156231 5240529521055406560234347)
          ·
            refine ⟨7860794281583109840351521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240529521055406560234347 7860794281583109840351521)
            ·
              refine ⟨5895595711187332380263641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7860794281583109840351521 5895595711187332380263641)
              ·
                refine ⟨4421696783390499285197731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5895595711187332380263641 4421696783390499285197731)
                ·
                  refine ⟨6632545175085748927796597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421696783390499285197731 6632545175085748927796597)
                  ·
                    refine ⟨621801110164288961980931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6632545175085748927796597 621801110164288961980931)
                    ·
                      rfl

theorem cell22_1816430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1816430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816430 prefixEnd_1816430 := by exact prefixLift 1816430
  have htrace : WordTrace (prefixWord ++ tailWord_1816430) baseStart_1816430 baseEnd_1816430 := by
    simpa [prefixWord, tailWord_1816430, baseEnd_1816430] using wordTrace_append hprefix tailTrace_1816430
  have hstable : (prefixWord ++ tailWord_1816430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816430).length < 2 ^ (prefixWord ++ tailWord_1816430).sum := by decide
  have hdescent : baseEnd_1816430 < baseStart_1816430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816494 : List Nat := [4, 1, 5, 1, 1, 2, 8]
def baseStart_1816494 : Nat := 118140960795 + 1816494 * 2 ^ 59
def prefixEnd_1816494 : Nat := 4983230072969 + 3 ^ 40 * 1816494 * 2
def baseEnd_1816494 : Nat := 23030482173044967717805

theorem tailTrace_1816494 : CollatzResearch.WordTrace tailWord_1816494 prefixEnd_1816494 23030482173044967717805 := by
  unfold tailWord_1816494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281622385144993165180067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44168652720773296880960357 8281622385144993165180067)
  ·
    refine ⟨12422433577717489747770101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8281622385144993165180067 12422433577717489747770101)
    ·
      refine ⟨1164603147911014663853447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12422433577717489747770101 1164603147911014663853447)
      ·
        refine ⟨1746904721866521995780171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164603147911014663853447 1746904721866521995780171)
        ·
          refine ⟨2620357082799782993670257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746904721866521995780171 2620357082799782993670257)
          ·
            refine ⟨1965267812099837245252693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620357082799782993670257 1965267812099837245252693)
            ·
              refine ⟨23030482173044967717805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1965267812099837245252693 23030482173044967717805)
              ·
                rfl

theorem cell22_1816494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 8].length) (baseStart_1816494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816494 prefixEnd_1816494 := by exact prefixLift 1816494
  have htrace : WordTrace (prefixWord ++ tailWord_1816494) baseStart_1816494 baseEnd_1816494 := by
    simpa [prefixWord, tailWord_1816494, baseEnd_1816494] using wordTrace_append hprefix tailTrace_1816494
  have hstable : (prefixWord ++ tailWord_1816494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816494).length < 2 ^ (prefixWord ++ tailWord_1816494).sum := by decide
  have hdescent : baseEnd_1816494 < baseStart_1816494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816661 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_1816661 : Nat := 118140960795 + 1816661 * 2 ^ 59
def prefixEnd_1816661 : Nat := 4983230072969 + 3 ^ 40 * 1816661 * 2
def baseEnd_1816661 : Nat := 621880186185081359455223

theorem tailTrace_1816661 : CollatzResearch.WordTrace tailWord_1816661 prefixEnd_1816661 621880186185081359455223 := by
  unfold tailWord_1816661
  simp only [CollatzResearch.WordTrace]
  refine ⟨66259070071554932842769837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44172713381036621895179891 66259070071554932842769837)
  ·
    refine ⟨24847151276833099816038689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66259070071554932842769837 24847151276833099816038689)
    ·
      refine ⟨18635363457624824862029017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24847151276833099816038689 18635363457624824862029017)
      ·
        refine ⟨13976522593218618646521763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18635363457624824862029017 13976522593218618646521763)
        ·
          refine ⟨20964783889827927969782645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13976522593218618646521763 20964783889827927969782645)
          ·
            refine ⟨1965448489671368247167123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20964783889827927969782645 1965448489671368247167123)
            ·
              refine ⟨2948172734507052370750685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965448489671368247167123 2948172734507052370750685)
              ·
                refine ⟨1105564775440144639031507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2948172734507052370750685 1105564775440144639031507)
                ·
                  refine ⟨1658347163160216958547261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105564775440144639031507 1658347163160216958547261)
                  ·
                    refine ⟨621880186185081359455223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1658347163160216958547261 621880186185081359455223)
                    ·
                      rfl

theorem cell22_1816661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_1816661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816661 prefixEnd_1816661 := by exact prefixLift 1816661
  have htrace : WordTrace (prefixWord ++ tailWord_1816661) baseStart_1816661 baseEnd_1816661 := by
    simpa [prefixWord, tailWord_1816661, baseEnd_1816661] using wordTrace_append hprefix tailTrace_1816661
  have hstable : (prefixWord ++ tailWord_1816661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816661).length < 2 ^ (prefixWord ++ tailWord_1816661).sum := by decide
  have hdescent : baseEnd_1816661 < baseStart_1816661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816730 : List Nat := [3, 1, 1, 5, 12]
def baseStart_1816730 : Nat := 118140960795 + 1816730 * 2 ^ 59
def prefixEnd_1816730 : Nat := 4983230072969 + 3 ^ 40 * 1816730 * 2
def baseEnd_1816730 : Nat := 2559274923025465759177

theorem tailTrace_1816730 : CollatzResearch.WordTrace tailWord_1816730 prefixEnd_1816730 2559274923025465759177 := by
  unfold tailWord_1816730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565396677076239406757911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44174391138869971751354429 16565396677076239406757911)
  ·
    refine ⟨24848095015614359110136867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16565396677076239406757911 24848095015614359110136867)
    ·
      refine ⟨37272142523421538665205301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24848095015614359110136867 37272142523421538665205301)
      ·
        refine ⟨3494263361570769249862997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37272142523421538665205301 3494263361570769249862997)
        ·
          refine ⟨2559274923025465759177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3494263361570769249862997 2559274923025465759177)
          ·
            rfl

theorem cell22_1816730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 12].length) (baseStart_1816730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816730 prefixEnd_1816730 := by exact prefixLift 1816730
  have htrace : WordTrace (prefixWord ++ tailWord_1816730) baseStart_1816730 baseEnd_1816730 := by
    simpa [prefixWord, tailWord_1816730, baseEnd_1816730] using wordTrace_append hprefix tailTrace_1816730
  have hstable : (prefixWord ++ tailWord_1816730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816730).length < 2 ^ (prefixWord ++ tailWord_1816730).sum := by decide
  have hdescent : baseEnd_1816730 < baseStart_1816730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816732 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1816732 : Nat := 118140960795 + 1816732 * 2 ^ 59
def prefixEnd_1816732 : Nat := 4983230072969 + 3 ^ 40 * 1816732 * 2
def baseEnd_1816732 : Nat := 621904490936060840930005

theorem tailTrace_1816732 : CollatzResearch.WordTrace tailWord_1816732 prefixEnd_1816732 621904490936060840930005 := by
  unfold tailWord_1816732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33130829827148855984302225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44174439769531807979069633 33130829827148855984302225)
  ·
    refine ⟨24848122370361641988226669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33130829827148855984302225 24848122370361641988226669)
    ·
      refine ⟨9318045888885615745585001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24848122370361641988226669 9318045888885615745585001)
      ·
        refine ⟨6988534416664211809188751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9318045888885615745585001 6988534416664211809188751)
        ·
          refine ⟨10482801624996317713783127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988534416664211809188751 10482801624996317713783127)
          ·
            refine ⟨15724202437494476570674691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482801624996317713783127 15724202437494476570674691)
            ·
              refine ⟨23586303656241714856012037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724202437494476570674691 23586303656241714856012037)
              ·
                refine ⟨4422431935545321535502257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23586303656241714856012037 4422431935545321535502257)
                ·
                  refine ⟨3316823951658991151626693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422431935545321535502257 3316823951658991151626693)
                  ·
                    refine ⟨621904490936060840930005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3316823951658991151626693 621904490936060840930005)
                    ·
                      rfl

theorem cell22_1816732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1816732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816732 prefixEnd_1816732 := by exact prefixLift 1816732
  have htrace : WordTrace (prefixWord ++ tailWord_1816732) baseStart_1816732 baseEnd_1816732 := by
    simpa [prefixWord, tailWord_1816732, baseEnd_1816732] using wordTrace_append hprefix tailTrace_1816732
  have hstable : (prefixWord ++ tailWord_1816732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816732).length < 2 ^ (prefixWord ++ tailWord_1816732).sum := by decide
  have hdescent : baseEnd_1816732 < baseStart_1816732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816736 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 4]
def baseStart_1816736 : Nat := 118140960795 + 1816736 * 2 ^ 59
def prefixEnd_1816736 : Nat := 4983230072969 + 3 ^ 40 * 1816736 * 2
def baseEnd_1816736 : Nat := 207301953405935387943331

theorem tailTrace_1816736 : CollatzResearch.WordTrace tailWord_1816736 prefixEnd_1816736 207301953405935387943331 := by
  unfold tailWord_1816736
  simp only [CollatzResearch.WordTrace]
  refine ⟨33130902773141610325875031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44174537030855480434500041 33130902773141610325875031)
  ·
    refine ⟨49696354159712415488812547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33130902773141610325875031 49696354159712415488812547)
    ·
      refine ⟨74544531239568623233218821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49696354159712415488812547 74544531239568623233218821)
      ·
        refine ⟨13977099607419116856228529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74544531239568623233218821 13977099607419116856228529)
        ·
          refine ⟨10482824705564337642171397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13977099607419116856228529 10482824705564337642171397)
          ·
            refine ⟨1965529632293313307907137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10482824705564337642171397 1965529632293313307907137)
            ·
              refine ⟨1474147224219984980930353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965529632293313307907137 1474147224219984980930353)
              ·
                refine ⟨1105610418164988735697765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474147224219984980930353 1105610418164988735697765)
                ·
                  refine ⟨207301953405935387943331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105610418164988735697765 207301953405935387943331)
                  ·
                    rfl

theorem cell22_1816736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_1816736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816736 prefixEnd_1816736 := by exact prefixLift 1816736
  have htrace : WordTrace (prefixWord ++ tailWord_1816736) baseStart_1816736 baseEnd_1816736 := by
    simpa [prefixWord, tailWord_1816736, baseEnd_1816736] using wordTrace_append hprefix tailTrace_1816736
  have hstable : (prefixWord ++ tailWord_1816736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816736).length < 2 ^ (prefixWord ++ tailWord_1816736).sum := by decide
  have hdescent : baseEnd_1816736 < baseStart_1816736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816760 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_1816760 : Nat := 118140960795 + 1816760 * 2 ^ 59
def prefixEnd_1816760 : Nat := 4983230072969 + 3 ^ 40 * 1816760 * 2
def baseEnd_1816760 : Nat := 621914075908278101229919

theorem tailTrace_1816760 : CollatzResearch.WordTrace tailWord_1816760 prefixEnd_1816760 621914075908278101229919 := by
  unfold tailWord_1816760
  simp only [CollatzResearch.WordTrace]
  refine ⟨33131340449098136375311867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44175120598797515167082489 33131340449098136375311867)
  ·
    refine ⟨49697010673647204562967801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33131340449098136375311867 49697010673647204562967801)
    ·
      refine ⟨37272758005235403422225851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49697010673647204562967801 37272758005235403422225851)
      ·
        refine ⟨55909137007853105133338777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37272758005235403422225851 55909137007853105133338777)
        ·
          refine ⟨41931852755889828850004083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55909137007853105133338777 41931852755889828850004083)
          ·
            refine ⟨62897779133834743275006125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41931852755889828850004083 62897779133834743275006125)
            ·
              refine ⟨23586667175188028728127297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62897779133834743275006125 23586667175188028728127297)
              ·
                refine ⟨17690000381391021546095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23586667175188028728127297 17690000381391021546095473)
                ·
                  refine ⟨13267500286043266159571605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17690000381391021546095473 13267500286043266159571605)
                  ·
                    refine ⟨621914075908278101229919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13267500286043266159571605 621914075908278101229919)
                    ·
                      rfl

theorem cell22_1816760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_1816760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816760 prefixEnd_1816760 := by exact prefixLift 1816760
  have htrace : WordTrace (prefixWord ++ tailWord_1816760) baseStart_1816760 baseEnd_1816760 := by
    simpa [prefixWord, tailWord_1816760, baseEnd_1816760] using wordTrace_append hprefix tailTrace_1816760
  have hstable : (prefixWord ++ tailWord_1816760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816760).length < 2 ^ (prefixWord ++ tailWord_1816760).sum := by decide
  have hdescent : baseEnd_1816760 < baseStart_1816760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816762 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1816762 : Nat := 118140960795 + 1816762 * 2 ^ 59
def prefixEnd_1816762 : Nat := 4983230072969 + 3 ^ 40 * 1816762 * 2
def baseEnd_1816762 : Nat := 621914760549150762679913

theorem tailTrace_1816762 : CollatzResearch.WordTrace tailWord_1816762 prefixEnd_1816762 621914760549150762679913 := by
  unfold tailWord_1816762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565688461047256773049135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44175169229459351394797693 16565688461047256773049135)
  ·
    refine ⟨24848532691570885159573703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16565688461047256773049135 24848532691570885159573703)
    ·
      refine ⟨37272799037356327739360555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24848532691570885159573703 37272799037356327739360555)
      ·
        refine ⟨55909198556034491609040833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37272799037356327739360555 55909198556034491609040833)
        ·
          refine ⟨41931898917025868706780625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55909198556034491609040833 41931898917025868706780625)
          ·
            refine ⟨31448924187769401530085469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41931898917025868706780625 31448924187769401530085469)
            ·
              refine ⟨11793346570413525573782051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31448924187769401530085469 11793346570413525573782051)
              ·
                refine ⟨17690019855620288360673077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11793346570413525573782051 17690019855620288360673077)
                ·
                  refine ⟨1658439361464402033813101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17690019855620288360673077 1658439361464402033813101)
                  ·
                    refine ⟨621914760549150762679913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1658439361464402033813101 621914760549150762679913)
                    ·
                      rfl

theorem cell22_1816762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1816762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816762 prefixEnd_1816762 := by exact prefixLift 1816762
  have htrace : WordTrace (prefixWord ++ tailWord_1816762) baseStart_1816762 baseEnd_1816762 := by
    simpa [prefixWord, tailWord_1816762, baseEnd_1816762] using wordTrace_append hprefix tailTrace_1816762
  have hstable : (prefixWord ++ tailWord_1816762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816762).length < 2 ^ (prefixWord ++ tailWord_1816762).sum := by decide
  have hdescent : baseEnd_1816762 < baseStart_1816762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816764 : List Nat := [2, 2, 2, 3, 3, 1, 3, 6]
def baseStart_1816764 : Nat := 118140960795 + 1816764 * 2 ^ 59
def prefixEnd_1816764 : Nat := 4983230072969 + 3 ^ 40 * 1816764 * 2
def baseEnd_1816764 : Nat := 69101716132224824903323

theorem tailTrace_1816764 : CollatzResearch.WordTrace tailWord_1816764 prefixEnd_1816764 69101716132224824903323 := by
  unfold tailWord_1816764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33131413395090890716884673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44175217860121187622512897 33131413395090890716884673)
  ·
    refine ⟨24848560046318168037663505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33131413395090890716884673 24848560046318168037663505)
    ·
      refine ⟨18636420034738626028247629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24848560046318168037663505 18636420034738626028247629)
      ·
        refine ⟨6988657513026984760592861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18636420034738626028247629 6988657513026984760592861)
        ·
          refine ⟨2620746567385119285222323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6988657513026984760592861 2620746567385119285222323)
          ·
            refine ⟨3931119851077678927833485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620746567385119285222323 3931119851077678927833485)
            ·
              refine ⟨1474169944154129597937557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3931119851077678927833485 1474169944154129597937557)
              ·
                refine ⟨69101716132224824903323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1474169944154129597937557 69101716132224824903323)
                ·
                  rfl

theorem cell22_1816764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 6].length) (baseStart_1816764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816764 prefixEnd_1816764 := by exact prefixLift 1816764
  have htrace : WordTrace (prefixWord ++ tailWord_1816764) baseStart_1816764 baseEnd_1816764 := by
    simpa [prefixWord, tailWord_1816764, baseEnd_1816764] using wordTrace_append hprefix tailTrace_1816764
  have hstable : (prefixWord ++ tailWord_1816764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816764).length < 2 ^ (prefixWord ++ tailWord_1816764).sum := by decide
  have hdescent : baseEnd_1816764 < baseStart_1816764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816766 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1816766 : Nat := 118140960795 + 1816766 * 2 ^ 59
def prefixEnd_1816766 : Nat := 4983230072969 + 3 ^ 40 * 1816766 * 2
def baseEnd_1816766 : Nat := 621916129830896085579901

theorem tailTrace_1816766 : CollatzResearch.WordTrace tailWord_1816766 prefixEnd_1816766 621916129830896085579901 := by
  unfold tailWord_1816766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282862467021816971917769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44175266490783023850228101 8282862467021816971917769)
  ·
    refine ⟨6212146850266362728938327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8282862467021816971917769 6212146850266362728938327)
    ·
      refine ⟨9318220275399544093407491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6212146850266362728938327 9318220275399544093407491)
      ·
        refine ⟨13977330413099316140111237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318220275399544093407491 13977330413099316140111237)
        ·
          refine ⟨2620749452456121776270857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13977330413099316140111237 2620749452456121776270857)
          ·
            refine ⟨1965562089342091332203143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620749452456121776270857 1965562089342091332203143)
            ·
              refine ⟨2948343134013136998304715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965562089342091332203143 2948343134013136998304715)
              ·
                refine ⟨4422514701019705497457073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948343134013136998304715 4422514701019705497457073)
                ·
                  refine ⟨3316886025764779123092805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422514701019705497457073 3316886025764779123092805)
                  ·
                    refine ⟨621916129830896085579901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3316886025764779123092805 621916129830896085579901)
                    ·
                      rfl

theorem cell22_1816766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1816766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816766 prefixEnd_1816766 := by exact prefixLift 1816766
  have htrace : WordTrace (prefixWord ++ tailWord_1816766) baseStart_1816766 baseEnd_1816766 := by
    simpa [prefixWord, tailWord_1816766, baseEnd_1816766] using wordTrace_append hprefix tailTrace_1816766
  have hstable : (prefixWord ++ tailWord_1816766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816766).length < 2 ^ (prefixWord ++ tailWord_1816766).sum := by decide
  have hdescent : baseEnd_1816766 < baseStart_1816766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816792 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_1816792 : Nat := 118140960795 + 1816792 * 2 ^ 59
def prefixEnd_1816792 : Nat := 4983230072969 + 3 ^ 40 * 1816792 * 2
def baseEnd_1816792 : Nat := 207308343387413561476607

theorem tailTrace_1816792 : CollatzResearch.WordTrace tailWord_1816792 prefixEnd_1816792 207308343387413561476607 := by
  unfold tailWord_1816792
  simp only [CollatzResearch.WordTrace]
  refine ⟨33131924017040171107894315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44175898689386894810525753 33131924017040171107894315)
  ·
    refine ⟨49697886025560256661841473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33131924017040171107894315 49697886025560256661841473)
    ·
      refine ⟨37273414519170192496381105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49697886025560256661841473 37273414519170192496381105)
      ·
        refine ⟨27955060889377644372285829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37273414519170192496381105 27955060889377644372285829)
        ·
          refine ⟨5241573916758308319803593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27955060889377644372285829 5241573916758308319803593)
          ·
            refine ⟨3931180437568731239852695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5241573916758308319803593 3931180437568731239852695)
            ·
              refine ⟨5896770656353096859779043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931180437568731239852695 5896770656353096859779043)
              ·
                refine ⟨8845155984529645289668565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896770656353096859779043 8845155984529645289668565)
                ·
                  refine ⟨207308343387413561476607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8845155984529645289668565 207308343387413561476607)
                  ·
                    rfl

theorem cell22_1816792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_1816792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816792 prefixEnd_1816792 := by exact prefixLift 1816792
  have htrace : WordTrace (prefixWord ++ tailWord_1816792) baseStart_1816792 baseEnd_1816792 := by
    simpa [prefixWord, tailWord_1816792, baseEnd_1816792] using wordTrace_append hprefix tailTrace_1816792
  have hstable : (prefixWord ++ tailWord_1816792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816792).length < 2 ^ (prefixWord ++ tailWord_1816792).sum := by decide
  have hdescent : baseEnd_1816792 < baseStart_1816792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816802 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1816802 : Nat := 118140960795 + 1816802 * 2 ^ 59
def prefixEnd_1816802 : Nat := 4983230072969 + 3 ^ 40 * 1816802 * 2
def baseEnd_1816802 : Nat := 621928453366603991679791

theorem tailTrace_1816802 : CollatzResearch.WordTrace tailWord_1816802 prefixEnd_1816802 621928453366603991679791 := by
  unfold tailWord_1816802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566053191011028480913165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44176141842696075949101773 16566053191011028480913165)
  ·
    refine ⟨6212269946629135680342437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16566053191011028480913165 6212269946629135680342437)
    ·
      refine ⟨1164800614992962940064207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6212269946629135680342437 1164800614992962940064207)
      ·
        refine ⟨1747200922489444410096311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164800614992962940064207 1747200922489444410096311)
        ·
          refine ⟨2620801383734166615144467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747200922489444410096311 2620801383734166615144467)
          ·
            refine ⟨3931202075601249922716701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620801383734166615144467 3931202075601249922716701)
            ·
              refine ⟨1474200778350468721018763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3931202075601249922716701 1474200778350468721018763)
              ·
                refine ⟨2211301167525703081528145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474200778350468721018763 2211301167525703081528145)
                ·
                  refine ⟨1658475875644277311146109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2211301167525703081528145 1658475875644277311146109)
                  ·
                    refine ⟨621928453366603991679791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1658475875644277311146109 621928453366603991679791)
                    ·
                      rfl

theorem cell22_1816802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1816802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816802 prefixEnd_1816802 := by exact prefixLift 1816802
  have htrace : WordTrace (prefixWord ++ tailWord_1816802) baseStart_1816802 baseEnd_1816802 := by
    simpa [prefixWord, tailWord_1816802, baseEnd_1816802] using wordTrace_append hprefix tailTrace_1816802
  have hstable : (prefixWord ++ tailWord_1816802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816802).length < 2 ^ (prefixWord ++ tailWord_1816802).sum := by decide
  have hdescent : baseEnd_1816802 < baseStart_1816802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816867 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 4, 4]
def baseStart_1816867 : Nat := 118140960795 + 1816867 * 2 ^ 59
def prefixEnd_1816867 : Nat := 4983230072969 + 3 ^ 40 * 1816867 * 2
def baseEnd_1816867 : Nat := 621950704194965488804591

theorem tailTrace_1816867 : CollatzResearch.WordTrace tailWord_1816867 prefixEnd_1816867 621950704194965488804591 := by
  unfold tailWord_1816867
  simp only [CollatzResearch.WordTrace]
  refine ⟨66266583508808630024768855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44177722339205753349845903 66266583508808630024768855)
  ·
    refine ⟨99399875263212945037153283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66266583508808630024768855 99399875263212945037153283)
    ·
      refine ⟨149099812894819417555729925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99399875263212945037153283 149099812894819417555729925)
      ·
        refine ⟨27956214917778640791699361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149099812894819417555729925 27956214917778640791699361)
        ·
          refine ⟨20967161188333980593774521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27956214917778640791699361 20967161188333980593774521)
          ·
            refine ⟨15725370891250485445330891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20967161188333980593774521 15725370891250485445330891)
            ·
              refine ⟨23588056336875728167996337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15725370891250485445330891 23588056336875728167996337)
              ·
                refine ⟨17691042252656796125997253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23588056336875728167996337 17691042252656796125997253)
                ·
                  refine ⟨3317070422373149273624485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17691042252656796125997253 3317070422373149273624485)
                  ·
                    refine ⟨621950704194965488804591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317070422373149273624485 621950704194965488804591)
                    ·
                      rfl

theorem cell22_1816867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_1816867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816867 prefixEnd_1816867 := by exact prefixLift 1816867
  have htrace : WordTrace (prefixWord ++ tailWord_1816867) baseStart_1816867 baseEnd_1816867 := by
    simpa [prefixWord, tailWord_1816867, baseEnd_1816867] using wordTrace_append hprefix tailTrace_1816867
  have hstable : (prefixWord ++ tailWord_1816867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816867).length < 2 ^ (prefixWord ++ tailWord_1816867).sum := by decide
  have hdescent : baseEnd_1816867 < baseStart_1816867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816912 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_1816912 : Nat := 118140960795 + 1816912 * 2 ^ 59
def prefixEnd_1816912 : Nat := 4983230072969 + 3 ^ 40 * 1816912 * 2
def baseEnd_1816912 : Nat := 621966108614600371429453

theorem tailTrace_1816912 : CollatzResearch.WordTrace tailWord_1816912 prefixEnd_1816912 621966108614600371429453 := by
  unfold tailWord_1816912
  simp only [CollatzResearch.WordTrace]
  refine ⟨33134112396822801355078495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44178816529097068473437993 33134112396822801355078495)
  ·
    refine ⟨49701168595234202032617743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33134112396822801355078495 49701168595234202032617743)
    ·
      refine ⟨74551752892851303048926615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49701168595234202032617743 74551752892851303048926615)
      ·
        refine ⟨111827629339276954573389923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74551752892851303048926615 111827629339276954573389923)
        ·
          refine ⟨167741444008915431860084885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111827629339276954573389923 167741444008915431860084885)
          ·
            refine ⟨7862880187917910868441479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167741444008915431860084885 7862880187917910868441479)
            ·
              refine ⟨11794320281876866302662219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862880187917910868441479 11794320281876866302662219)
              ·
                refine ⟨17691480422815299453993329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11794320281876866302662219 17691480422815299453993329)
                ·
                  refine ⟨13268610317111474590494997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17691480422815299453993329 13268610317111474590494997)
                  ·
                    refine ⟨621966108614600371429453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13268610317111474590494997 621966108614600371429453)
                    ·
                      rfl

theorem cell22_1816912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_1816912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816912 prefixEnd_1816912 := by exact prefixLift 1816912
  have htrace : WordTrace (prefixWord ++ tailWord_1816912) baseStart_1816912 baseEnd_1816912 := by
    simpa [prefixWord, tailWord_1816912, baseEnd_1816912] using wordTrace_append hprefix tailTrace_1816912
  have hstable : (prefixWord ++ tailWord_1816912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816912).length < 2 ^ (prefixWord ++ tailWord_1816912).sum := by decide
  have hdescent : baseEnd_1816912 < baseStart_1816912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816961 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 5]
def baseStart_1816961 : Nat := 118140960795 + 1816961 * 2 ^ 59
def prefixEnd_1816961 : Nat := 4983230072969 + 3 ^ 40 * 1816961 * 2
def baseEnd_1816961 : Nat := 207327627438660192318101

theorem tailTrace_1816961 : CollatzResearch.WordTrace tailWord_1816961 prefixEnd_1816961 207327627438660192318101 := by
  unfold tailWord_1816961
  simp only [CollatzResearch.WordTrace]
  refine ⟨66270011970468084078690737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44180007980312056052460491 66270011970468084078690737)
  ·
    refine ⟨49702508977851063059018053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66270011970468084078690737 49702508977851063059018053)
    ·
      refine ⟨9319220433347074323565885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49702508977851063059018053 9319220433347074323565885)
      ·
        refine ⟨3494707662505152871337207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9319220433347074323565885 3494707662505152871337207)
        ·
          refine ⟨5242061493757729307005811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494707662505152871337207 5242061493757729307005811)
          ·
            refine ⟨7863092240636593960508717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242061493757729307005811 7863092240636593960508717)
            ·
              refine ⟨2948659590238722735190769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7863092240636593960508717 2948659590238722735190769)
              ·
                refine ⟨2211494692679042051393077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2948659590238722735190769 2211494692679042051393077)
                ·
                  refine ⟨207327627438660192318101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2211494692679042051393077 207327627438660192318101)
                  ·
                    rfl

theorem cell22_1816961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_1816961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816961 prefixEnd_1816961 := by exact prefixLift 1816961
  have htrace : WordTrace (prefixWord ++ tailWord_1816961) baseStart_1816961 baseEnd_1816961 := by
    simpa [prefixWord, tailWord_1816961, baseEnd_1816961] using wordTrace_append hprefix tailTrace_1816961
  have hstable : (prefixWord ++ tailWord_1816961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816961).length < 2 ^ (prefixWord ++ tailWord_1816961).sum := by decide
  have hdescent : baseEnd_1816961 < baseStart_1816961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816991 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 1, 4]
def baseStart_1816991 : Nat := 118140960795 + 1816991 * 2 ^ 59
def prefixEnd_1816991 : Nat := 4983230072969 + 3 ^ 40 * 1816991 * 2
def baseEnd_1816991 : Nat := 621993151929070498704211

theorem tailTrace_1816991 : CollatzResearch.WordTrace tailWord_1816991 prefixEnd_1816991 621993151929070498704211 := by
  unfold tailWord_1816991
  simp only [CollatzResearch.WordTrace]
  refine ⟨66271106160359399202282827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44180737440239599468188551 66271106160359399202282827)
  ·
    refine ⟨99406659240539098803424241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66271106160359399202282827 99406659240539098803424241)
    ·
      refine ⟨74554994430404324102568181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99406659240539098803424241 74554994430404324102568181)
      ·
        refine ⟨6989530727850405384615767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74554994430404324102568181 6989530727850405384615767)
        ·
          refine ⟨10484296091775608076923651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989530727850405384615767 10484296091775608076923651)
          ·
            refine ⟨15726444137663412115385477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484296091775608076923651 15726444137663412115385477)
            ·
              refine ⟨2948708275811889771634777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15726444137663412115385477 2948708275811889771634777)
              ·
                refine ⟨2211531206858917328726083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2948708275811889771634777 2211531206858917328726083)
                ·
                  refine ⟨3317296810288375993089125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211531206858917328726083 3317296810288375993089125)
                  ·
                    refine ⟨621993151929070498704211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317296810288375993089125 621993151929070498704211)
                    ·
                      rfl

theorem cell22_1816991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_1816991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1816991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1816991 prefixEnd_1816991 := by exact prefixLift 1816991
  have htrace : WordTrace (prefixWord ++ tailWord_1816991) baseStart_1816991 baseEnd_1816991 := by
    simpa [prefixWord, tailWord_1816991, baseEnd_1816991] using wordTrace_append hprefix tailTrace_1816991
  have hstable : (prefixWord ++ tailWord_1816991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816991).length < 2 ^ (prefixWord ++ tailWord_1816991).sum := by decide
  have hdescent : baseEnd_1816991 < baseStart_1816991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817021 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_1817021 : Nat := 118140960795 + 1817021 * 2 ^ 59
def prefixEnd_1817021 : Nat := 4983230072969 + 3 ^ 40 * 1817021 * 2
def baseEnd_1817021 : Nat := 622003421542160420454119

theorem tailTrace_1817021 : CollatzResearch.WordTrace tailWord_1817021 prefixEnd_1817021 622003421542160420454119 := by
  unfold tailWord_1817021
  simp only [CollatzResearch.WordTrace]
  refine ⟨66272200350250714325874917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44181466900167142883916611 66272200350250714325874917)
  ·
    refine ⟨12426037565672008936101547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66272200350250714325874917 12426037565672008936101547)
    ·
      refine ⟨18639056348508013404152321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12426037565672008936101547 18639056348508013404152321)
      ·
        refine ⟨13979292261381010053114241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18639056348508013404152321 13979292261381010053114241)
        ·
          refine ⟨10484469196035757539835681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13979292261381010053114241 10484469196035757539835681)
          ·
            refine ⟨7863351897026818154876761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10484469196035757539835681 7863351897026818154876761)
            ·
              refine ⟨5897513922770113616157571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7863351897026818154876761 5897513922770113616157571)
              ·
                refine ⟨8846270884155170424236357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897513922770113616157571 8846270884155170424236357)
                ·
                  refine ⟨1658675790779094454544317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8846270884155170424236357 1658675790779094454544317)
                  ·
                    refine ⟨622003421542160420454119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1658675790779094454544317 622003421542160420454119)
                    ·
                      rfl

theorem cell22_1817021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_1817021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817021 prefixEnd_1817021 := by exact prefixLift 1817021
  have htrace : WordTrace (prefixWord ++ tailWord_1817021) baseStart_1817021 baseEnd_1817021 := by
    simpa [prefixWord, tailWord_1817021, baseEnd_1817021] using wordTrace_append hprefix tailTrace_1817021
  have hstable : (prefixWord ++ tailWord_1817021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817021).length < 2 ^ (prefixWord ++ tailWord_1817021).sum := by decide
  have hdescent : baseEnd_1817021 < baseStart_1817021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817034 : List Nat := [3, 1, 2, 1, 2, 2, 4, 7]
def baseStart_1817034 : Nat := 118140960795 + 1817034 * 2 ^ 59
def prefixEnd_1817034 : Nat := 4983230072969 + 3 ^ 40 * 1817034 * 2
def baseEnd_1817034 : Nat := 69111985745314746653231

theorem tailTrace_1817034 : CollatzResearch.WordTrace tailWord_1817034 prefixEnd_1817034 69111985745314746653231 := by
  unfold tailWord_1817034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568168624800904386524539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44181782999469078364065437 16568168624800904386524539)
  ·
    refine ⟨24852252937201356579786809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16568168624800904386524539 24852252937201356579786809)
    ·
      refine ⟨18639189702901017434840107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24852252937201356579786809 18639189702901017434840107)
      ·
        refine ⟨27958784554351526152260161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18639189702901017434840107 27958784554351526152260161)
        ·
          refine ⟨20969088415763644614195121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27958784554351526152260161 20969088415763644614195121)
          ·
            refine ⟨15726816311822733460646341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20969088415763644614195121 15726816311822733460646341)
            ·
              refine ⟨2948778058466762523871189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15726816311822733460646341 2948778058466762523871189)
              ·
                refine ⟨69111985745314746653231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2948778058466762523871189 69111985745314746653231)
                ·
                  rfl

theorem cell22_1817034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_1817034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817034 prefixEnd_1817034 := by exact prefixLift 1817034
  have htrace : WordTrace (prefixWord ++ tailWord_1817034) baseStart_1817034 baseEnd_1817034 := by
    simpa [prefixWord, tailWord_1817034, baseEnd_1817034] using wordTrace_append hprefix tailTrace_1817034
  have hstable : (prefixWord ++ tailWord_1817034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817034).length < 2 ^ (prefixWord ++ tailWord_1817034).sum := by decide
  have hdescent : baseEnd_1817034 < baseStart_1817034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817042 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1817042 : Nat := 118140960795 + 1817042 * 2 ^ 59
def prefixEnd_1817042 : Nat := 4983230072969 + 3 ^ 40 * 1817042 * 2
def baseEnd_1817042 : Nat := 622010610271323365679055

theorem tailTrace_1817042 : CollatzResearch.WordTrace tailWord_1817042 prefixEnd_1817042 622010610271323365679055 := by
  unfold tailWord_1817042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568241570793658728097345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44181977522116423274926253 16568241570793658728097345)
  ·
    refine ⟨12426181178095244046073009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16568241570793658728097345 12426181178095244046073009)
    ·
      refine ⟨9319635883571433034554757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12426181178095244046073009 9319635883571433034554757)
      ·
        refine ⟨1747431728169643693979017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9319635883571433034554757 1747431728169643693979017)
        ·
          refine ⟨1310573796127232770484263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1747431728169643693979017 1310573796127232770484263)
          ·
            refine ⟨1965860694190849155726395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310573796127232770484263 1965860694190849155726395)
            ·
              refine ⟨2948791041286273733589593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965860694190849155726395 2948791041286273733589593)
              ·
                refine ⟨2211593280964705300192195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2948791041286273733589593 2211593280964705300192195)
                ·
                  refine ⟨3317389921447057950288293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211593280964705300192195 3317389921447057950288293)
                  ·
                    refine ⟨622010610271323365679055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317389921447057950288293 622010610271323365679055)
                    ·
                      rfl

theorem cell22_1817042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1817042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817042 prefixEnd_1817042 := by exact prefixLift 1817042
  have htrace : WordTrace (prefixWord ++ tailWord_1817042) baseStart_1817042 baseEnd_1817042 := by
    simpa [prefixWord, tailWord_1817042, baseEnd_1817042] using wordTrace_append hprefix tailTrace_1817042
  have hstable : (prefixWord ++ tailWord_1817042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817042).length < 2 ^ (prefixWord ++ tailWord_1817042).sum := by decide
  have hdescent : baseEnd_1817042 < baseStart_1817042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817141 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 6]
def baseStart_1817141 : Nat := 118140960795 + 1817141 * 2 ^ 59
def prefixEnd_1817141 : Nat := 4983230072969 + 3 ^ 40 * 1817141 * 2
def baseEnd_1817141 : Nat := 207348166664840035817917

theorem tailTrace_1817141 : CollatzResearch.WordTrace tailWord_1817141 prefixEnd_1817141 207348166664840035817917 := by
  unfold tailWord_1817141
  simp only [CollatzResearch.WordTrace]
  refine ⟨66276577109815974820243277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44184384739877316546828851 66276577109815974820243277)
  ·
    refine ⟨24853716416180990557591229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66276577109815974820243277 24853716416180990557591229)
    ·
      refine ⟨9320143656067871459096711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24853716416180990557591229 9320143656067871459096711)
      ·
        refine ⟨13980215484101807188645067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9320143656067871459096711 13980215484101807188645067)
        ·
          refine ⟨20970323226152710782967601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13980215484101807188645067 20970323226152710782967601)
          ·
            refine ⟨15727742419614533087225701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20970323226152710782967601 15727742419614533087225701)
            ·
              refine ⟨2948951703677724953854819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15727742419614533087225701 2948951703677724953854819)
              ·
                refine ⟨4423427555516587430782229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948951703677724953854819 4423427555516587430782229)
                ·
                  refine ⟨207348166664840035817917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4423427555516587430782229 207348166664840035817917)
                  ·
                    rfl

theorem cell22_1817141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_1817141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817141 prefixEnd_1817141 := by exact prefixLift 1817141
  have htrace : WordTrace (prefixWord ++ tailWord_1817141) baseStart_1817141 baseEnd_1817141 := by
    simpa [prefixWord, tailWord_1817141, baseEnd_1817141] using wordTrace_append hprefix tailTrace_1817141
  have hstable : (prefixWord ++ tailWord_1817141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817141).length < 2 ^ (prefixWord ++ tailWord_1817141).sum := by decide
  have hdescent : baseEnd_1817141 < baseStart_1817141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817192 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 4]
def baseStart_1817192 : Nat := 118140960795 + 1817192 * 2 ^ 59
def prefixEnd_1817192 : Nat := 4983230072969 + 3 ^ 40 * 1817192 * 2
def baseEnd_1817192 : Nat := 207353986112257658142865

theorem tailTrace_1817192 : CollatzResearch.WordTrace tailWord_1817192 prefixEnd_1817192 207353986112257658142865 := by
  unfold tailWord_1817192
  simp only [CollatzResearch.WordTrace]
  refine ⟨33139218616315605265174915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44185624821754140353566553 33139218616315605265174915)
  ·
    refine ⟨49708827924473407897762373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33139218616315605265174915 49708827924473407897762373)
    ·
      refine ⟨9320405235838763980830445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49708827924473407897762373 9320405235838763980830445)
      ·
        refine ⟨3495151963439536492811417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9320405235838763980830445 3495151963439536492811417)
        ·
          refine ⟨2621363972579652369608563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495151963439536492811417 2621363972579652369608563)
          ·
            refine ⟨3932045958869478554412845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621363972579652369608563 3932045958869478554412845)
            ·
              refine ⟨1474517234576054457904817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3932045958869478554412845 1474517234576054457904817)
              ·
                refine ⟨1105887925932040843428613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474517234576054457904817 1105887925932040843428613)
                ·
                  refine ⟨207353986112257658142865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105887925932040843428613 207353986112257658142865)
                  ·
                    rfl

theorem cell22_1817192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_1817192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817192 prefixEnd_1817192 := by exact prefixLift 1817192
  have htrace : WordTrace (prefixWord ++ tailWord_1817192) baseStart_1817192 baseEnd_1817192 := by
    simpa [prefixWord, tailWord_1817192, baseEnd_1817192] using wordTrace_append hprefix tailTrace_1817192
  have hstable : (prefixWord ++ tailWord_1817192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817192).length < 2 ^ (prefixWord ++ tailWord_1817192).sum := by decide
  have hdescent : baseEnd_1817192 < baseStart_1817192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817278 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1817278 : Nat := 118140960795 + 1817278 * 2 ^ 59
def prefixEnd_1817278 : Nat := 4983230072969 + 3 ^ 40 * 1817278 * 2
def baseEnd_1817278 : Nat := 622091397894297416778331

theorem tailTrace_1817278 : CollatzResearch.WordTrace tailWord_1817278 prefixEnd_1817278 622091397894297416778331 := by
  unfold tailWord_1817278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8285196738789955902247561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44187715940213098145320325 8285196738789955902247561)
  ·
    refine ⟨6213897554092466926685671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8285196738789955902247561 6213897554092466926685671)
    ·
      refine ⟨9320846331138700390028507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6213897554092466926685671 9320846331138700390028507)
      ·
        refine ⟨13981269496708050585042761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9320846331138700390028507 13981269496708050585042761)
        ·
          refine ⟨10485952122531037938782071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13981269496708050585042761 10485952122531037938782071)
          ·
            refine ⟨15728928183796556908173107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485952122531037938782071 15728928183796556908173107)
            ·
              refine ⟨23593392275694835362259661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728928183796556908173107 23593392275694835362259661)
              ·
                refine ⟨8847522103385563260847373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23593392275694835362259661 8847522103385563260847373)
                ·
                  refine ⟨3317820788769586222817765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8847522103385563260847373 3317820788769586222817765)
                  ·
                    refine ⟨622091397894297416778331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317820788769586222817765 622091397894297416778331)
                    ·
                      rfl

theorem cell22_1817278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1817278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817278 prefixEnd_1817278 := by exact prefixLift 1817278
  have htrace : WordTrace (prefixWord ++ tailWord_1817278) baseStart_1817278 baseEnd_1817278 := by
    simpa [prefixWord, tailWord_1817278, baseEnd_1817278] using wordTrace_append hprefix tailTrace_1817278
  have hstable : (prefixWord ++ tailWord_1817278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817278).length < 2 ^ (prefixWord ++ tailWord_1817278).sum := by decide
  have hdescent : baseEnd_1817278 < baseStart_1817278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817336 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_1817336 : Nat := 118140960795 + 1817336 * 2 ^ 59
def prefixEnd_1817336 : Nat := 4983230072969 + 3 ^ 40 * 1817336 * 2
def baseEnd_1817336 : Nat := 622111252479604598828153

theorem tailTrace_1817336 : CollatzResearch.WordTrace tailWord_1817336 prefixEnd_1817336 622111252479604598828153 := by
  unfold tailWord_1817336
  simp only [CollatzResearch.WordTrace]
  refine ⟨33141844672054761561795931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44189126229406348749061241 33141844672054761561795931)
  ·
    refine ⟨49712767008082142342693897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33141844672054761561795931 49712767008082142342693897)
    ·
      refine ⟨37284575256061606757020423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49712767008082142342693897 37284575256061606757020423)
      ·
        refine ⟨55926862884092410135530635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37284575256061606757020423 55926862884092410135530635)
        ·
          refine ⟨83890294326138615203295953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55926862884092410135530635 83890294326138615203295953)
          ·
            refine ⟨62917720744603961402471965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83890294326138615203295953 62917720744603961402471965)
            ·
              refine ⟨23594145279226485525926987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62917720744603961402471965 23594145279226485525926987)
              ·
                refine ⟨35391217918839728288890481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23594145279226485525926987 35391217918839728288890481)
                ·
                  refine ⟨26543413439129796216667861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35391217918839728288890481 26543413439129796216667861)
                  ·
                    refine ⟨622111252479604598828153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26543413439129796216667861 622111252479604598828153)
                    ·
                      rfl

theorem cell22_1817336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_1817336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817336 prefixEnd_1817336 := by exact prefixLift 1817336
  have htrace : WordTrace (prefixWord ++ tailWord_1817336) baseStart_1817336 baseEnd_1817336 := by
    simpa [prefixWord, tailWord_1817336, baseEnd_1817336] using wordTrace_append hprefix tailTrace_1817336
  have hstable : (prefixWord ++ tailWord_1817336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817336).length < 2 ^ (prefixWord ++ tailWord_1817336).sum := by decide
  have hdescent : baseEnd_1817336 < baseStart_1817336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817338 : List Nat := [3, 1, 1, 1, 1, 3, 6, 6]
def baseStart_1817338 : Nat := 118140960795 + 1817338 * 2 ^ 59
def prefixEnd_1817338 : Nat := 4983230072969 + 3 ^ 40 * 1817338 * 2
def baseEnd_1817338 : Nat := 69123548568941917808683

theorem tailTrace_1817338 : CollatzResearch.WordTrace tailWord_1817338 prefixEnd_1817338 69123548568941917808683 := by
  unfold tailWord_1817338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16570940572525569366291167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44189174860068184976776445 16570940572525569366291167)
  ·
    refine ⟨24856410858788354049436751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16570940572525569366291167 24856410858788354049436751)
    ·
      refine ⟨37284616288182531074155127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24856410858788354049436751 37284616288182531074155127)
      ·
        refine ⟨55926924432273796611232691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37284616288182531074155127 55926924432273796611232691)
        ·
          refine ⟨83890386648410694916849037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55926924432273796611232691 83890386648410694916849037)
          ·
            refine ⟨31458894993154010593818389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83890386648410694916849037 31458894993154010593818389)
            ·
              refine ⟨1474635702804094246585237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31458894993154010593818389 1474635702804094246585237)
              ·
                refine ⟨69123548568941917808683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1474635702804094246585237 69123548568941917808683)
                ·
                  rfl

theorem cell22_1817338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_1817338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817338 prefixEnd_1817338 := by exact prefixLift 1817338
  have htrace : WordTrace (prefixWord ++ tailWord_1817338) baseStart_1817338 baseEnd_1817338 := by
    simpa [prefixWord, tailWord_1817338, baseEnd_1817338] using wordTrace_append hprefix tailTrace_1817338
  have hstable : (prefixWord ++ tailWord_1817338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817338).length < 2 ^ (prefixWord ++ tailWord_1817338).sum := by decide
  have hdescent : baseEnd_1817338 < baseStart_1817338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817353 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_1817353 : Nat := 118140960795 + 1817353 * 2 ^ 59
def prefixEnd_1817353 : Nat := 4983230072969 + 3 ^ 40 * 1817353 * 2
def baseEnd_1817353 : Nat := 622117071927022221153101

theorem tailTrace_1817353 : CollatzResearch.WordTrace tailWord_1817353 prefixEnd_1817353 622117071927022221153101 := by
  unfold tailWord_1817353
  simp only [CollatzResearch.WordTrace]
  refine ⟨66284309385047935026960713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44189539590031956684640475 66284309385047935026960713)
  ·
    refine ⟨49713232038785951270220535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66284309385047935026960713 49713232038785951270220535)
    ·
      refine ⟨74569848058178926905330803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49713232038785951270220535 74569848058178926905330803)
      ·
        refine ⟨111854772087268390357996205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74569848058178926905330803 111854772087268390357996205)
        ·
          refine ⟨41945539532725646384248577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111854772087268390357996205 41945539532725646384248577)
          ·
            refine ⟨31459154649544234788186433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41945539532725646384248577 31459154649544234788186433)
            ·
              refine ⟨23594365987158176091139825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31459154649544234788186433 23594365987158176091139825)
              ·
                refine ⟨17695774490368632068354869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23594365987158176091139825 17695774490368632068354869)
                ·
                  refine ⟨1658978858472059256408269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17695774490368632068354869 1658978858472059256408269)
                  ·
                    refine ⟨622117071927022221153101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1658978858472059256408269 622117071927022221153101)
                    ·
                      rfl

theorem cell22_1817353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_1817353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817353 prefixEnd_1817353 := by exact prefixLift 1817353
  have htrace : WordTrace (prefixWord ++ tailWord_1817353) baseStart_1817353 baseEnd_1817353 := by
    simpa [prefixWord, tailWord_1817353, baseEnd_1817353] using wordTrace_append hprefix tailTrace_1817353
  have hstable : (prefixWord ++ tailWord_1817353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817353).length < 2 ^ (prefixWord ++ tailWord_1817353).sum := by decide
  have hdescent : baseEnd_1817353 < baseStart_1817353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817421 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1817421 : Nat := 118140960795 + 1817421 * 2 ^ 59
def prefixEnd_1817421 : Nat := 4983230072969 + 3 ^ 40 * 1817421 * 2
def baseEnd_1817421 : Nat := 622140349716692710452893

theorem tailTrace_1817421 : CollatzResearch.WordTrace tailWord_1817421 prefixEnd_1817421 622140349716692710452893 := by
  unfold tailWord_1817421
  simp only [CollatzResearch.WordTrace]
  refine ⟨66286789548801582640436117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44191193032534388426957411 66286789548801582640436117)
  ·
    refine ⟨3107193260100074186270443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66286789548801582640436117 3107193260100074186270443)
    ·
      refine ⟨4660789890150111279405665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107193260100074186270443 4660789890150111279405665)
      ·
        refine ⟨3495592417612583459554249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4660789890150111279405665 3495592417612583459554249)
        ·
          refine ⟨2621694313209437594665687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495592417612583459554249 2621694313209437594665687)
          ·
            refine ⟨3932541469814156391998531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621694313209437594665687 3932541469814156391998531)
            ·
              refine ⟨5898812204721234587997797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932541469814156391998531 5898812204721234587997797)
              ·
                refine ⟨1106027288385231485249587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5898812204721234587997797 1106027288385231485249587)
                ·
                  refine ⟨1659040932577847227874381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106027288385231485249587 1659040932577847227874381)
                  ·
                    refine ⟨622140349716692710452893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659040932577847227874381 622140349716692710452893)
                    ·
                      rfl

theorem cell22_1817421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1817421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817421 prefixEnd_1817421 := by exact prefixLift 1817421
  have htrace : WordTrace (prefixWord ++ tailWord_1817421) baseStart_1817421 baseEnd_1817421 := by
    simpa [prefixWord, tailWord_1817421, baseEnd_1817421] using wordTrace_append hprefix tailTrace_1817421
  have hstable : (prefixWord ++ tailWord_1817421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817421).length < 2 ^ (prefixWord ++ tailWord_1817421).sum := by decide
  have hdescent : baseEnd_1817421 < baseStart_1817421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817477 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_1817477 : Nat := 118140960795 + 1817477 * 2 ^ 59
def prefixEnd_1817477 : Nat := 4983230072969 + 3 ^ 40 * 1817477 * 2
def baseEnd_1817477 : Nat := 622159519661127231052721

theorem tailTrace_1817477 : CollatzResearch.WordTrace tailWord_1817477 prefixEnd_1817477 622159519661127231052721 := by
  unfold tailWord_1817477
  simp only [CollatzResearch.WordTrace]
  refine ⟨66288832036598704204474685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44192554691065802802983123 66288832036598704204474685)
  ·
    refine ⟨24858312013724514076678007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66288832036598704204474685 24858312013724514076678007)
    ·
      refine ⟨37287468020586771115017011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24858312013724514076678007 37287468020586771115017011)
      ·
        refine ⟨55931202030880156672525517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37287468020586771115017011 55931202030880156672525517)
        ·
          refine ⟨20974200761580058752197069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55931202030880156672525517 20974200761580058752197069)
          ·
            refine ⟨7865325285592522032073901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20974200761580058752197069 7865325285592522032073901)
            ·
              refine ⟨2949496982097195762027713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7865325285592522032073901 2949496982097195762027713)
              ·
                refine ⟨2212122736572896821520785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949496982097195762027713 2212122736572896821520785)
                ·
                  refine ⟨1659092052429672616140589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2212122736572896821520785 1659092052429672616140589)
                  ·
                    refine ⟨622159519661127231052721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659092052429672616140589 622159519661127231052721)
                    ·
                      rfl

theorem cell22_1817477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_1817477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817477 prefixEnd_1817477 := by exact prefixLift 1817477
  have htrace : WordTrace (prefixWord ++ tailWord_1817477) baseStart_1817477 baseEnd_1817477 := by
    simpa [prefixWord, tailWord_1817477, baseEnd_1817477] using wordTrace_append hprefix tailTrace_1817477
  have hstable : (prefixWord ++ tailWord_1817477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817477).length < 2 ^ (prefixWord ++ tailWord_1817477).sum := by decide
  have hdescent : baseEnd_1817477 < baseStart_1817477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817612 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_1817612 : Nat := 118140960795 + 1817612 * 2 ^ 59
def prefixEnd_1817612 : Nat := 4983230072969 + 3 ^ 40 * 1817612 * 2
def baseEnd_1817612 : Nat := 622205732920031878927307

theorem tailTrace_1817612 : CollatzResearch.WordTrace tailWord_1817612 prefixEnd_1817612 622205732920031878927307 := by
  unfold tailWord_1817612
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146877945554811130319545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44195837260739748173759393 33146877945554811130319545)
  ·
    refine ⟨24860158459166108347739659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33146877945554811130319545 24860158459166108347739659)
    ·
      refine ⟨37290237688749162521609489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24860158459166108347739659 37290237688749162521609489)
      ·
        refine ⟨27967678266561871891207117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37290237688749162521609489 27967678266561871891207117)
        ·
          refine ⟨10487879349960701959202669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27967678266561871891207117 10487879349960701959202669)
          ·
            refine ⟨3932954756235263234701001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10487879349960701959202669 3932954756235263234701001)
            ·
              refine ⟨2949716067176447426025751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932954756235263234701001 2949716067176447426025751)
              ·
                refine ⟨4424574100764671139038627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949716067176447426025751 4424574100764671139038627)
                ·
                  refine ⟨6636861151147006708557941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424574100764671139038627 6636861151147006708557941)
                  ·
                    refine ⟨622205732920031878927307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6636861151147006708557941 622205732920031878927307)
                    ·
                      rfl

theorem cell22_1817612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_1817612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817612 prefixEnd_1817612 := by exact prefixLift 1817612
  have htrace : WordTrace (prefixWord ++ tailWord_1817612) baseStart_1817612 baseEnd_1817612 := by
    simpa [prefixWord, tailWord_1817612, baseEnd_1817612] using wordTrace_append hprefix tailTrace_1817612
  have hstable : (prefixWord ++ tailWord_1817612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817612).length < 2 ^ (prefixWord ++ tailWord_1817612).sum := by decide
  have hdescent : baseEnd_1817612 < baseStart_1817612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817642 : List Nat := [3, 1, 4, 1, 3, 1, 9]
def baseStart_1817642 : Nat := 118140960795 + 1817642 * 2 ^ 59
def prefixEnd_1817642 : Nat := 4983230072969 + 3 ^ 40 * 1817642 * 2
def baseEnd_1817642 : Nat := 23045037130856362988045

theorem tailTrace_1817642 : CollatzResearch.WordTrace tailWord_1817642 prefixEnd_1817642 23045037130856362988045 := by
  unfold tailWord_1817642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16573712520250234346057795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44196566720667291589487453 16573712520250234346057795)
  ·
    refine ⟨24860568780375351519086693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16573712520250234346057795 24860568780375351519086693)
    ·
      refine ⟨4661356646320378409828755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24860568780375351519086693 4661356646320378409828755)
      ·
        refine ⟨6992034969480567614743133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661356646320378409828755 6992034969480567614743133)
        ·
          refine ⟨2622013113555212855528675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6992034969480567614743133 2622013113555212855528675)
          ·
            refine ⟨3933019670332819283293013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622013113555212855528675 3933019670332819283293013)
            ·
              refine ⟨23045037130856362988045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3933019670332819283293013 23045037130856362988045)
              ·
                rfl

theorem cell22_1817642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 9].length) (baseStart_1817642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817642 prefixEnd_1817642 := by exact prefixLift 1817642
  have htrace : WordTrace (prefixWord ++ tailWord_1817642) baseStart_1817642 baseEnd_1817642 := by
    simpa [prefixWord, tailWord_1817642, baseEnd_1817642] using wordTrace_append hprefix tailTrace_1817642
  have hstable : (prefixWord ++ tailWord_1817642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817642).length < 2 ^ (prefixWord ++ tailWord_1817642).sum := by decide
  have hdescent : baseEnd_1817642 < baseStart_1817642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817721 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 5]
def baseStart_1817721 : Nat := 118140960795 + 1817721 * 2 ^ 59
def prefixEnd_1817721 : Nat := 4983230072969 + 3 ^ 40 * 1817721 * 2
def baseEnd_1817721 : Nat := 207414348615863975983991

theorem tailTrace_1817721 : CollatzResearch.WordTrace tailWord_1817721 prefixEnd_1817721 207414348615863975983991 := by
  unfold tailWord_1817721
  simp only [CollatzResearch.WordTrace]
  refine ⟨66297731447714733876357017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44198487631809822584238011 66297731447714733876357017)
  ·
    refine ⟨49723298585786050407267763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66297731447714733876357017 49723298585786050407267763)
    ·
      refine ⟨74584947878679075610901645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49723298585786050407267763 74584947878679075610901645)
      ·
        refine ⟨27969355454504653354088117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74584947878679075610901645 27969355454504653354088117)
        ·
          refine ⟨2622127073859811251945761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27969355454504653354088117 2622127073859811251945761)
          ·
            refine ⟨1966595305394858438959321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622127073859811251945761 1966595305394858438959321)
            ·
              refine ⟨1474946479046143829219491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966595305394858438959321 1474946479046143829219491)
              ·
                refine ⟨2212419718569215743829237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474946479046143829219491 2212419718569215743829237)
                ·
                  refine ⟨207414348615863975983991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2212419718569215743829237 207414348615863975983991)
                  ·
                    rfl

theorem cell22_1817721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_1817721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817721 prefixEnd_1817721 := by exact prefixLift 1817721
  have htrace : WordTrace (prefixWord ++ tailWord_1817721) baseStart_1817721 baseEnd_1817721 := by
    simpa [prefixWord, tailWord_1817721, baseEnd_1817721] using wordTrace_append hprefix tailTrace_1817721
  have hstable : (prefixWord ++ tailWord_1817721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817721).length < 2 ^ (prefixWord ++ tailWord_1817721).sum := by decide
  have hdescent : baseEnd_1817721 < baseStart_1817721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817747 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 6, 3]
def baseStart_1817747 : Nat := 118140960795 + 1817747 * 2 ^ 59
def prefixEnd_1817747 : Nat := 4983230072969 + 3 ^ 40 * 1817747 * 2
def baseEnd_1817747 : Nat := 622251946178936526801893

theorem tailTrace_1817747 : CollatzResearch.WordTrace tailWord_1817747 prefixEnd_1817747 622251946178936526801893 := by
  unfold tailWord_1817747
  simp only [CollatzResearch.WordTrace]
  refine ⟨66298679745620540316803495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44199119830413693544535663 66298679745620540316803495)
  ·
    refine ⟨99448019618430810475205243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66298679745620540316803495 99448019618430810475205243)
    ·
      refine ⟨149172029427646215712807865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99448019618430810475205243 149172029427646215712807865)
      ·
        refine ⟨111879022070734661784605899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149172029427646215712807865 111879022070734661784605899)
        ·
          refine ⟨167818533106101992676908849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111879022070734661784605899 167818533106101992676908849)
          ·
            refine ⟨125863899829576494507681637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167818533106101992676908849 125863899829576494507681637)
            ·
              refine ⟨23599481218045592720190307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125863899829576494507681637 23599481218045592720190307)
              ·
                refine ⟨35399221827068389080285461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23599481218045592720190307 35399221827068389080285461)
                ·
                  refine ⟨1659338523143830738138381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35399221827068389080285461 1659338523143830738138381)
                  ·
                    refine ⟨622251946178936526801893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659338523143830738138381 622251946178936526801893)
                    ·
                      rfl

theorem cell22_1817747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 3].length) (baseStart_1817747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817747 prefixEnd_1817747 := by exact prefixLift 1817747
  have htrace : WordTrace (prefixWord ++ tailWord_1817747) baseStart_1817747 baseEnd_1817747 := by
    simpa [prefixWord, tailWord_1817747, baseEnd_1817747] using wordTrace_append hprefix tailTrace_1817747
  have hstable : (prefixWord ++ tailWord_1817747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817747).length < 2 ^ (prefixWord ++ tailWord_1817747).sum := by decide
  have hdescent : baseEnd_1817747 < baseStart_1817747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817751 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 1, 4]
def baseStart_1817751 : Nat := 118140960795 + 1817751 * 2 ^ 59
def prefixEnd_1817751 : Nat := 4983230072969 + 3 ^ 40 * 1817751 * 2
def baseEnd_1817751 : Nat := 622253315460681849701881

theorem tailTrace_1817751 : CollatzResearch.WordTrace tailWord_1817751 prefixEnd_1817751 622253315460681849701881 := by
  unfold tailWord_1817751
  simp only [CollatzResearch.WordTrace]
  refine ⟨66298825637606048999949107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44199217091737365999966071 66298825637606048999949107)
  ·
    refine ⟨99448238456409073499923661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66298825637606048999949107 99448238456409073499923661)
    ·
      refine ⟨37293089421153402562471373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99448238456409073499923661 37293089421153402562471373)
      ·
        refine ⟨13984908532932525960926765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37293089421153402562471373 13984908532932525960926765)
        ·
          refine ⟨5244340699849697235347537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13984908532932525960926765 5244340699849697235347537)
          ·
            refine ⟨3933255524887272926510653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5244340699849697235347537 3933255524887272926510653)
            ·
              refine ⟨1474970821832727347441495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3933255524887272926510653 1474970821832727347441495)
              ·
                refine ⟨2212456232749091021162243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474970821832727347441495 2212456232749091021162243)
                ·
                  refine ⟨3318684349123636531743365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212456232749091021162243 3318684349123636531743365)
                  ·
                    refine ⟨622253315460681849701881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3318684349123636531743365 622253315460681849701881)
                    ·
                      rfl

theorem cell22_1817751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_1817751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817751 prefixEnd_1817751 := by exact prefixLift 1817751
  have htrace : WordTrace (prefixWord ++ tailWord_1817751) baseStart_1817751 baseEnd_1817751 := by
    simpa [prefixWord, tailWord_1817751, baseEnd_1817751] using wordTrace_append hprefix tailTrace_1817751
  have hstable : (prefixWord ++ tailWord_1817751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817751).length < 2 ^ (prefixWord ++ tailWord_1817751).sum := by decide
  have hdescent : baseEnd_1817751 < baseStart_1817751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817860 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1817860 : Nat := 118140960795 + 1817860 * 2 ^ 59
def prefixEnd_1817860 : Nat := 4983230072969 + 3 ^ 40 * 1817860 * 2
def baseEnd_1817860 : Nat := 622290628388241898726547

theorem tailTrace_1817860 : CollatzResearch.WordTrace tailWord_1817860 prefixEnd_1817860 622290628388241898726547 := by
  unfold tailWord_1817860
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151400597105580307833517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44201867462807440410444689 33151400597105580307833517)
  ·
    refine ⟨12431775223914592615437569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33151400597105580307833517 12431775223914592615437569)
    ·
      refine ⟨9323831417935944461578177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12431775223914592615437569 9323831417935944461578177)
      ·
        refine ⟨6992873563451958346183633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9323831417935944461578177 6992873563451958346183633)
        ·
          refine ⟨5244655172588968759637725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6992873563451958346183633 5244655172588968759637725)
          ·
            refine ⟨1966745689720863284864147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5244655172588968759637725 1966745689720863284864147)
            ·
              refine ⟨2950118534581294927296221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966745689720863284864147 2950118534581294927296221)
              ·
                refine ⟨1106294450467985597736083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2950118534581294927296221 1106294450467985597736083)
                ·
                  refine ⟨1659441675701978396604125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106294450467985597736083 1659441675701978396604125)
                  ·
                    refine ⟨622290628388241898726547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659441675701978396604125 622290628388241898726547)
                    ·
                      rfl

theorem cell22_1817860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1817860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817860 prefixEnd_1817860 := by exact prefixLift 1817860
  have htrace : WordTrace (prefixWord ++ tailWord_1817860) baseStart_1817860 baseEnd_1817860 := by
    simpa [prefixWord, tailWord_1817860, baseEnd_1817860] using wordTrace_append hprefix tailTrace_1817860
  have hstable : (prefixWord ++ tailWord_1817860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817860).length < 2 ^ (prefixWord ++ tailWord_1817860).sum := by decide
  have hdescent : baseEnd_1817860 < baseStart_1817860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817884 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_1817884 : Nat := 118140960795 + 1817884 * 2 ^ 59
def prefixEnd_1817884 : Nat := 4983230072969 + 3 ^ 40 * 1817884 * 2
def baseEnd_1817884 : Nat := 207432948026237945375491

theorem tailTrace_1817884 : CollatzResearch.WordTrace tailWord_1817884 prefixEnd_1817884 207432948026237945375491 := by
  unfold tailWord_1817884
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151838273062106357270353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44202451030749475143027137 33151838273062106357270353)
  ·
    refine ⟨24863878704796579767952765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33151838273062106357270353 24863878704796579767952765)
    ·
      refine ⟨9323954514298717412982287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24863878704796579767952765 9323954514298717412982287)
      ·
        refine ⟨13985931771448076119473431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323954514298717412982287 13985931771448076119473431)
        ·
          refine ⟨20978897657172114179210147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13985931771448076119473431 20978897657172114179210147)
          ·
            refine ⟨31468346485758171268815221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20978897657172114179210147 31468346485758171268815221)
            ·
              refine ⟨2950157483039828556451427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31468346485758171268815221 2950157483039828556451427)
              ·
                refine ⟨4425236224559742834677141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950157483039828556451427 4425236224559742834677141)
                ·
                  refine ⟨207432948026237945375491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4425236224559742834677141 207432948026237945375491)
                  ·
                    rfl

theorem cell22_1817884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_1817884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817884 prefixEnd_1817884 := by exact prefixLift 1817884
  have htrace : WordTrace (prefixWord ++ tailWord_1817884) baseStart_1817884 baseEnd_1817884 := by
    simpa [prefixWord, tailWord_1817884, baseEnd_1817884] using wordTrace_append hprefix tailTrace_1817884
  have hstable : (prefixWord ++ tailWord_1817884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817884).length < 2 ^ (prefixWord ++ tailWord_1817884).sum := by decide
  have hdescent : baseEnd_1817884 < baseStart_1817884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817890 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1817890 : Nat := 118140960795 + 1817890 * 2 ^ 59
def prefixEnd_1817890 : Nat := 4983230072969 + 3 ^ 40 * 1817890 * 2
def baseEnd_1817890 : Nat := 207433632667110606825485

theorem tailTrace_1817890 : CollatzResearch.WordTrace tailWord_1817890 prefixEnd_1817890 207433632667110606825485 := by
  unfold tailWord_1817890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575973846025618934814781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44202596922734983826172749 16575973846025618934814781)
  ·
    refine ⟨6215990192259607100555543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16575973846025618934814781 6215990192259607100555543)
    ·
      refine ⟨9323985288389410650833315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215990192259607100555543 9323985288389410650833315)
      ·
        refine ⟨13985977932584115976249973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323985288389410650833315 13985977932584115976249973)
        ·
          refine ⟨1311185431179760872773435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13985977932584115976249973 1311185431179760872773435)
          ·
            refine ⟨1966778146769641309160153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311185431179760872773435 1966778146769641309160153)
            ·
              refine ⟨1475083610077230981870115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966778146769641309160153 1475083610077230981870115)
              ·
                refine ⟨2212625415115846472805173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475083610077230981870115 2212625415115846472805173)
                ·
                  refine ⟨207433632667110606825485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2212625415115846472805173 207433632667110606825485)
                  ·
                    rfl

theorem cell22_1817890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1817890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817890 prefixEnd_1817890 := by exact prefixLift 1817890
  have htrace : WordTrace (prefixWord ++ tailWord_1817890) baseStart_1817890 baseEnd_1817890 := by
    simpa [prefixWord, tailWord_1817890, baseEnd_1817890] using wordTrace_append hprefix tailTrace_1817890
  have hstable : (prefixWord ++ tailWord_1817890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817890).length < 2 ^ (prefixWord ++ tailWord_1817890).sum := by decide
  have hdescent : baseEnd_1817890 < baseStart_1817890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817989 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1817989 : Nat := 118140960795 + 1817989 * 2 ^ 59
def prefixEnd_1817989 : Nat := 4983230072969 + 3 ^ 40 * 1817989 * 2
def baseEnd_1817989 : Nat := 622334787724528562251151

theorem tailTrace_1817989 : CollatzResearch.WordTrace tailWord_1817989 prefixEnd_1817989 622334787724528562251151 := by
  unfold tailWord_1817989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66307506210743815647113021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44205004140495877098075347 66307506210743815647113021)
  ·
    refine ⟨24865314829028930867667383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66307506210743815647113021 24865314829028930867667383)
    ·
      refine ⟨37297972243543396301501075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24865314829028930867667383 37297972243543396301501075)
      ·
        refine ⟨55946958365315094452251613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37297972243543396301501075 55946958365315094452251613)
        ·
          refine ⟨20980109386993160419594355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55946958365315094452251613 20980109386993160419594355)
          ·
            refine ⟨31470164080489740629391533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20980109386993160419594355 31470164080489740629391533)
            ·
              refine ⟨11801311530183652736021825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31470164080489740629391533 11801311530183652736021825)
              ·
                refine ⟨8850983647637739552016369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801311530183652736021825 8850983647637739552016369)
                ·
                  refine ⟨6638237735728304664012277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8850983647637739552016369 6638237735728304664012277)
                  ·
                    refine ⟨622334787724528562251151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6638237735728304664012277 622334787724528562251151)
                    ·
                      rfl

theorem cell22_1817989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1817989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817989 prefixEnd_1817989 := by exact prefixLift 1817989
  have htrace : WordTrace (prefixWord ++ tailWord_1817989) baseStart_1817989 baseEnd_1817989 := by
    simpa [prefixWord, tailWord_1817989, baseEnd_1817989] using wordTrace_append hprefix tailTrace_1817989
  have hstable : (prefixWord ++ tailWord_1817989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817989).length < 2 ^ (prefixWord ++ tailWord_1817989).sum := by decide
  have hdescent : baseEnd_1817989 < baseStart_1817989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817991 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 5]
def baseStart_1817991 : Nat := 118140960795 + 1817991 * 2 ^ 59
def prefixEnd_1817991 : Nat := 4983230072969 + 3 ^ 40 * 1817991 * 2
def baseEnd_1817991 : Nat := 207445157455133741233715

theorem tailTrace_1817991 : CollatzResearch.WordTrace tailWord_1817991 prefixEnd_1817991 207445157455133741233715 := by
  unfold tailWord_1817991
  simp only [CollatzResearch.WordTrace]
  refine ⟨66307579156736569988685827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44205052771157713325790551 66307579156736569988685827)
  ·
    refine ⟨99461368735104854983028741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66307579156736569988685827 99461368735104854983028741)
    ·
      refine ⟨18649006637832160309317889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99461368735104854983028741 18649006637832160309317889)
      ·
        refine ⟨13986754978374120231988417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18649006637832160309317889 13986754978374120231988417)
        ·
          refine ⟨10490066233780590173991313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13986754978374120231988417 10490066233780590173991313)
          ·
            refine ⟨7867549675335442630493485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10490066233780590173991313 7867549675335442630493485)
            ·
              refine ⟨2950331128250790986435057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7867549675335442630493485 2950331128250790986435057)
              ·
                refine ⟨2212748346188093239826293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950331128250790986435057 2212748346188093239826293)
                ·
                  refine ⟨207445157455133741233715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2212748346188093239826293 207445157455133741233715)
                  ·
                    rfl

theorem cell22_1817991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 5].length) (baseStart_1817991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1817991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1817991 prefixEnd_1817991 := by exact prefixLift 1817991
  have htrace : WordTrace (prefixWord ++ tailWord_1817991) baseStart_1817991 baseEnd_1817991 := by
    simpa [prefixWord, tailWord_1817991, baseEnd_1817991] using wordTrace_append hprefix tailTrace_1817991
  have hstable : (prefixWord ++ tailWord_1817991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817991).length < 2 ^ (prefixWord ++ tailWord_1817991).sum := by decide
  have hdescent : baseEnd_1817991 < baseStart_1817991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818019 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 6]
def baseStart_1818019 : Nat := 118140960795 + 1818019 * 2 ^ 59
def prefixEnd_1818019 : Nat := 4983230072969 + 3 ^ 40 * 1818019 * 2
def baseEnd_1818019 : Nat := 207448352445872828000353

theorem tailTrace_1818019 : CollatzResearch.WordTrace tailWord_1818019 prefixEnd_1818019 207448352445872828000353 := by
  unfold tailWord_1818019
  simp only [CollatzResearch.WordTrace]
  refine ⟨66308600400635130770705111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44205733600423420513803407 66308600400635130770705111)
  ·
    refine ⟨99462900600952696156057667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66308600400635130770705111 99462900600952696156057667)
    ·
      refine ⟨149194350901429044234086501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99462900600952696156057667 149194350901429044234086501)
      ·
        refine ⟨27973940794017945793891219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149194350901429044234086501 27973940794017945793891219)
        ·
          refine ⟨41960911191026918690836829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27973940794017945793891219 41960911191026918690836829)
          ·
            refine ⟨15735341696635094509063811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41960911191026918690836829 15735341696635094509063811)
            ·
              refine ⟨23603012544952641763595717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15735341696635094509063811 23603012544952641763595717)
              ·
                refine ⟨4425564852178620330674197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23603012544952641763595717 4425564852178620330674197)
                ·
                  refine ⟨207448352445872828000353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4425564852178620330674197 207448352445872828000353)
                  ·
                    rfl

theorem cell22_1818019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_1818019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818019 prefixEnd_1818019 := by exact prefixLift 1818019
  have htrace : WordTrace (prefixWord ++ tailWord_1818019) baseStart_1818019 baseEnd_1818019 := by
    simpa [prefixWord, tailWord_1818019, baseEnd_1818019] using wordTrace_append hprefix tailTrace_1818019
  have hstable : (prefixWord ++ tailWord_1818019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818019).length < 2 ^ (prefixWord ++ tailWord_1818019).sum := by decide
  have hdescent : baseEnd_1818019 < baseStart_1818019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818051 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 4, 3]
def baseStart_1818051 : Nat := 118140960795 + 1818051 * 2 ^ 59
def prefixEnd_1818051 : Nat := 4983230072969 + 3 ^ 40 * 1818051 * 2
def baseEnd_1818051 : Nat := 622356011591581067200961

theorem tailTrace_1818051 : CollatzResearch.WordTrace tailWord_1818051 prefixEnd_1818051 622356011591581067200961 := by
  unfold tailWord_1818051
  simp only [CollatzResearch.WordTrace]
  refine ⟨66309767536519200235870007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44206511691012800157246671 66309767536519200235870007)
  ·
    refine ⟨99464651304778800353805011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66309767536519200235870007 99464651304778800353805011)
    ·
      refine ⟨149196976957168200530707517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99464651304778800353805011 149196976957168200530707517)
      ·
        refine ⟨55948866358938075199015319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149196976957168200530707517 55948866358938075199015319)
        ·
          refine ⟨83923299538407112798522979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55948866358938075199015319 83923299538407112798522979)
          ·
            refine ⟨125884949307610669197784469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83923299538407112798522979 125884949307610669197784469)
            ·
              refine ⟨5900856998794250118646147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125884949307610669197784469 5900856998794250118646147)
              ·
                refine ⟨8851285498191375177969221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900856998794250118646147 8851285498191375177969221)
                ·
                  refine ⟨1659616030910882845869229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8851285498191375177969221 1659616030910882845869229)
                  ·
                    refine ⟨622356011591581067200961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659616030910882845869229 622356011591581067200961)
                    ·
                      rfl

theorem cell22_1818051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 3].length) (baseStart_1818051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818051 prefixEnd_1818051 := by exact prefixLift 1818051
  have htrace : WordTrace (prefixWord ++ tailWord_1818051) baseStart_1818051 baseEnd_1818051 := by
    simpa [prefixWord, tailWord_1818051, baseEnd_1818051] using wordTrace_append hprefix tailTrace_1818051
  have hstable : (prefixWord ++ tailWord_1818051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818051).length < 2 ^ (prefixWord ++ tailWord_1818051).sum := by decide
  have hdescent : baseEnd_1818051 < baseStart_1818051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818083 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 2, 4]
def baseStart_1818083 : Nat := 118140960795 + 1818083 * 2 ^ 59
def prefixEnd_1818083 : Nat := 4983230072969 + 3 ^ 40 * 1818083 * 2
def baseEnd_1818083 : Nat := 622366965845543650400863

theorem tailTrace_1818083 : CollatzResearch.WordTrace tailWord_1818083 prefixEnd_1818083 622366965845543650400863 := by
  unfold tailWord_1818083
  simp only [CollatzResearch.WordTrace]
  refine ⟨66310934672403269701034903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44207289781602179800689935 66310934672403269701034903)
  ·
    refine ⟨99466402008604904551552355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66310934672403269701034903 99466402008604904551552355)
    ·
      refine ⟨149199603012907356827328533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99466402008604904551552355 149199603012907356827328533)
      ·
        refine ⟨6993731391230032351281025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149199603012907356827328533 6993731391230032351281025)
        ·
          refine ⟨5245298543422524263460769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6993731391230032351281025 5245298543422524263460769)
          ·
            refine ⟨3933973907566893197595577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5245298543422524263460769 3933973907566893197595577)
            ·
              refine ⟨2950480430675169898196683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933973907566893197595577 2950480430675169898196683)
              ·
                refine ⟨4425720646012754847295025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950480430675169898196683 4425720646012754847295025)
                ·
                  refine ⟨3319290484509566135471269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425720646012754847295025 3319290484509566135471269)
                  ·
                    refine ⟨622366965845543650400863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3319290484509566135471269 622366965845543650400863)
                    ·
                      rfl

theorem cell22_1818083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].length) (baseStart_1818083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818083 prefixEnd_1818083 := by exact prefixLift 1818083
  have htrace : WordTrace (prefixWord ++ tailWord_1818083) baseStart_1818083 baseEnd_1818083 := by
    simpa [prefixWord, tailWord_1818083, baseEnd_1818083] using wordTrace_append hprefix tailTrace_1818083
  have hstable : (prefixWord ++ tailWord_1818083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818083).length < 2 ^ (prefixWord ++ tailWord_1818083).sum := by decide
  have hdescent : baseEnd_1818083 < baseStart_1818083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818141 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1818141 : Nat := 118140960795 + 1818141 * 2 ^ 59
def prefixEnd_1818141 : Nat := 4983230072969 + 3 ^ 40 * 1818141 * 2
def baseEnd_1818141 : Nat := 622386820430850832450685

theorem tailTrace_1818141 : CollatzResearch.WordTrace tailWord_1818141 prefixEnd_1818141 622386820430850832450685 := by
  unfold tailWord_1818141
  simp only [CollatzResearch.WordTrace]
  refine ⟨66313050106193145606646277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44208700070795430404430851 66313050106193145606646277)
  ·
    refine ⟨12433696894911214801246177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66313050106193145606646277 12433696894911214801246177)
    ·
      refine ⟨9325272671183411100934633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12433696894911214801246177 9325272671183411100934633)
      ·
        refine ⟨6993954503387558325700975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325272671183411100934633 6993954503387558325700975)
        ·
          refine ⟨10490931755081337488551463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993954503387558325700975 10490931755081337488551463)
          ·
            refine ⟨15736397632622006232827195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10490931755081337488551463 15736397632622006232827195)
            ·
              refine ⟨23604596448933009349240793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736397632622006232827195 23604596448933009349240793)
              ·
                refine ⟨17703447336699757011930595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23604596448933009349240793 17703447336699757011930595)
                ·
                  refine ⟨26555171005049635517895893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17703447336699757011930595 26555171005049635517895893)
                  ·
                    refine ⟨622386820430850832450685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26555171005049635517895893 622386820430850832450685)
                    ·
                      rfl

theorem cell22_1818141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1818141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818141 prefixEnd_1818141 := by exact prefixLift 1818141
  have htrace : WordTrace (prefixWord ++ tailWord_1818141) baseStart_1818141 baseEnd_1818141 := by
    simpa [prefixWord, tailWord_1818141, baseEnd_1818141] using wordTrace_append hprefix tailTrace_1818141
  have hstable : (prefixWord ++ tailWord_1818141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818141).length < 2 ^ (prefixWord ++ tailWord_1818141).sum := by decide
  have hdescent : baseEnd_1818141 < baseStart_1818141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818147 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 1, 3]
def baseStart_1818147 : Nat := 118140960795 + 1818147 * 2 ^ 59
def prefixEnd_1818147 : Nat := 4983230072969 + 3 ^ 40 * 1818147 * 2
def baseEnd_1818147 : Nat := 622388874353468816800667

theorem tailTrace_1818147 : CollatzResearch.WordTrace tailWord_1818147 prefixEnd_1818147 622388874353468816800667 := by
  unfold tailWord_1818147
  simp only [CollatzResearch.WordTrace]
  refine ⟨66313268944171408631364695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44208845962780939087576463 66313268944171408631364695)
  ·
    refine ⟨99469903416257112947047043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66313268944171408631364695 99469903416257112947047043)
    ·
      refine ⟨149204855124385669420570565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99469903416257112947047043 149204855124385669420570565)
      ·
        refine ⟨27975910335822313016356981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149204855124385669420570565 27975910335822313016356981)
        ·
          refine ⟨2622741593983341845283467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27975910335822313016356981 2622741593983341845283467)
          ·
            refine ⟨3934112390975012767925201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622741593983341845283467 3934112390975012767925201)
            ·
              refine ⟨2950584293231259575943901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934112390975012767925201 2950584293231259575943901)
              ·
                refine ⟨1106469109961722340978963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2950584293231259575943901 1106469109961722340978963)
                ·
                  refine ⟨1659703664942583511468445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106469109961722340978963 1659703664942583511468445)
                  ·
                    refine ⟨622388874353468816800667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659703664942583511468445 622388874353468816800667)
                    ·
                      rfl

theorem cell22_1818147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 3].length) (baseStart_1818147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818147 prefixEnd_1818147 := by exact prefixLift 1818147
  have htrace : WordTrace (prefixWord ++ tailWord_1818147) baseStart_1818147 baseEnd_1818147 := by
    simpa [prefixWord, tailWord_1818147, baseEnd_1818147] using wordTrace_append hprefix tailTrace_1818147
  have hstable : (prefixWord ++ tailWord_1818147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818147).length < 2 ^ (prefixWord ++ tailWord_1818147).sum := by decide
  have hdescent : baseEnd_1818147 < baseStart_1818147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818158 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1818158 : Nat := 118140960795 + 1818158 * 2 ^ 59
def prefixEnd_1818158 : Nat := 4983230072969 + 3 ^ 40 * 1818158 * 2
def baseEnd_1818158 : Nat := 622392639878268454775633

theorem tailTrace_1818158 : CollatzResearch.WordTrace tailWord_1818158 prefixEnd_1818158 622392639878268454775633 := by
  unfold tailWord_1818158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289208768391444688751891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44209113431421038340010085 8289208768391444688751891)
  ·
    refine ⟨12433813152587167033127837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289208768391444688751891 12433813152587167033127837)
    ·
      refine ⟨4662679932220187637422939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12433813152587167033127837 4662679932220187637422939)
      ·
        refine ⟨6994019898330281456134409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662679932220187637422939 6994019898330281456134409)
        ·
          refine ⟨5245514923747711092100807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6994019898330281456134409 5245514923747711092100807)
          ·
            refine ⟨7868272385621566638151211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245514923747711092100807 7868272385621566638151211)
            ·
              refine ⟨11802408578432349957226817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868272385621566638151211 11802408578432349957226817)
              ·
                refine ⟨8851806433824262467920113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11802408578432349957226817 8851806433824262467920113)
                ·
                  refine ⟨6638854825368196850940085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8851806433824262467920113 6638854825368196850940085)
                  ·
                    refine ⟨622392639878268454775633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6638854825368196850940085 622392639878268454775633)
                    ·
                      rfl

theorem cell22_1818158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1818158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818158 prefixEnd_1818158 := by exact prefixLift 1818158
  have htrace : WordTrace (prefixWord ++ tailWord_1818158) baseStart_1818158 baseEnd_1818158 := by
    simpa [prefixWord, tailWord_1818158, baseEnd_1818158] using wordTrace_append hprefix tailTrace_1818158
  have hstable : (prefixWord ++ tailWord_1818158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818158).length < 2 ^ (prefixWord ++ tailWord_1818158).sum := by decide
  have hdescent : baseEnd_1818158 < baseStart_1818158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818198 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1818198 : Nat := 118140960795 + 1818198 * 2 ^ 59
def prefixEnd_1818198 : Nat := 4983230072969 + 3 ^ 40 * 1818198 * 2
def baseEnd_1818198 : Nat := 622406332695721683775511

theorem tailTrace_1818198 : CollatzResearch.WordTrace tailWord_1818198 prefixEnd_1818198 622406332695721683775511 := by
  unfold tailWord_1818198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144695566686665271341953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44210086044657762894314165 4144695566686665271341953)
  ·
    refine ⟨3108521675014998953506465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4144695566686665271341953 3108521675014998953506465)
    ·
      refine ⟨2331391256261249215129849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3108521675014998953506465 2331391256261249215129849)
      ·
        refine ⟨1748543442195936911347387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2331391256261249215129849 1748543442195936911347387)
        ·
          refine ⟨2622815163293905367021081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748543442195936911347387 2622815163293905367021081)
          ·
            refine ⟨1967111372470429025265811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622815163293905367021081 1967111372470429025265811)
            ·
              refine ⟨2950667058705643537898717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967111372470429025265811 2950667058705643537898717)
              ·
                refine ⟨1106500147014616326712019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2950667058705643537898717 1106500147014616326712019)
                ·
                  refine ⟨1659750220521924490068029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1106500147014616326712019 1659750220521924490068029)
                  ·
                    refine ⟨622406332695721683775511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659750220521924490068029 622406332695721683775511)
                    ·
                      rfl

theorem cell22_1818198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1818198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818198 prefixEnd_1818198 := by exact prefixLift 1818198
  have htrace : WordTrace (prefixWord ++ tailWord_1818198) baseStart_1818198 baseEnd_1818198 := by
    simpa [prefixWord, tailWord_1818198, baseEnd_1818198] using wordTrace_append hprefix tailTrace_1818198
  have hstable : (prefixWord ++ tailWord_1818198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818198).length < 2 ^ (prefixWord ++ tailWord_1818198).sum := by decide
  have hdescent : baseEnd_1818198 < baseStart_1818198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818201 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_1818201 : Nat := 118140960795 + 1818201 * 2 ^ 59
def prefixEnd_1818201 : Nat := 4983230072969 + 3 ^ 40 * 1818201 * 2
def baseEnd_1818201 : Nat := 622407359657030675950501

theorem tailTrace_1818201 : CollatzResearch.WordTrace tailWord_1818201 prefixEnd_1818201 622407359657030675950501 := by
  unfold tailWord_1818201
  simp only [CollatzResearch.WordTrace]
  refine ⟨66315238485975775853830457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44210158990650517235886971 66315238485975775853830457)
  ·
    refine ⟨49736428864481831890372843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66315238485975775853830457 49736428864481831890372843)
    ·
      refine ⟨74604643296722747835559265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49736428864481831890372843 74604643296722747835559265)
      ·
        refine ⟨55953482472542060876669449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74604643296722747835559265 55953482472542060876669449)
        ·
          refine ⟨41965111854406545657502087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55953482472542060876669449 41965111854406545657502087)
          ·
            refine ⟨62947667781609818486253131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41965111854406545657502087 62947667781609818486253131)
            ·
              refine ⟨94421501672414727729379697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62947667781609818486253131 94421501672414727729379697)
              ·
                refine ⟨70816126254311045797034773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94421501672414727729379697 70816126254311045797034773)
                ·
                  refine ⟨3319505918170830271736005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70816126254311045797034773 3319505918170830271736005)
                  ·
                    refine ⟨622407359657030675950501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3319505918170830271736005 622407359657030675950501)
                    ·
                      rfl

theorem cell22_1818201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_1818201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818201 prefixEnd_1818201 := by exact prefixLift 1818201
  have htrace : WordTrace (prefixWord ++ tailWord_1818201) baseStart_1818201 baseEnd_1818201 := by
    simpa [prefixWord, tailWord_1818201, baseEnd_1818201] using wordTrace_append hprefix tailTrace_1818201
  have hstable : (prefixWord ++ tailWord_1818201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818201).length < 2 ^ (prefixWord ++ tailWord_1818201).sum := by decide
  have hdescent : baseEnd_1818201 < baseStart_1818201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818218 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1818218 : Nat := 118140960795 + 1818218 * 2 ^ 59
def prefixEnd_1818218 : Nat := 4983230072969 + 3 ^ 40 * 1818218 * 2
def baseEnd_1818218 : Nat := 622413179104448298275449

theorem tailTrace_1818218 : CollatzResearch.WordTrace tailWord_1818218 prefixEnd_1818218 622413179104448298275449 := by
  unfold tailWord_1818218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578964631728546939299827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44210572351276125171466205 16578964631728546939299827)
  ·
    refine ⟨24868446947592820408949741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16578964631728546939299827 24868446947592820408949741)
    ·
      refine ⟨9325667605347307653356153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24868446947592820408949741 9325667605347307653356153)
      ·
        refine ⟨6994250704010480740017115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325667605347307653356153 6994250704010480740017115)
        ·
          refine ⟨10491376056015721110025673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994250704010480740017115 10491376056015721110025673)
          ·
            refine ⟨7868532042011790832519255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10491376056015721110025673 7868532042011790832519255)
            ·
              refine ⟨11802798063017686248778883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868532042011790832519255 11802798063017686248778883)
              ·
                refine ⟨17704197094526529373168325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11802798063017686248778883 17704197094526529373168325)
                ·
                  refine ⟨3319536955223724257469061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17704197094526529373168325 3319536955223724257469061)
                  ·
                    refine ⟨622413179104448298275449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3319536955223724257469061 622413179104448298275449)
                    ·
                      rfl

theorem cell22_1818218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1818218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818218 prefixEnd_1818218 := by exact prefixLift 1818218
  have htrace : WordTrace (prefixWord ++ tailWord_1818218) baseStart_1818218 baseEnd_1818218 := by
    simpa [prefixWord, tailWord_1818218, baseEnd_1818218] using wordTrace_append hprefix tailTrace_1818218
  have hstable : (prefixWord ++ tailWord_1818218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818218).length < 2 ^ (prefixWord ++ tailWord_1818218).sum := by decide
  have hdescent : baseEnd_1818218 < baseStart_1818218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818222 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_1818222 : Nat := 118140960795 + 1818222 * 2 ^ 59
def prefixEnd_1818222 : Nat := 4983230072969 + 3 ^ 40 * 1818222 * 2
def baseEnd_1818222 : Nat := 207471516128731207058479

theorem tailTrace_1818222 : CollatzResearch.WordTrace tailWord_1818222 prefixEnd_1818222 207471516128731207058479 := by
  unfold tailWord_1818222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289500552362462055043115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44210669612599797626896613 8289500552362462055043115)
  ·
    refine ⟨12434250828543693082564673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289500552362462055043115 12434250828543693082564673)
    ·
      refine ⟨9325688121407769811923505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12434250828543693082564673 9325688121407769811923505)
      ·
        refine ⟨6994266091055827358942629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325688121407769811923505 6994266091055827358942629)
        ·
          refine ⟨1311424892072967629801743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6994266091055827358942629 1311424892072967629801743)
          ·
            refine ⟨1967137338109451444702615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311424892072967629801743 1967137338109451444702615)
            ·
              refine ⟨2950706007164177167053923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967137338109451444702615 2950706007164177167053923)
              ·
                refine ⟨4426059010746265750580885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950706007164177167053923 4426059010746265750580885)
                ·
                  refine ⟨207471516128731207058479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4426059010746265750580885 207471516128731207058479)
                  ·
                    rfl

theorem cell22_1818222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_1818222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818222 prefixEnd_1818222 := by exact prefixLift 1818222
  have htrace : WordTrace (prefixWord ++ tailWord_1818222) baseStart_1818222 baseEnd_1818222 := by
    simpa [prefixWord, tailWord_1818222, baseEnd_1818222] using wordTrace_append hprefix tailTrace_1818222
  have hstable : (prefixWord ++ tailWord_1818222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818222).length < 2 ^ (prefixWord ++ tailWord_1818222).sum := by decide
  have hdescent : baseEnd_1818222 < baseStart_1818222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818237 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1818237 : Nat := 118140960795 + 1818237 * 2 ^ 59
def prefixEnd_1818237 : Nat := 4983230072969 + 3 ^ 40 * 1818237 * 2
def baseEnd_1818237 : Nat := 622419683192738582050391

theorem tailTrace_1818237 : CollatzResearch.WordTrace tailWord_1818237 prefixEnd_1818237 622419683192738582050391 := by
  unfold tailWord_1818237
  simp only [CollatzResearch.WordTrace]
  refine ⟨66316551513845354002140965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44211034342563569334760643 66316551513845354002140965)
  ·
    refine ⟨12434353408846003875401431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66316551513845354002140965 12434353408846003875401431)
    ·
      refine ⟨18651530113269005813102147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434353408846003875401431 18651530113269005813102147)
      ·
        refine ⟨27977295169903508719653221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651530113269005813102147 27977295169903508719653221)
        ·
          refine ⟨5245742844356907884934979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27977295169903508719653221 5245742844356907884934979)
          ·
            refine ⟨7868614266535361827402469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245742844356907884934979 7868614266535361827402469)
            ·
              refine ⟨1475365174975380342637963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7868614266535361827402469 1475365174975380342637963)
              ·
                refine ⟨2213047762463070513956945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475365174975380342637963 2213047762463070513956945)
                ·
                  refine ⟨1659785821847302885467709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2213047762463070513956945 1659785821847302885467709)
                  ·
                    refine ⟨622419683192738582050391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659785821847302885467709 622419683192738582050391)
                    ·
                      rfl

theorem cell22_1818237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1818237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818237 prefixEnd_1818237 := by exact prefixLift 1818237
  have htrace : WordTrace (prefixWord ++ tailWord_1818237) baseStart_1818237 baseEnd_1818237 := by
    simpa [prefixWord, tailWord_1818237, baseEnd_1818237] using wordTrace_append hprefix tailTrace_1818237
  have hstable : (prefixWord ++ tailWord_1818237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818237).length < 2 ^ (prefixWord ++ tailWord_1818237).sum := by decide
  have hdescent : baseEnd_1818237 < baseStart_1818237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818261 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 9]
def baseStart_1818261 : Nat := 118140960795 + 1818261 * 2 ^ 59
def prefixEnd_1818261 : Nat := 4983230072969 + 3 ^ 40 * 1818261 * 2
def baseEnd_1818261 : Nat := 207475966294403506483439

theorem tailTrace_1818261 : CollatzResearch.WordTrace tailWord_1818261 prefixEnd_1818261 207475966294403506483439 := by
  unfold tailWord_1818261
  simp only [CollatzResearch.WordTrace]
  refine ⟨66317426865758406101014637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44211617910505604067343091 66317426865758406101014637)
  ·
    refine ⟨24869035074659402287880489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66317426865758406101014637 24869035074659402287880489)
    ·
      refine ⟨18651776305994551715910367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24869035074659402287880489 18651776305994551715910367)
      ·
        refine ⟨27977664458991827573865551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651776305994551715910367 27977664458991827573865551)
        ·
          refine ⟨41966496688487741360798327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27977664458991827573865551 41966496688487741360798327)
          ·
            refine ⟨62949745032731612041197491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41966496688487741360798327 62949745032731612041197491)
            ·
              refine ⟨94424617549097418061796237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62949745032731612041197491 94424617549097418061796237)
              ·
                refine ⟨35409231580911531773173589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94424617549097418061796237 35409231580911531773173589)
                ·
                  refine ⟨207475966294403506483439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35409231580911531773173589 207475966294403506483439)
                  ·
                    rfl

theorem cell22_1818261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_1818261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818261 prefixEnd_1818261 := by exact prefixLift 1818261
  have htrace : WordTrace (prefixWord ++ tailWord_1818261) baseStart_1818261 baseEnd_1818261 := by
    simpa [prefixWord, tailWord_1818261, baseEnd_1818261] using wordTrace_append hprefix tailTrace_1818261
  have hstable : (prefixWord ++ tailWord_1818261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818261).length < 2 ^ (prefixWord ++ tailWord_1818261).sum := by decide
  have hdescent : baseEnd_1818261 < baseStart_1818261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818340 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1818340 : Nat := 118140960795 + 1818340 * 2 ^ 59
def prefixEnd_1818340 : Nat := 4983230072969 + 3 ^ 40 * 1818340 * 2
def baseEnd_1818340 : Nat := 207484980732560215575025

theorem tailTrace_1818340 : CollatzResearch.WordTrace tailWord_1818340 prefixEnd_1818340 207484980732560215575025 := by
  unfold tailWord_1818340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33160154116236101296570237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44213538821648135062093649 33160154116236101296570237)
  ·
    refine ⟨12435057793588537986213839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33160154116236101296570237 12435057793588537986213839)
    ·
      refine ⟨18652586690382806979320759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435057793588537986213839 18652586690382806979320759)
      ·
        refine ⟨27978880035574210468981139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18652586690382806979320759 27978880035574210468981139)
        ·
          refine ⟨41968320053361315703471709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27978880035574210468981139 41968320053361315703471709)
          ·
            refine ⟨15738120020010493388801891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41968320053361315703471709 15738120020010493388801891)
            ·
              refine ⟨23607180030015740083202837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15738120020010493388801891 23607180030015740083202837)
              ·
                refine ⟨1106586563906987816400133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23607180030015740083202837 1106586563906987816400133)
                ·
                  refine ⟨207484980732560215575025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106586563906987816400133 207484980732560215575025)
                  ·
                    rfl

theorem cell22_1818340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1818340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818340 prefixEnd_1818340 := by exact prefixLift 1818340
  have htrace : WordTrace (prefixWord ++ tailWord_1818340) baseStart_1818340 baseEnd_1818340 := by
    simpa [prefixWord, tailWord_1818340, baseEnd_1818340] using wordTrace_append hprefix tailTrace_1818340
  have hstable : (prefixWord ++ tailWord_1818340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818340).length < 2 ^ (prefixWord ++ tailWord_1818340).sum := by decide
  have hdescent : baseEnd_1818340 < baseStart_1818340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818353 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1818353 : Nat := 118140960795 + 1818353 * 2 ^ 59
def prefixEnd_1818353 : Nat := 4983230072969 + 3 ^ 40 * 1818353 * 2
def baseEnd_1818353 : Nat := 622459392363352946150035

theorem tailTrace_1818353 : CollatzResearch.WordTrace tailWord_1818353 prefixEnd_1818353 622459392363352946150035 := by
  unfold tailWord_1818353
  simp only [CollatzResearch.WordTrace]
  refine ⟨66320782381425105813363713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44213854920950070542242475 66320782381425105813363713)
  ·
    refine ⟨49740586786068829360022785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66320782381425105813363713 49740586786068829360022785)
    ·
      refine ⟨37305440089551622020017089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49740586786068829360022785 37305440089551622020017089)
      ·
        refine ⟨27979080067163716515012817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37305440089551622020017089 27979080067163716515012817)
        ·
          refine ⟨20984310050372787386259613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27979080067163716515012817 20984310050372787386259613)
          ·
            refine ⟨7869116268889795269847355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20984310050372787386259613 7869116268889795269847355)
            ·
              refine ⟨11803674403334692904771033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869116268889795269847355 11803674403334692904771033)
              ·
                refine ⟨8852755802501019678578275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11803674403334692904771033 8852755802501019678578275)
                ·
                  refine ⟨13279133703751529517867413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8852755802501019678578275 13279133703751529517867413)
                  ·
                    refine ⟨622459392363352946150035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13279133703751529517867413 622459392363352946150035)
                    ·
                      rfl

theorem cell22_1818353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1818353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818353 prefixEnd_1818353 := by exact prefixLift 1818353
  have htrace : WordTrace (prefixWord ++ tailWord_1818353) baseStart_1818353 baseEnd_1818353 := by
    simpa [prefixWord, tailWord_1818353, baseEnd_1818353] using wordTrace_append hprefix tailTrace_1818353
  have hstable : (prefixWord ++ tailWord_1818353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818353).length < 2 ^ (prefixWord ++ tailWord_1818353).sum := by decide
  have hdescent : baseEnd_1818353 < baseStart_1818353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818355 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 2, 3]
def baseStart_1818355 : Nat := 118140960795 + 1818355 * 2 ^ 59
def prefixEnd_1818355 : Nat := 4983230072969 + 3 ^ 40 * 1818355 * 2
def baseEnd_1818355 : Nat := 622460077004225607600029

theorem tailTrace_1818355 : CollatzResearch.WordTrace tailWord_1818355 prefixEnd_1818355 622460077004225607600029 := by
  unfold tailWord_1818355
  simp only [CollatzResearch.WordTrace]
  refine ⟨66320855327417860154936519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44213903551611906769957679 66320855327417860154936519)
  ·
    refine ⟨99481282991126790232404779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66320855327417860154936519 99481282991126790232404779)
    ·
      refine ⟨149221924486690185348607169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99481282991126790232404779 149221924486690185348607169)
      ·
        refine ⟨111916443365017639011455377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149221924486690185348607169 111916443365017639011455377)
        ·
          refine ⟨83937332523763229258591533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111916443365017639011455377 83937332523763229258591533)
          ·
            refine ⟨31476499696411210971971825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83937332523763229258591533 31476499696411210971971825)
            ·
              refine ⟨23607374772308408228978869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31476499696411210971971825 23607374772308408228978869)
              ·
                refine ⟨2213191384903913271466769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23607374772308408228978869 2213191384903913271466769)
                ·
                  refine ⟨1659893538677934953600077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2213191384903913271466769 1659893538677934953600077)
                  ·
                    refine ⟨622460077004225607600029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659893538677934953600077 622460077004225607600029)
                    ·
                      rfl

theorem cell22_1818355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 3].length) (baseStart_1818355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818355 prefixEnd_1818355 := by exact prefixLift 1818355
  have htrace : WordTrace (prefixWord ++ tailWord_1818355) baseStart_1818355 baseEnd_1818355 := by
    simpa [prefixWord, tailWord_1818355, baseEnd_1818355] using wordTrace_append hprefix tailTrace_1818355
  have hstable : (prefixWord ++ tailWord_1818355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818355).length < 2 ^ (prefixWord ++ tailWord_1818355).sum := by decide
  have hdescent : baseEnd_1818355 < baseStart_1818355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818370 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1818370 : Nat := 118140960795 + 1818370 * 2 ^ 59
def prefixEnd_1818370 : Nat := 4983230072969 + 3 ^ 40 * 1818370 * 2
def baseEnd_1818370 : Nat := 622465211810770568474983

theorem tailTrace_1818370 : CollatzResearch.WordTrace tailWord_1818370 prefixEnd_1818370 622465211810770568474983 := by
  unfold tailWord_1818370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580350605590879429183141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44214268281575678477821709 16580350605590879429183141)
  ·
    refine ⟨3108815738548289892971839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16580350605590879429183141 3108815738548289892971839)
    ·
      refine ⟨4663223607822434839457759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108815738548289892971839 4663223607822434839457759)
      ·
        refine ⟨6994835411733652259186639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663223607822434839457759 6994835411733652259186639)
        ·
          refine ⟨10492253117600478388779959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994835411733652259186639 10492253117600478388779959)
          ·
            refine ⟨15738379676400717583169939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492253117600478388779959 15738379676400717583169939)
            ·
              refine ⟨23607569514601076374754909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15738379676400717583169939 23607569514601076374754909)
              ·
                refine ⟨8852838567975403640533091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23607569514601076374754909 8852838567975403640533091)
                ·
                  refine ⟨13279257851963105460799637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8852838567975403640533091 13279257851963105460799637)
                  ·
                    refine ⟨622465211810770568474983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13279257851963105460799637 622465211810770568474983)
                    ·
                      rfl

theorem cell22_1818370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1818370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818370 prefixEnd_1818370 := by exact prefixLift 1818370
  have htrace : WordTrace (prefixWord ++ tailWord_1818370) baseStart_1818370 baseEnd_1818370 := by
    simpa [prefixWord, tailWord_1818370, baseEnd_1818370] using wordTrace_append hprefix tailTrace_1818370
  have hstable : (prefixWord ++ tailWord_1818370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818370).length < 2 ^ (prefixWord ++ tailWord_1818370).sum := by decide
  have hdescent : baseEnd_1818370 < baseStart_1818370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818490 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1818490 : Nat := 118140960795 + 1818490 * 2 ^ 59
def prefixEnd_1818490 : Nat := 4983230072969 + 3 ^ 40 * 1818490 * 2
def baseEnd_1818490 : Nat := 622506290263130255474615

theorem tailTrace_1818490 : CollatzResearch.WordTrace tailWord_1818490 prefixEnd_1818490 622506290263130255474615 := by
  unfold tailWord_1818490
  simp only [CollatzResearch.WordTrace]
  refine ⟨16581444795482194552775231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44217186121285852140733949 16581444795482194552775231)
  ·
    refine ⟨24872167193223291829162847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16581444795482194552775231 24872167193223291829162847)
    ·
      refine ⟨37308250789834937743744271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24872167193223291829162847 37308250789834937743744271)
      ·
        refine ⟨55962376184752406615616407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37308250789834937743744271 55962376184752406615616407)
        ·
          refine ⟨83943564277128609923424611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55962376184752406615616407 83943564277128609923424611)
          ·
            refine ⟨125915346415692914885136917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83943564277128609923424611 125915346415692914885136917)
            ·
              refine ⟨5902281863235605385240793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125915346415692914885136917 5902281863235605385240793)
              ·
                refine ⟨4426711397426704038930595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902281863235605385240793 4426711397426704038930595)
                ·
                  refine ⟨6640067096140056058395893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426711397426704038930595 6640067096140056058395893)
                  ·
                    refine ⟨622506290263130255474615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6640067096140056058395893 622506290263130255474615)
                    ·
                      rfl

theorem cell22_1818490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1818490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818490 prefixEnd_1818490 := by exact prefixLift 1818490
  have htrace : WordTrace (prefixWord ++ tailWord_1818490) baseStart_1818490 baseEnd_1818490 := by
    simpa [prefixWord, tailWord_1818490, baseEnd_1818490] using wordTrace_append hprefix tailTrace_1818490
  have hstable : (prefixWord ++ tailWord_1818490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818490).length < 2 ^ (prefixWord ++ tailWord_1818490).sum := by decide
  have hdescent : baseEnd_1818490 < baseStart_1818490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818505 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_1818505 : Nat := 118140960795 + 1818505 * 2 ^ 59
def prefixEnd_1818505 : Nat := 4983230072969 + 3 ^ 40 * 1818505 * 2
def baseEnd_1818505 : Nat := 622511425069675216349569

theorem tailTrace_1818505 : CollatzResearch.WordTrace tailWord_1818505 prefixEnd_1818505 622511425069675216349569 := by
  unfold tailWord_1818505
  simp only [CollatzResearch.WordTrace]
  refine ⟨66326326276874435772896969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44217550851249623848597979 66326326276874435772896969)
  ·
    refine ⟨49744744707655826829672727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66326326276874435772896969 49744744707655826829672727)
    ·
      refine ⟨74617117061483740244509091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49744744707655826829672727 74617117061483740244509091)
      ·
        refine ⟨111925675592225610366763637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74617117061483740244509091 111925675592225610366763637)
        ·
          refine ⟨10493032086771150971884091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111925675592225610366763637 10493032086771150971884091)
          ·
            refine ⟨15739548130156726457826137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10493032086771150971884091 15739548130156726457826137)
            ·
              refine ⟨11804661097617544843369603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15739548130156726457826137 11804661097617544843369603)
              ·
                refine ⟨17706991646426317265054405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804661097617544843369603 17706991646426317265054405)
                ·
                  refine ⟨3320060933704934487197701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17706991646426317265054405 3320060933704934487197701)
                  ·
                    refine ⟨622511425069675216349569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3320060933704934487197701 622511425069675216349569)
                    ·
                      rfl

theorem cell22_1818505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_1818505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818505 prefixEnd_1818505 := by exact prefixLift 1818505
  have htrace : WordTrace (prefixWord ++ tailWord_1818505) baseStart_1818505 baseEnd_1818505 := by
    simpa [prefixWord, tailWord_1818505, baseEnd_1818505] using wordTrace_append hprefix tailTrace_1818505
  have hstable : (prefixWord ++ tailWord_1818505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818505).length < 2 ^ (prefixWord ++ tailWord_1818505).sum := by decide
  have hdescent : baseEnd_1818505 < baseStart_1818505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818524 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1818524 : Nat := 118140960795 + 1818524 * 2 ^ 59
def prefixEnd_1818524 : Nat := 4983230072969 + 3 ^ 40 * 1818524 * 2
def baseEnd_1818524 : Nat := 622517929157965500124511

theorem tailTrace_1818524 : CollatzResearch.WordTrace tailWord_1818524 prefixEnd_1818524 622517929157965500124511 := by
  unfold tailWord_1818524
  simp only [CollatzResearch.WordTrace]
  refine ⟨33163509631902801008919313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44218012842537068011892417 33163509631902801008919313)
  ·
    refine ⟨24872632223927100756689485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33163509631902801008919313 24872632223927100756689485)
    ·
      refine ⟨9327237083972662783758557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24872632223927100756689485 9327237083972662783758557)
      ·
        refine ⟨3497713906489748543909459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9327237083972662783758557 3497713906489748543909459)
        ·
          refine ⟨5246570859734622815864189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497713906489748543909459 5246570859734622815864189)
          ·
            refine ⟨1967464072400483555949071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5246570859734622815864189 1967464072400483555949071)
            ·
              refine ⟨2951196108600725333923607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967464072400483555949071 2951196108600725333923607)
              ·
                refine ⟨4426794162901088000885411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951196108600725333923607 4426794162901088000885411)
                ·
                  refine ⟨6640191244351632001328117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426794162901088000885411 6640191244351632001328117)
                  ·
                    refine ⟨622517929157965500124511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6640191244351632001328117 622517929157965500124511)
                    ·
                      rfl

theorem cell22_1818524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1818524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818524 prefixEnd_1818524 := by exact prefixLift 1818524
  have htrace : WordTrace (prefixWord ++ tailWord_1818524) baseStart_1818524 baseEnd_1818524 := by
    simpa [prefixWord, tailWord_1818524, baseEnd_1818524] using wordTrace_append hprefix tailTrace_1818524
  have hstable : (prefixWord ++ tailWord_1818524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818524).length < 2 ^ (prefixWord ++ tailWord_1818524).sum := by decide
  have hdescent : baseEnd_1818524 < baseStart_1818524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818640 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_1818640 : Nat := 118140960795 + 1818640 * 2 ^ 59
def prefixEnd_1818640 : Nat := 4983230072969 + 3 ^ 40 * 1818640 * 2
def baseEnd_1818640 : Nat := 622557638328579864224155

theorem tailTrace_1818640 : CollatzResearch.WordTrace tailWord_1818640 prefixEnd_1818640 622557638328579864224155 := by
  unfold tailWord_1818640
  simp only [CollatzResearch.WordTrace]
  refine ⟨33165625065692676914530687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44220833420923569219374249 33165625065692676914530687)
  ·
    refine ⟨49748437598539015371796031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33165625065692676914530687 49748437598539015371796031)
    ·
      refine ⟨74622656397808523057694047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49748437598539015371796031 74622656397808523057694047)
      ·
        refine ⟨111933984596712784586541071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74622656397808523057694047 111933984596712784586541071)
        ·
          refine ⟨167900976895069176879811607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111933984596712784586541071 167900976895069176879811607)
          ·
            refine ⟨251851465342603765319717411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167900976895069176879811607 251851465342603765319717411)
            ·
              refine ⟨377777198013905647979576117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251851465342603765319717411 377777198013905647979576117)
              ·
                refine ⟨35416612313803654498085261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377777198013905647979576117 35416612313803654498085261)
                ·
                  refine ⟨13281229617676370436781973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35416612313803654498085261 13281229617676370436781973)
                  ·
                    refine ⟨622557638328579864224155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13281229617676370436781973 622557638328579864224155)
                    ·
                      rfl

theorem cell22_1818640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_1818640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818640 prefixEnd_1818640 := by exact prefixLift 1818640
  have htrace : WordTrace (prefixWord ++ tailWord_1818640) baseStart_1818640 baseEnd_1818640 := by
    simpa [prefixWord, tailWord_1818640, baseEnd_1818640] using wordTrace_append hprefix tailTrace_1818640
  have hstable : (prefixWord ++ tailWord_1818640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818640).length < 2 ^ (prefixWord ++ tailWord_1818640).sum := by decide
  have hdescent : baseEnd_1818640 < baseStart_1818640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818706 : List Nat := [3, 2, 2, 1, 4, 2, 2, 6]
def baseStart_1818706 : Nat := 118140960795 + 1818706 * 2 ^ 59
def prefixEnd_1818706 : Nat := 4983230072969 + 3 ^ 40 * 1818706 * 2
def baseEnd_1818706 : Nat := 69175581275264188008217

theorem tailTrace_1818706 : CollatzResearch.WordTrace tailWord_1818706 prefixEnd_1818706 69175581275264188008217 := by
  unfold tailWord_1818706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583414337286561775240993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44222438232764164733975981 16583414337286561775240993)
  ·
    refine ⟨12437560752964921331430745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16583414337286561775240993 12437560752964921331430745)
    ·
      refine ⟨9328170564723690998573059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12437560752964921331430745 9328170564723690998573059)
      ·
        refine ⟨13992255847085536497859589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9328170564723690998573059 13992255847085536497859589)
        ·
          refine ⟨2623547971328538093348673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13992255847085536497859589 2623547971328538093348673)
          ·
            refine ⟨1967660978496403570011505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2623547971328538093348673 1967660978496403570011505)
            ·
              refine ⟨1475745733872302677508629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967660978496403570011505 1475745733872302677508629)
              ·
                refine ⟨69175581275264188008217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1475745733872302677508629 69175581275264188008217)
                ·
                  rfl

theorem cell22_1818706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_1818706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818706 prefixEnd_1818706 := by exact prefixLift 1818706
  have htrace : WordTrace (prefixWord ++ tailWord_1818706) baseStart_1818706 baseEnd_1818706 := by
    simpa [prefixWord, tailWord_1818706, baseEnd_1818706] using wordTrace_append hprefix tailTrace_1818706
  have hstable : (prefixWord ++ tailWord_1818706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818706).length < 2 ^ (prefixWord ++ tailWord_1818706).sum := by decide
  have hdescent : baseEnd_1818706 < baseStart_1818706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818734 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1818734 : Nat := 118140960795 + 1818734 * 2 ^ 59
def prefixEnd_1818734 : Nat := 4983230072969 + 3 ^ 40 * 1818734 * 2
def baseEnd_1818734 : Nat := 207529938816531650791289

theorem tailTrace_1818734 : CollatzResearch.WordTrace tailWord_1818734 prefixEnd_1818734 207529938816531650791289 := by
  unfold tailWord_1818734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291834824130600985372907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44223119062029871921988837 8291834824130600985372907)
  ·
    refine ⟨12437752236195901478059361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8291834824130600985372907 12437752236195901478059361)
    ·
      refine ⟨9328314177146926108544521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12437752236195901478059361 9328314177146926108544521)
      ·
        refine ⟨6996235632860194581408391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9328314177146926108544521 6996235632860194581408391)
        ·
          refine ⟨10494353449290291872112587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6996235632860194581408391 10494353449290291872112587)
          ·
            refine ⟨15741530173935437808168881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494353449290291872112587 15741530173935437808168881)
            ·
              refine ⟨11806147630451578356126661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15741530173935437808168881 11806147630451578356126661)
              ·
                refine ⟨2213652680709670941773749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11806147630451578356126661 2213652680709670941773749)
                ·
                  refine ⟨207529938816531650791289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2213652680709670941773749 207529938816531650791289)
                  ·
                    rfl

theorem cell22_1818734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1818734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818734 prefixEnd_1818734 := by exact prefixLift 1818734
  have htrace : WordTrace (prefixWord ++ tailWord_1818734) baseStart_1818734 baseEnd_1818734 := by
    simpa [prefixWord, tailWord_1818734, baseEnd_1818734] using wordTrace_append hprefix tailTrace_1818734
  have hstable : (prefixWord ++ tailWord_1818734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818734).length < 2 ^ (prefixWord ++ tailWord_1818734).sum := by decide
  have hdescent : baseEnd_1818734 < baseStart_1818734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
