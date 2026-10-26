import V185TrunkScan23Chunk1180

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6997818 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2]
def baseStart_6997818 : Nat := 118140960795 + 6997818 * 2 ^ 59
def prefixEnd_6997818 : Nat := 4983230072969 + 3 ^ 40 * 6997818 * 2
def baseEnd_6997818 : Nat := 3593244166684607238592627

theorem tailTrace_6997818 : CollatzResearch.WordTrace tailWord_6997818 prefixEnd_6997818 3593244166684607238592627 := by
  unfold tailWord_6997818
  simp only [CollatzResearch.WordTrace]
  refine ⟨63807847640526998252544527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170154260374738662006785405 63807847640526998252544527)
  ·
    refine ⟨95711771460790497378816791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63807847640526998252544527 95711771460790497378816791)
    ·
      refine ⟨143567657191185746068225187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95711771460790497378816791 143567657191185746068225187)
      ·
        refine ⟨215351485786778619102337781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143567657191185746068225187 215351485786778619102337781)
        ·
          refine ⟨20189201792510495540844167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215351485786778619102337781 20189201792510495540844167)
          ·
            refine ⟨30283802688765743311266251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20189201792510495540844167 30283802688765743311266251)
            ·
              refine ⟨45425704033148614966899377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30283802688765743311266251 45425704033148614966899377)
              ·
                refine ⟨34069278024861461225174533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45425704033148614966899377 34069278024861461225174533)
                ·
                  refine ⟨6387989629661523979720225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34069278024861461225174533 6387989629661523979720225)
                  ·
                    refine ⟨4790992222246142984790169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6387989629661523979720225 4790992222246142984790169)
                    ·
                      refine ⟨3593244166684607238592627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790992222246142984790169 3593244166684607238592627)
                      ·
                        rfl

theorem cell23_6997818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_6997818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997818 prefixEnd_6997818 := by exact prefixLift 6997818
  have htrace : WordTrace (prefixWord ++ tailWord_6997818) baseStart_6997818 baseEnd_6997818 := by
    simpa [prefixWord, tailWord_6997818, baseEnd_6997818] using wordTrace_append hprefix tailTrace_6997818
  have hstable : (prefixWord ++ tailWord_6997818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997818).length < 2 ^ (prefixWord ++ tailWord_6997818).sum := by decide
  have hdescent : baseEnd_6997818 < baseStart_6997818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997821 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6997821 : Nat := 118140960795 + 6997821 * 2 ^ 59
def prefixEnd_6997821 : Nat := 4983230072969 + 3 ^ 40 * 6997821 * 2
def baseEnd_6997821 : Nat := 3593245707126570726855113

theorem tailTrace_6997821 : CollatzResearch.WordTrace tailWord_6997821 prefixEnd_6997821 3593245707126570726855113 := by
  unfold tailWord_6997821
  simp only [CollatzResearch.WordTrace]
  refine ⟨255231499981097124522537317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170154333320731416348358211 255231499981097124522537317)
  ·
    refine ⟨47855906246455710847975747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255231499981097124522537317 47855906246455710847975747)
    ·
      refine ⟨71783859369683566271963621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47855906246455710847975747 71783859369683566271963621)
      ·
        refine ⟨13459473631815668675993179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71783859369683566271963621 13459473631815668675993179)
        ·
          refine ⟨20189210447723503013989769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13459473631815668675993179 20189210447723503013989769)
          ·
            refine ⟨15141907835792627260492327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20189210447723503013989769 15141907835792627260492327)
            ·
              refine ⟨22712861753688940890738491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15141907835792627260492327 22712861753688940890738491)
              ·
                refine ⟨34069292630533411336107737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22712861753688940890738491 34069292630533411336107737)
                ·
                  refine ⟨25551969472900058502080803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34069292630533411336107737 25551969472900058502080803)
                  ·
                    refine ⟨38327954209350087753121205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25551969472900058502080803 38327954209350087753121205)
                    ·
                      refine ⟨3593245707126570726855113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38327954209350087753121205 3593245707126570726855113)
                      ·
                        rfl

theorem cell23_6997821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6997821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997821 prefixEnd_6997821 := by exact prefixLift 6997821
  have htrace : WordTrace (prefixWord ++ tailWord_6997821) baseStart_6997821 baseEnd_6997821 := by
    simpa [prefixWord, tailWord_6997821, baseEnd_6997821] using wordTrace_append hprefix tailTrace_6997821
  have hstable : (prefixWord ++ tailWord_6997821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997821).length < 2 ^ (prefixWord ++ tailWord_6997821).sum := by decide
  have hdescent : baseEnd_6997821 < baseStart_6997821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997841 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 7]
def baseStart_6997841 : Nat := 118140960795 + 6997841 * 2 ^ 59
def prefixEnd_6997841 : Nat := 4983230072969 + 3 ^ 40 * 6997841 * 2
def baseEnd_6997841 : Nat := 399250664082184516511669

theorem tailTrace_6997841 : CollatzResearch.WordTrace tailWord_6997841 prefixEnd_6997841 399250664082184516511669 := by
  unfold tailWord_6997841
  simp only [CollatzResearch.WordTrace]
  refine ⟨255232229441024667938265377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170154819627349778625510251 255232229441024667938265377)
  ·
    refine ⟨191424172080768500953699033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255232229441024667938265377 191424172080768500953699033)
    ·
      refine ⟨143568129060576375715274275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191424172080768500953699033 143568129060576375715274275)
      ·
        refine ⟨215352193590864563572911413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143568129060576375715274275 215352193590864563572911413)
        ·
          refine ⟨20189268149143552834960445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215352193590864563572911413 20189268149143552834960445)
          ·
            refine ⟨7570975555928832313110167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20189268149143552834960445 7570975555928832313110167)
            ·
              refine ⟨11356463333893248469665251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570975555928832313110167 11356463333893248469665251)
              ·
                refine ⟨17034695000839872704497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11356463333893248469665251 17034695000839872704497877)
                ·
                  refine ⟨399250664082184516511669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17034695000839872704497877 399250664082184516511669)
                  ·
                    rfl

theorem cell23_6997841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 7].length) (baseStart_6997841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997841 prefixEnd_6997841 := by exact prefixLift 6997841
  have htrace : WordTrace (prefixWord ++ tailWord_6997841) baseStart_6997841 baseEnd_6997841 := by
    simpa [prefixWord, tailWord_6997841, baseEnd_6997841] using wordTrace_append hprefix tailTrace_6997841
  have hstable : (prefixWord ++ tailWord_6997841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997841).length < 2 ^ (prefixWord ++ tailWord_6997841).sum := by decide
  have hdescent : baseEnd_6997841 < baseStart_6997841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997852 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6997852 : Nat := 118140960795 + 6997852 * 2 ^ 59
def prefixEnd_6997852 : Nat := 4983230072969 + 3 ^ 40 * 6997852 * 2
def baseEnd_6997852 : Nat := 3593261625026860105567471

theorem tailTrace_6997852 : CollatzResearch.WordTrace tailWord_6997852 prefixEnd_6997852 3593261625026860105567471 := by
  unfold tailWord_6997852
  simp only [CollatzResearch.WordTrace]
  refine ⟨127616315321992408408457905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170155087095989877877943873 127616315321992408408457905)
  ·
    refine ⟨95712236491494306306343429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127616315321992408408457905 95712236491494306306343429)
    ·
      refine ⟨17946044342155182432439393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95712236491494306306343429 17946044342155182432439393)
      ·
        refine ⟨13459533256616386824329545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17946044342155182432439393 13459533256616386824329545)
        ·
          refine ⟨10094649942462290118247159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13459533256616386824329545 10094649942462290118247159)
          ·
            refine ⟨15141974913693435177370739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094649942462290118247159 15141974913693435177370739)
            ·
              refine ⟨22712962370540152766056109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15141974913693435177370739 22712962370540152766056109)
              ·
                refine ⟨8517360888952557287271041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22712962370540152766056109 8517360888952557287271041)
                ·
                  refine ⟨6388020666714417965453281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8517360888952557287271041 6388020666714417965453281)
                  ·
                    refine ⟨4791015500035813474089961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388020666714417965453281 4791015500035813474089961)
                    ·
                      refine ⟨3593261625026860105567471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791015500035813474089961 3593261625026860105567471)
                      ·
                        rfl

theorem cell23_6997852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6997852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997852 prefixEnd_6997852 := by exact prefixLift 6997852
  have htrace : WordTrace (prefixWord ++ tailWord_6997852) baseStart_6997852 baseEnd_6997852 := by
    simpa [prefixWord, tailWord_6997852, baseEnd_6997852] using wordTrace_append hprefix tailTrace_6997852
  have hstable : (prefixWord ++ tailWord_6997852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997852).length < 2 ^ (prefixWord ++ tailWord_6997852).sum := by decide
  have hdescent : baseEnd_6997852 < baseStart_6997852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997864 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6997864 : Nat := 118140960795 + 6997864 * 2 ^ 59
def prefixEnd_6997864 : Nat := 4983230072969 + 3 ^ 40 * 6997864 * 2
def baseEnd_6997864 : Nat := 3593267786794714058617415

theorem tailTrace_6997864 : CollatzResearch.WordTrace tailWord_6997864 prefixEnd_6997864 3593267786794714058617415 := by
  unfold tailWord_6997864
  simp only [CollatzResearch.WordTrace]
  refine ⟨127616534159970671433176323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170155378879960895244235097 127616534159970671433176323)
  ·
    refine ⟨191424801239956007149764485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127616534159970671433176323 191424801239956007149764485)
    ·
      refine ⟨35892150232491751340580841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191424801239956007149764485 35892150232491751340580841)
      ·
        refine ⟨26919112674368813505435631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35892150232491751340580841 26919112674368813505435631)
        ·
          refine ⟨40378669011553220258153447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26919112674368813505435631 40378669011553220258153447)
          ·
            refine ⟨60568003517329830387230171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40378669011553220258153447 60568003517329830387230171)
            ·
              refine ⟨90852005275994745580845257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60568003517329830387230171 90852005275994745580845257)
              ·
                refine ⟨68139003956996059185633943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90852005275994745580845257 68139003956996059185633943)
                ·
                  refine ⟨102208505935494088778450915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68139003956996059185633943 102208505935494088778450915)
                  ·
                    refine ⟨153312758903241133167676373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102208505935494088778450915 153312758903241133167676373)
                    ·
                      refine ⟨3593267786794714058617415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153312758903241133167676373 3593267786794714058617415)
                      ·
                        rfl

theorem cell23_6997864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6997864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997864 prefixEnd_6997864 := by exact prefixLift 6997864
  have htrace : WordTrace (prefixWord ++ tailWord_6997864) baseStart_6997864 baseEnd_6997864 := by
    simpa [prefixWord, tailWord_6997864, baseEnd_6997864] using wordTrace_append hprefix tailTrace_6997864
  have hstable : (prefixWord ++ tailWord_6997864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997864).length < 2 ^ (prefixWord ++ tailWord_6997864).sum := by decide
  have hdescent : baseEnd_6997864 < baseStart_6997864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997891 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 4]
def baseStart_6997891 : Nat := 118140960795 + 6997891 * 2 ^ 59
def prefixEnd_6997891 : Nat := 4983230072969 + 3 ^ 40 * 6997891 * 2
def baseEnd_6997891 : Nat := 3593281650772385452979791

theorem tailTrace_6997891 : CollatzResearch.WordTrace tailWord_6997891 prefixEnd_6997891 3593281650772385452979791 := by
  unfold tailWord_6997891
  simp only [CollatzResearch.WordTrace]
  refine ⟨255234053090843526477585527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170156035393895684318390351 255234053090843526477585527)
  ·
    refine ⟨382851079636265289716378291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255234053090843526477585527 382851079636265289716378291)
    ·
      refine ⟨574276619454397934574567437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382851079636265289716378291 574276619454397934574567437)
      ·
        refine ⟨215353732295399225465462789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574276619454397934574567437 215353732295399225465462789)
        ·
          refine ⟨40378824805387354774774273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215353732295399225465462789 40378824805387354774774273)
          ·
            refine ⟨30284118604040516081080705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40378824805387354774774273 30284118604040516081080705)
            ·
              refine ⟨22713088953030387060810529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30284118604040516081080705 22713088953030387060810529)
              ·
                refine ⟨17034816714772790295607897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22713088953030387060810529 17034816714772790295607897)
                ·
                  refine ⟨12776112536079592721705923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17034816714772790295607897 12776112536079592721705923)
                  ·
                    refine ⟨19164168804119389082558885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12776112536079592721705923 19164168804119389082558885)
                    ·
                      refine ⟨3593281650772385452979791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19164168804119389082558885 3593281650772385452979791)
                      ·
                        rfl

theorem cell23_6997891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_6997891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997891 prefixEnd_6997891 := by exact prefixLift 6997891
  have htrace : WordTrace (prefixWord ++ tailWord_6997891) baseStart_6997891 baseEnd_6997891 := by
    simpa [prefixWord, tailWord_6997891, baseEnd_6997891] using wordTrace_append hprefix tailTrace_6997891
  have hstable : (prefixWord ++ tailWord_6997891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997891).length < 2 ^ (prefixWord ++ tailWord_6997891).sum := by decide
  have hdescent : baseEnd_6997891 < baseStart_6997891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997908 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6997908 : Nat := 118140960795 + 6997908 * 2 ^ 59
def prefixEnd_6997908 : Nat := 4983230072969 + 3 ^ 40 * 6997908 * 2
def baseEnd_6997908 : Nat := 3593290379943511886467213

theorem tailTrace_6997908 : CollatzResearch.WordTrace tailWord_6997908 prefixEnd_6997908 3593290379943511886467213 := by
  unfold tailWord_6997908
  simp only [CollatzResearch.WordTrace]
  refine ⟨127617336565890969190477189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170156448754521292253969585 127617336565890969190477189)
  ·
    refine ⟨23928250606104556723214473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127617336565890969190477189 23928250606104556723214473)
    ·
      refine ⟨17946187954578417542410855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23928250606104556723214473 17946187954578417542410855)
      ·
        refine ⟨26919281931867626313616283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946187954578417542410855 26919281931867626313616283)
        ·
          refine ⟨40378922897801439470424425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26919281931867626313616283 40378922897801439470424425)
          ·
            refine ⟨30284192173351079602818319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40378922897801439470424425 30284192173351079602818319)
            ·
              refine ⟨45426288260026619404227479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30284192173351079602818319 45426288260026619404227479)
              ·
                refine ⟨68139432390039929106341219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45426288260026619404227479 68139432390039929106341219)
                ·
                  refine ⟨102209148585059893659511829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68139432390039929106341219 102209148585059893659511829)
                  ·
                    refine ⟨4791053839924682515289617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102209148585059893659511829 4791053839924682515289617)
                    ·
                      refine ⟨3593290379943511886467213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791053839924682515289617 3593290379943511886467213)
                      ·
                        rfl

theorem cell23_6997908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6997908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997908 prefixEnd_6997908 := by exact prefixLift 6997908
  have htrace : WordTrace (prefixWord ++ tailWord_6997908) baseStart_6997908 baseEnd_6997908 := by
    simpa [prefixWord, tailWord_6997908, baseEnd_6997908] using wordTrace_append hprefix tailTrace_6997908
  have hstable : (prefixWord ++ tailWord_6997908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997908).length < 2 ^ (prefixWord ++ tailWord_6997908).sum := by decide
  have hdescent : baseEnd_6997908 < baseStart_6997908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997948 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 8]
def baseStart_6997948 : Nat := 118140960795 + 6997948 * 2 ^ 59
def prefixEnd_6997948 : Nat := 4983230072969 + 3 ^ 40 * 6997948 * 2
def baseEnd_6997948 : Nat := 399256768796632414440781

theorem tailTrace_6997948 : CollatzResearch.WordTrace tailWord_6997948 prefixEnd_6997948 399256768796632414440781 := by
  unfold tailWord_6997948
  simp only [CollatzResearch.WordTrace]
  refine ⟨127618066025818512606205249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170157421367758016808273665 127618066025818512606205249)
  ·
    refine ⟨95713549519363884454653937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127618066025818512606205249 95713549519363884454653937)
    ·
      refine ⟨71785162139522913340990453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95713549519363884454653937 71785162139522913340990453)
      ·
        refine ⟨6729858950580273125717855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71785162139522913340990453 6729858950580273125717855)
        ·
          refine ⟨10094788425870409688576783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729858950580273125717855 10094788425870409688576783)
          ·
            refine ⟨15142182638805614532865175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094788425870409688576783 15142182638805614532865175)
            ·
              refine ⟨22713273958208421799297763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15142182638805614532865175 22713273958208421799297763)
              ·
                refine ⟨34069910937312632698946645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22713273958208421799297763 34069910937312632698946645)
                ·
                  refine ⟨399256768796632414440781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34069910937312632698946645 399256768796632414440781)
                  ·
                    rfl

theorem cell23_6997948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_6997948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997948 prefixEnd_6997948 := by exact prefixLift 6997948
  have htrace : WordTrace (prefixWord ++ tailWord_6997948) baseStart_6997948 baseEnd_6997948 := by
    simpa [prefixWord, tailWord_6997948, baseEnd_6997948] using wordTrace_append hprefix tailTrace_6997948
  have hstable : (prefixWord ++ tailWord_6997948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997948).length < 2 ^ (prefixWord ++ tailWord_6997948).sum := by decide
  have hdescent : baseEnd_6997948 < baseStart_6997948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997986 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6997986 : Nat := 118140960795 + 6997986 * 2 ^ 59
def prefixEnd_6997986 : Nat := 4983230072969 + 3 ^ 40 * 6997986 * 2
def baseEnd_6997986 : Nat := 1197776810478187527097285

theorem tailTrace_6997986 : CollatzResearch.WordTrace tailWord_6997986 prefixEnd_6997986 1197776810478187527097285 := by
  unfold tailWord_6997986
  simp only [CollatzResearch.WordTrace]
  refine ⟨63809379506374839425573453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170158345350332905134862541 63809379506374839425573453)
  ·
    refine ⟨23928517314890564784590045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63809379506374839425573453 23928517314890564784590045)
    ·
      refine ⟨8973193993083961794221267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23928517314890564784590045 8973193993083961794221267)
      ·
        refine ⟨13459790989625942691331901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8973193993083961794221267 13459790989625942691331901)
        ·
          refine ⟨5047421621109728509249463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13459790989625942691331901 5047421621109728509249463)
          ·
            refine ⟨7571132431664592763874195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047421621109728509249463 7571132431664592763874195)
            ·
              refine ⟨11356698647496889145811293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571132431664592763874195 11356698647496889145811293)
              ·
                refine ⟨4258761992811333429679235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11356698647496889145811293 4258761992811333429679235)
                ·
                  refine ⟨6388142989217000144518853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258761992811333429679235 6388142989217000144518853)
                  ·
                    refine ⟨1197776810478187527097285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6388142989217000144518853 1197776810478187527097285)
                    ·
                      rfl

theorem cell23_6997986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6997986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997986 prefixEnd_6997986 := by exact prefixLift 6997986
  have htrace : WordTrace (prefixWord ++ tailWord_6997986) baseStart_6997986 baseEnd_6997986 := by
    simpa [prefixWord, tailWord_6997986, baseEnd_6997986] using wordTrace_append hprefix tailTrace_6997986
  have hstable : (prefixWord ++ tailWord_6997986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997986).length < 2 ^ (prefixWord ++ tailWord_6997986).sum := by decide
  have hdescent : baseEnd_6997986 < baseStart_6997986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998021 : List Nat := [1, 3, 1, 1, 2, 5, 2, 8]
def baseStart_6998021 : Nat := 118140960795 + 6998021 * 2 ^ 59
def prefixEnd_6998021 : Nat := 4983230072969 + 3 ^ 40 * 6998021 * 2
def baseEnd_6998021 : Nat := 133086977898424812753859

theorem tailTrace_6998021 : CollatzResearch.WordTrace tailWord_6998021 prefixEnd_6998021 133086977898424812753859 := by
  unfold tailWord_6998021
  simp only [CollatzResearch.WordTrace]
  refine ⟨255238794580372558679817917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170159196386915039119878611 255238794580372558679817917)
  ·
    refine ⟨95714547967639709504931719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255238794580372558679817917 95714547967639709504931719)
    ·
      refine ⟨143571821951459564257397579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95714547967639709504931719 143571821951459564257397579)
      ·
        refine ⟨215357732927189346386096369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143571821951459564257397579 215357732927189346386096369)
        ·
          refine ⟨161518299695392009789572277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215357732927189346386096369 161518299695392009789572277)
          ·
            refine ⟨15142340596443000917772401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161518299695392009789572277 15142340596443000917772401)
            ·
              refine ⟨11356755447332250688329301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15142340596443000917772401 11356755447332250688329301)
              ·
                refine ⟨133086977898424812753859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11356755447332250688329301 133086977898424812753859)
                ·
                  rfl

theorem cell23_6998021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 8].length) (baseStart_6998021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998021 prefixEnd_6998021 := by exact prefixLift 6998021
  have htrace : WordTrace (prefixWord ++ tailWord_6998021) baseStart_6998021 baseEnd_6998021 := by
    simpa [prefixWord, tailWord_6998021, baseEnd_6998021] using wordTrace_append hprefix tailTrace_6998021
  have hstable : (prefixWord ++ tailWord_6998021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998021).length < 2 ^ (prefixWord ++ tailWord_6998021).sum := by decide
  have hdescent : baseEnd_6998021 < baseStart_6998021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998052 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6998052 : Nat := 118140960795 + 6998052 * 2 ^ 59
def prefixEnd_6998052 : Nat := 4983230072969 + 3 ^ 40 * 6998052 * 2
def baseEnd_6998052 : Nat := 3593364321157759323066551

theorem tailTrace_6998052 : CollatzResearch.WordTrace tailWord_6998052 prefixEnd_6998052 3593364321157759323066551 := by
  unfold tailWord_6998052
  simp only [CollatzResearch.WordTrace]
  refine ⟨127619962621630125487098205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170159950162173500649464273 127619962621630125487098205)
  ·
    refine ⟨47857485983111297057661827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127619962621630125487098205 47857485983111297057661827)
    ·
      refine ⟨71786228974666945586492741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47857485983111297057661827 71786228974666945586492741)
      ·
        refine ⟨13459917932750052297467389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71786228974666945586492741 13459917932750052297467389)
        ·
          refine ⟨5047469224781269611550271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13459917932750052297467389 5047469224781269611550271)
          ·
            refine ⟨7571203837171904417325407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047469224781269611550271 7571203837171904417325407)
            ·
              refine ⟨11356805755757856625988111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571203837171904417325407 11356805755757856625988111)
              ·
                refine ⟨17035208633636784938982167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11356805755757856625988111 17035208633636784938982167)
                ·
                  refine ⟨25552812950455177408473251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17035208633636784938982167 25552812950455177408473251)
                  ·
                    refine ⟨38329219425682766112709877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25552812950455177408473251 38329219425682766112709877)
                    ·
                      refine ⟨3593364321157759323066551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38329219425682766112709877 3593364321157759323066551)
                      ·
                        rfl

theorem cell23_6998052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6998052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998052 prefixEnd_6998052 := by exact prefixLift 6998052
  have htrace : WordTrace (prefixWord ++ tailWord_6998052) baseStart_6998052 baseEnd_6998052 := by
    simpa [prefixWord, tailWord_6998052, baseEnd_6998052] using wordTrace_append hprefix tailTrace_6998052
  have hstable : (prefixWord ++ tailWord_6998052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998052).length < 2 ^ (prefixWord ++ tailWord_6998052).sum := by decide
  have hdescent : baseEnd_6998052 < baseStart_6998052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998065 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_6998065 : Nat := 118140960795 + 6998065 * 2 ^ 59
def prefixEnd_6998065 : Nat := 4983230072969 + 3 ^ 40 * 6998065 * 2
def baseEnd_6998065 : Nat := 3593370996406267772203991

theorem tailTrace_6998065 : CollatzResearch.WordTrace tailWord_6998065 prefixEnd_6998065 3593370996406267772203991 := by
  unfold tailWord_6998065
  simp only [CollatzResearch.WordTrace]
  refine ⟨255240399392213154194419649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170160266261475436129613099 255240399392213154194419649)
  ·
    refine ⟨191430299544159865645814737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255240399392213154194419649 191430299544159865645814737)
    ·
      refine ⟨143572724658119899234361053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191430299544159865645814737 143572724658119899234361053)
      ·
        refine ⟨53839771746794962212885395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143572724658119899234361053 53839771746794962212885395)
        ·
          refine ⟨80759657620192443319328093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53839771746794962212885395 80759657620192443319328093)
          ·
            refine ⟨30284871607572166244748035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80759657620192443319328093 30284871607572166244748035)
            ·
              refine ⟨45427307411358249367122053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30284871607572166244748035 45427307411358249367122053)
              ·
                refine ⟨8517620139629671756335385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45427307411358249367122053 8517620139629671756335385)
                ·
                  refine ⟨6388215104722253817251539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8517620139629671756335385 6388215104722253817251539)
                  ·
                    refine ⟨9582322657083380725877309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6388215104722253817251539 9582322657083380725877309)
                    ·
                      refine ⟨3593370996406267772203991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9582322657083380725877309 3593370996406267772203991)
                      ·
                        rfl

theorem cell23_6998065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_6998065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998065 prefixEnd_6998065 := by exact prefixLift 6998065
  have htrace : WordTrace (prefixWord ++ tailWord_6998065) baseStart_6998065 baseEnd_6998065 := by
    simpa [prefixWord, tailWord_6998065, baseEnd_6998065] using wordTrace_append hprefix tailTrace_6998065
  have hstable : (prefixWord ++ tailWord_6998065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998065).length < 2 ^ (prefixWord ++ tailWord_6998065).sum := by decide
  have hdescent : baseEnd_6998065 < baseStart_6998065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998066 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_6998066 : Nat := 118140960795 + 6998066 * 2 ^ 59
def prefixEnd_6998066 : Nat := 4983230072969 + 3 ^ 40 * 6998066 * 2
def baseEnd_6998066 : Nat := 3593371509886922268291487

theorem tailTrace_6998066 : CollatzResearch.WordTrace tailWord_6998066 prefixEnd_6998066 3593371509886922268291487 := by
  unfold tailWord_6998066
  simp only [CollatzResearch.WordTrace]
  refine ⟨63810108966302382841301513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170160290576806354243470701 63810108966302382841301513)
  ·
    refine ⟨47857581724726787130976135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63810108966302382841301513 47857581724726787130976135)
    ·
      refine ⟨71786372587090180696464203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47857581724726787130976135 71786372587090180696464203)
      ·
        refine ⟨107679558880635271044696305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71786372587090180696464203 107679558880635271044696305)
        ·
          refine ⟨80759669160476453283522229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107679558880635271044696305 80759669160476453283522229)
          ·
            refine ⟨7571218983794667495330209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80759669160476453283522229 7571218983794667495330209)
            ·
              refine ⟨5678414237846000621497657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7571218983794667495330209 5678414237846000621497657)
              ·
                refine ⟨4258810678384500466123243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678414237846000621497657 4258810678384500466123243)
                ·
                  refine ⟨6388216017576750699184865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258810678384500466123243 6388216017576750699184865)
                  ·
                    refine ⟨4791162013182563024388649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388216017576750699184865 4791162013182563024388649)
                    ·
                      refine ⟨3593371509886922268291487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791162013182563024388649 3593371509886922268291487)
                      ·
                        rfl

theorem cell23_6998066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_6998066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998066 prefixEnd_6998066 := by exact prefixLift 6998066
  have htrace : WordTrace (prefixWord ++ tailWord_6998066) baseStart_6998066 baseEnd_6998066 := by
    simpa [prefixWord, tailWord_6998066, baseEnd_6998066] using wordTrace_append hprefix tailTrace_6998066
  have hstable : (prefixWord ++ tailWord_6998066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998066).length < 2 ^ (prefixWord ++ tailWord_6998066).sum := by decide
  have hdescent : baseEnd_6998066 < baseStart_6998066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998071 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_6998071 : Nat := 118140960795 + 6998071 * 2 ^ 59
def prefixEnd_6998071 : Nat := 4983230072969 + 3 ^ 40 * 6998071 * 2
def baseEnd_6998071 : Nat := 3593374077290194748728963

theorem tailTrace_6998071 : CollatzResearch.WordTrace tailWord_6998071 prefixEnd_6998071 3593374077290194748728963 := by
  unfold tailWord_6998071
  simp only [CollatzResearch.WordTrace]
  refine ⟨255240618230191417219138067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170160412153460944812758711 255240618230191417219138067)
  ·
    refine ⟨382860927345287125828707101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255240618230191417219138067 382860927345287125828707101)
    ·
      refine ⟨143572847754482672185765163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382860927345287125828707101 143572847754482672185765163)
      ·
        refine ⟨215359271631724008278647745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143572847754482672185765163 215359271631724008278647745)
        ·
          refine ⟨161519453723793006208985809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215359271631724008278647745 161519453723793006208985809)
          ·
            refine ⟨121139590292844754656739357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161519453723793006208985809 121139590292844754656739357)
            ·
              refine ⟨45427346359816782996277259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121139590292844754656739357 45427346359816782996277259)
              ·
                refine ⟨68141019539725174494415889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45427346359816782996277259 68141019539725174494415889)
                ·
                  refine ⟨51105764654793880870811917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68141019539725174494415889 51105764654793880870811917)
                  ·
                    refine ⟨19164661745547705326554469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51105764654793880870811917 19164661745547705326554469)
                    ·
                      refine ⟨3593374077290194748728963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19164661745547705326554469 3593374077290194748728963)
                      ·
                        rfl

theorem cell23_6998071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_6998071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998071 prefixEnd_6998071 := by exact prefixLift 6998071
  have htrace : WordTrace (prefixWord ++ tailWord_6998071) baseStart_6998071 baseEnd_6998071 := by
    simpa [prefixWord, tailWord_6998071, baseEnd_6998071] using wordTrace_append hprefix tailTrace_6998071
  have hstable : (prefixWord ++ tailWord_6998071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998071).length < 2 ^ (prefixWord ++ tailWord_6998071).sum := by decide
  have hdescent : baseEnd_6998071 < baseStart_6998071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998105 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 4, 2, 2]
def baseStart_6998105 : Nat := 118140960795 + 6998105 * 2 ^ 59
def prefixEnd_6998105 : Nat := 4983230072969 + 3 ^ 40 * 6998105 * 2
def baseEnd_6998105 : Nat := 3593391535632447615703807

theorem tailTrace_6998105 : CollatzResearch.WordTrace tailWord_6998105 prefixEnd_6998105 3593391535632447615703807 := by
  unfold tailWord_6998105
  simp only [CollatzResearch.WordTrace]
  refine ⟨255241858312068241025875769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170161238874712160683917179 255241858312068241025875769)
  ·
    refine ⟨191431393734051180769406827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255241858312068241025875769 191431393734051180769406827)
    ·
      refine ⟨287147090601076771154110241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191431393734051180769406827 287147090601076771154110241)
      ·
        refine ⟨215360317950807578365582681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287147090601076771154110241 215360317950807578365582681)
        ·
          refine ⟨161520238463105683774187011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215360317950807578365582681 161520238463105683774187011)
          ·
            refine ⟨242280357694658525661280517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161520238463105683774187011 242280357694658525661280517)
            ·
              refine ⟨45427567067748473561490097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242280357694658525661280517 45427567067748473561490097)
              ·
                refine ⟨34070675300811355171117573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45427567067748473561490097 34070675300811355171117573)
                ·
                  refine ⟨6388251618902129094584545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34070675300811355171117573 6388251618902129094584545)
                  ·
                    refine ⟨4791188714176596820938409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388251618902129094584545 4791188714176596820938409)
                    ·
                      refine ⟨3593391535632447615703807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791188714176596820938409 3593391535632447615703807)
                      ·
                        rfl

theorem cell23_6998105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_6998105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998105 prefixEnd_6998105 := by exact prefixLift 6998105
  have htrace : WordTrace (prefixWord ++ tailWord_6998105) baseStart_6998105 baseEnd_6998105 := by
    simpa [prefixWord, tailWord_6998105, baseEnd_6998105] using wordTrace_append hprefix tailTrace_6998105
  have hstable : (prefixWord ++ tailWord_6998105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998105).length < 2 ^ (prefixWord ++ tailWord_6998105).sum := by decide
  have hdescent : baseEnd_6998105 < baseStart_6998105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998109 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6998109 : Nat := 118140960795 + 6998109 * 2 ^ 59
def prefixEnd_6998109 : Nat := 4983230072969 + 3 ^ 40 * 6998109 * 2
def baseEnd_6998109 : Nat := 3593393589555065600053789

theorem tailTrace_6998109 : CollatzResearch.WordTrace tailWord_6998109 prefixEnd_6998109 3593393589555065600053789 := by
  unfold tailWord_6998109
  simp only [CollatzResearch.WordTrace]
  refine ⟨255242004204053749709021381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170161336136035833139347587 255242004204053749709021381)
  ·
    refine ⟨47857875788260078070441509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255242004204053749709021381 47857875788260078070441509)
    ·
      refine ⟨8973351710298764638207783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47857875788260078070441509 8973351710298764638207783)
      ·
        refine ⟨13460027565448146957311675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8973351710298764638207783 13460027565448146957311675)
        ·
          refine ⟨20190041348172220435967513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13460027565448146957311675 20190041348172220435967513)
          ·
            refine ⟨15142531011129165326975635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20190041348172220435967513 15142531011129165326975635)
            ·
              refine ⟨22713796516693747990463453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15142531011129165326975635 22713796516693747990463453)
              ·
                refine ⟨8517673693760155496423795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22713796516693747990463453 8517673693760155496423795)
                ·
                  refine ⟨12776510540640233244635693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517673693760155496423795 12776510540640233244635693)
                  ·
                    refine ⟨4791191452740087466738385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12776510540640233244635693 4791191452740087466738385)
                    ·
                      refine ⟨3593393589555065600053789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791191452740087466738385 3593393589555065600053789)
                      ·
                        rfl

theorem cell23_6998109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6998109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998109 prefixEnd_6998109 := by exact prefixLift 6998109
  have htrace : WordTrace (prefixWord ++ tailWord_6998109) baseStart_6998109 baseEnd_6998109 := by
    simpa [prefixWord, tailWord_6998109, baseEnd_6998109] using wordTrace_append hprefix tailTrace_6998109
  have hstable : (prefixWord ++ tailWord_6998109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998109).length < 2 ^ (prefixWord ++ tailWord_6998109).sum := by decide
  have hdescent : baseEnd_6998109 < baseStart_6998109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998128 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 7]
def baseStart_6998128 : Nat := 118140960795 + 6998128 * 2 ^ 59
def prefixEnd_6998128 : Nat := 4983230072969 + 3 ^ 40 * 6998128 * 2
def baseEnd_6998128 : Nat := 399267038409722336190689

theorem tailTrace_6998128 : CollatzResearch.WordTrace tailWord_6998128 prefixEnd_6998128 399267038409722336190689 := by
  unfold tailWord_6998128
  simp only [CollatzResearch.WordTrace]
  refine ⟨127621348595492457976981519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170161798127323277302642025 127621348595492457976981519)
  ·
    refine ⟨191432022893238686965472279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127621348595492457976981519 191432022893238686965472279)
    ·
      refine ⟨287148034339858030448208419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191432022893238686965472279 287148034339858030448208419)
      ·
        refine ⟨430722051509787045672312629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287148034339858030448208419 430722051509787045672312629)
        ·
          refine ⟨40380192329042535531779309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 430722051509787045672312629 40380192329042535531779309)
          ·
            refine ⟨15142572123390950824417241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40380192329042535531779309 15142572123390950824417241)
            ·
              refine ⟨11356929092543213118312931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15142572123390950824417241 11356929092543213118312931)
              ·
                refine ⟨17035393638814819677469397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11356929092543213118312931 17035393638814819677469397)
                ·
                  refine ⟨399267038409722336190689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17035393638814819677469397 399267038409722336190689)
                  ·
                    rfl

theorem cell23_6998128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_6998128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998128 prefixEnd_6998128 := by exact prefixLift 6998128
  have htrace : WordTrace (prefixWord ++ tailWord_6998128) baseStart_6998128 baseEnd_6998128 := by
    simpa [prefixWord, tailWord_6998128, baseEnd_6998128] using wordTrace_append hprefix tailTrace_6998128
  have hstable : (prefixWord ++ tailWord_6998128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998128).length < 2 ^ (prefixWord ++ tailWord_6998128).sum := by decide
  have hdescent : baseEnd_6998128 < baseStart_6998128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998175 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 2, 5]
def baseStart_6998175 : Nat := 118140960795 + 6998175 * 2 ^ 59
def prefixEnd_6998175 : Nat := 4983230072969 + 3 ^ 40 * 6998175 * 2
def baseEnd_6998175 : Nat := 1197809159759420780609495

theorem tailTrace_6998175 : CollatzResearch.WordTrace tailWord_6998175 prefixEnd_6998175 1197809159759420780609495 := by
  unfold tailWord_6998175
  simp only [CollatzResearch.WordTrace]
  refine ⟨255244411421814642980923979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170162940947876428653949319 255244411421814642980923979)
  ·
    refine ⟨382866617132721964471385969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255244411421814642980923979 382866617132721964471385969)
    ·
      refine ⟨287149962849541473353539477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382866617132721964471385969 287149962849541473353539477)
      ·
        refine ⟨13460154508572256563447163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 287149962849541473353539477 13460154508572256563447163)
        ·
          refine ⟨20190231762858384845170745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13460154508572256563447163 20190231762858384845170745)
          ·
            refine ⟨15142673822143788633878059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20190231762858384845170745 15142673822143788633878059)
            ·
              refine ⟨22714010733215682950817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15142673822143788633878059 22714010733215682950817089)
              ·
                refine ⟨17035508049911762213112817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22714010733215682950817089 17035508049911762213112817)
                ·
                  refine ⟨12776631037433821659834613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17035508049911762213112817 12776631037433821659834613)
                  ·
                    refine ⟨1197809159759420780609495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12776631037433821659834613 1197809159759420780609495)
                    ·
                      rfl

theorem cell23_6998175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_6998175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998175 prefixEnd_6998175 := by exact prefixLift 6998175
  have htrace : WordTrace (prefixWord ++ tailWord_6998175) baseStart_6998175 baseEnd_6998175 := by
    simpa [prefixWord, tailWord_6998175, baseEnd_6998175] using wordTrace_append hprefix tailTrace_6998175
  have hstable : (prefixWord ++ tailWord_6998175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998175).length < 2 ^ (prefixWord ++ tailWord_6998175).sum := by decide
  have hdescent : baseEnd_6998175 < baseStart_6998175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998190 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6998190 : Nat := 118140960795 + 6998190 * 2 ^ 59
def prefixEnd_6998190 : Nat := 4983230072969 + 3 ^ 40 * 6998190 * 2
def baseEnd_6998190 : Nat := 3593435181488079783140917

theorem tailTrace_6998190 : CollatzResearch.WordTrace tailWord_6998190 prefixEnd_6998190 3593435181488079783140917 := by
  unfold tailWord_6998190
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905619814595037567840003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170163305677840200361813349 31905619814595037567840003)
  ·
    refine ⟨47858429721892556351760005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31905619814595037567840003 47858429721892556351760005)
    ·
      refine ⟨8973455572854854315955001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47858429721892556351760005 8973455572854854315955001)
      ·
        refine ⟨6730091679641140736966251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8973455572854854315955001 6730091679641140736966251)
        ·
          refine ⟨10095137519461711105449377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6730091679641140736966251 10095137519461711105449377)
          ·
            refine ⟨7571353139596283329087033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10095137519461711105449377 7571353139596283329087033)
            ·
              refine ⟨5678514854697212496815275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7571353139596283329087033 5678514854697212496815275)
              ·
                refine ⟨8517772282045818745222913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678514854697212496815275 8517772282045818745222913)
                ·
                  refine ⟨6388329211534364058917185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8517772282045818745222913 6388329211534364058917185)
                  ·
                    refine ⟨4791246908650773044187889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388329211534364058917185 4791246908650773044187889)
                    ·
                      refine ⟨3593435181488079783140917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791246908650773044187889 3593435181488079783140917)
                      ·
                        rfl

theorem cell23_6998190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6998190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998190 prefixEnd_6998190 := by exact prefixLift 6998190
  have htrace : WordTrace (prefixWord ++ tailWord_6998190) baseStart_6998190 baseEnd_6998190 := by
    simpa [prefixWord, tailWord_6998190, baseEnd_6998190] using wordTrace_append hprefix tailTrace_6998190
  have hstable : (prefixWord ++ tailWord_6998190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998190).length < 2 ^ (prefixWord ++ tailWord_6998190).sum := by decide
  have hdescent : baseEnd_6998190 < baseStart_6998190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998212 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_6998212 : Nat := 118140960795 + 6998212 * 2 ^ 59
def prefixEnd_6998212 : Nat := 4983230072969 + 3 ^ 40 * 6998212 * 2
def baseEnd_6998212 : Nat := 3593446478062478697065815

theorem tailTrace_6998212 : CollatzResearch.WordTrace tailWord_6998212 prefixEnd_6998212 3593446478062478697065815 := by
  unfold tailWord_6998212
  simp only [CollatzResearch.WordTrace]
  refine ⟨127622880461340299150010445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170163840615120398866680593 127622880461340299150010445)
  ·
    refine ⟨47858580173002612181253917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127622880461340299150010445 47858580173002612181253917)
    ·
      refine ⟨17946967564875979567970219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47858580173002612181253917 17946967564875979567970219)
      ·
        refine ⟨26920451347313969351955329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946967564875979567970219 26920451347313969351955329)
        ·
          refine ⟨20190338510485477013966497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26920451347313969351955329 20190338510485477013966497)
          ·
            refine ⟨15142753882864107760474873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20190338510485477013966497 15142753882864107760474873)
            ·
              refine ⟨11357065412148080820356155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15142753882864107760474873 11357065412148080820356155)
              ·
                refine ⟨17035598118222121230534233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357065412148080820356155 17035598118222121230534233)
                ·
                  refine ⟨12776698588666590922900675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17035598118222121230534233 12776698588666590922900675)
                  ·
                    refine ⟨19165047882999886384351013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12776698588666590922900675 19165047882999886384351013)
                    ·
                      refine ⟨3593446478062478697065815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19165047882999886384351013 3593446478062478697065815)
                      ·
                        rfl

theorem cell23_6998212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_6998212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998212 prefixEnd_6998212 := by exact prefixLift 6998212
  have htrace : WordTrace (prefixWord ++ tailWord_6998212) baseStart_6998212 baseEnd_6998212 := by
    simpa [prefixWord, tailWord_6998212, baseEnd_6998212] using wordTrace_append hprefix tailTrace_6998212
  have hstable : (prefixWord ++ tailWord_6998212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998212).length < 2 ^ (prefixWord ++ tailWord_6998212).sum := by decide
  have hdescent : baseEnd_6998212 < baseStart_6998212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998262 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_6998262 : Nat := 118140960795 + 6998262 * 2 ^ 59
def prefixEnd_6998262 : Nat := 4983230072969 + 3 ^ 40 * 6998262 * 2
def baseEnd_6998262 : Nat := 3593472152095203501440585

theorem tailTrace_6998262 : CollatzResearch.WordTrace tailWord_6998262 prefixEnd_6998262 3593472152095203501440585 := by
  unfold tailWord_6998262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952974035781216052458815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170165056381666304559560693 15952974035781216052458815)
  ·
    refine ⟨23929461053671824078688223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15952974035781216052458815 23929461053671824078688223)
    ·
      refine ⟨35894191580507736118032335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23929461053671824078688223 35894191580507736118032335)
      ·
        refine ⟨53841287370761604177048503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35894191580507736118032335 53841287370761604177048503)
        ·
          refine ⟨80761931056142406265572755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53841287370761604177048503 80761931056142406265572755)
          ·
            refine ⟨121142896584213609398359133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80761931056142406265572755 121142896584213609398359133)
            ·
              refine ⟨45428586219080103524384675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121142896584213609398359133 45428586219080103524384675)
              ·
                refine ⟨68142879328620155286577013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45428586219080103524384675 68142879328620155286577013)
                ·
                  refine ⟨6388394937058139558116595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68142879328620155286577013 6388394937058139558116595)
                  ·
                    refine ⟨9582592405587209337174893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6388394937058139558116595 9582592405587209337174893)
                    ·
                      refine ⟨3593472152095203501440585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9582592405587209337174893 3593472152095203501440585)
                      ·
                        rfl

theorem cell23_6998262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_6998262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998262 prefixEnd_6998262 := by exact prefixLift 6998262
  have htrace : WordTrace (prefixWord ++ tailWord_6998262) baseStart_6998262 baseEnd_6998262 := by
    simpa [prefixWord, tailWord_6998262, baseEnd_6998262] using wordTrace_append hprefix tailTrace_6998262
  have hstable : (prefixWord ++ tailWord_6998262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998262).length < 2 ^ (prefixWord ++ tailWord_6998262).sum := by decide
  have hdescent : baseEnd_6998262 < baseStart_6998262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998272 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 2, 3, 2]
def baseStart_6998272 : Nat := 118140960795 + 6998272 * 2 ^ 59
def prefixEnd_6998272 : Nat := 4983230072969 + 3 ^ 40 * 6998272 * 2
def baseEnd_6998272 : Nat := 3593477286901748462315539

theorem tailTrace_6998272 : CollatzResearch.WordTrace tailWord_6998272 prefixEnd_6998272 3593477286901748462315539 := by
  unfold tailWord_6998272
  simp only [CollatzResearch.WordTrace]
  refine ⟨127623974651231614273602535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170165299534975485698136713 127623974651231614273602535)
  ·
    refine ⟨191435961976847421410403803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127623974651231614273602535 191435961976847421410403803)
    ·
      refine ⟨287153942965271132115605705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191435961976847421410403803 287153942965271132115605705)
      ·
        refine ⟨215365457223953349086704279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287153942965271132115605705 215365457223953349086704279)
        ·
          refine ⟨323048185835930023630056419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215365457223953349086704279 323048185835930023630056419)
          ·
            refine ⟨484572278753895035445084629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323048185835930023630056419 484572278753895035445084629)
            ·
              refine ⟨11357162783294414893244171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 484572278753895035445084629 11357162783294414893244171)
              ·
                refine ⟨17035744174941622339866257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357162783294414893244171 17035744174941622339866257)
                ·
                  refine ⟨12776808131206216754899693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17035744174941622339866257 12776808131206216754899693)
                  ·
                    refine ⟨4791303049202331283087385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12776808131206216754899693 4791303049202331283087385)
                    ·
                      refine ⟨3593477286901748462315539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791303049202331283087385 3593477286901748462315539)
                      ·
                        rfl

theorem cell23_6998272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_6998272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998272 prefixEnd_6998272 := by exact prefixLift 6998272
  have htrace : WordTrace (prefixWord ++ tailWord_6998272) baseStart_6998272 baseEnd_6998272 := by
    simpa [prefixWord, tailWord_6998272, baseEnd_6998272] using wordTrace_append hprefix tailTrace_6998272
  have hstable : (prefixWord ++ tailWord_6998272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998272).length < 2 ^ (prefixWord ++ tailWord_6998272).sum := by decide
  have hdescent : baseEnd_6998272 < baseStart_6998272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998282 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_6998282 : Nat := 118140960795 + 6998282 * 2 ^ 59
def prefixEnd_6998282 : Nat := 4983230072969 + 3 ^ 40 * 6998282 * 2
def baseEnd_6998282 : Nat := 1197827473902764474396831

theorem tailTrace_6998282 : CollatzResearch.WordTrace tailWord_6998282 prefixEnd_6998282 1197827473902764474396831 := by
  unfold tailWord_6998282
  simp only [CollatzResearch.WordTrace]
  refine ⟨63812078508106750063767275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170165542688284666836712733 63812078508106750063767275)
  ·
    refine ⟨95718117762160125095650913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63812078508106750063767275 95718117762160125095650913)
    ·
      refine ⟨71788588321620093821738185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95718117762160125095650913 71788588321620093821738185)
      ·
        refine ⟨53841441241215070366303639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71788588321620093821738185 53841441241215070366303639)
        ·
          refine ⟨80762161861822605549455459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53841441241215070366303639 80762161861822605549455459)
          ·
            refine ⟨121143242792733908324183189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80762161861822605549455459 121143242792733908324183189)
            ·
              refine ⟨5678589505909401952696087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121143242792733908324183189 5678589505909401952696087)
              ·
                refine ⟨8517884258864102929044131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678589505909401952696087 8517884258864102929044131)
                ·
                  refine ⟨12776826388296154393566197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517884258864102929044131 12776826388296154393566197)
                  ·
                    refine ⟨1197827473902764474396831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12776826388296154393566197 1197827473902764474396831)
                    ·
                      rfl

theorem cell23_6998282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_6998282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998282 prefixEnd_6998282 := by exact prefixLift 6998282
  have htrace : WordTrace (prefixWord ++ tailWord_6998282) baseStart_6998282 baseEnd_6998282 := by
    simpa [prefixWord, tailWord_6998282, baseEnd_6998282] using wordTrace_append hprefix tailTrace_6998282
  have hstable : (prefixWord ++ tailWord_6998282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998282).length < 2 ^ (prefixWord ++ tailWord_6998282).sum := by decide
  have hdescent : baseEnd_6998282 < baseStart_6998282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998305 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6998305 : Nat := 118140960795 + 6998305 * 2 ^ 59
def prefixEnd_6998305 : Nat := 4983230072969 + 3 ^ 40 * 6998305 * 2
def baseEnd_6998305 : Nat := 3593494231763346833202887

theorem tailTrace_6998305 : CollatzResearch.WordTrace tailWord_6998305 prefixEnd_6998305 3593494231763346833202887 := by
  unfold tailWord_6998305
  simp only [CollatzResearch.WordTrace]
  refine ⟨255249152911343675183156369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170166101940895783455437579 255249152911343675183156369)
  ·
    refine ⟨191436864683507756387367277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255249152911343675183156369 191436864683507756387367277)
    ·
      refine ⟨71788824256315408645262729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191436864683507756387367277 71788824256315408645262729)
      ·
        refine ⟨53841618192236556483947047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71788824256315408645262729 53841618192236556483947047)
        ·
          refine ⟨80762427288354834725920571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53841618192236556483947047 80762427288354834725920571)
          ·
            refine ⟨121143640932532252088880857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80762427288354834725920571 121143640932532252088880857)
            ·
              refine ⟨90857730699399189066660643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121143640932532252088880857 90857730699399189066660643)
              ·
                refine ⟨136286596049098783599990965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90857730699399189066660643 136286596049098783599990965)
                ·
                  refine ⟨12776868379603010962499153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136286596049098783599990965 12776868379603010962499153)
                  ·
                    refine ⟨9582651284702258221874365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12776868379603010962499153 9582651284702258221874365)
                    ·
                      refine ⟨3593494231763346833202887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9582651284702258221874365 3593494231763346833202887)
                      ·
                        rfl

theorem cell23_6998305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6998305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998305 prefixEnd_6998305 := by exact prefixLift 6998305
  have htrace : WordTrace (prefixWord ++ tailWord_6998305) baseStart_6998305 baseEnd_6998305 := by
    simpa [prefixWord, tailWord_6998305, baseEnd_6998305] using wordTrace_append hprefix tailTrace_6998305
  have hstable : (prefixWord ++ tailWord_6998305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998305).length < 2 ^ (prefixWord ++ tailWord_6998305).sum := by decide
  have hdescent : baseEnd_6998305 < baseStart_6998305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998335 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_6998335 : Nat := 118140960795 + 6998335 * 2 ^ 59
def prefixEnd_6998335 : Nat := 4983230072969 + 3 ^ 40 * 6998335 * 2
def baseEnd_6998335 : Nat := 3593509636182981715827749

theorem tailTrace_6998335 : CollatzResearch.WordTrace tailWord_6998335 prefixEnd_6998335 3593509636182981715827749 := by
  unfold tailWord_6998335
  simp only [CollatzResearch.WordTrace]
  refine ⟨255250247101234990306748459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170166831400823326871165639 255250247101234990306748459)
  ·
    refine ⟨382875370651852485460122689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255250247101234990306748459 382875370651852485460122689)
    ·
      refine ⟨287156527988889364095092017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382875370651852485460122689 287156527988889364095092017)
      ·
        refine ⟨215367395991667023071319013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287156527988889364095092017 215367395991667023071319013)
        ·
          refine ⟨40381386748437566825872315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215367395991667023071319013 40381386748437566825872315)
          ·
            refine ⟨60572080122656350238808473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40381386748437566825872315 60572080122656350238808473)
            ·
              refine ⟨45429060091992262679106355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60572080122656350238808473 45429060091992262679106355)
              ·
                refine ⟨68143590137988394018659533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45429060091992262679106355 68143590137988394018659533)
                ·
                  refine ⟨25553846301745647756997325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68143590137988394018659533 25553846301745647756997325)
                  ·
                    refine ⟨9582692363154617908873997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25553846301745647756997325 9582692363154617908873997)
                    ·
                      refine ⟨3593509636182981715827749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9582692363154617908873997 3593509636182981715827749)
                      ·
                        rfl

theorem cell23_6998335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_6998335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998335 prefixEnd_6998335 := by exact prefixLift 6998335
  have htrace : WordTrace (prefixWord ++ tailWord_6998335) baseStart_6998335 baseEnd_6998335 := by
    simpa [prefixWord, tailWord_6998335, baseEnd_6998335] using wordTrace_append hprefix tailTrace_6998335
  have hstable : (prefixWord ++ tailWord_6998335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998335).length < 2 ^ (prefixWord ++ tailWord_6998335).sum := by decide
  have hdescent : baseEnd_6998335 < baseStart_6998335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998352 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 4, 1, 3]
def baseStart_6998352 : Nat := 118140960795 + 6998352 * 2 ^ 59
def prefixEnd_6998352 : Nat := 4983230072969 + 3 ^ 40 * 6998352 * 2
def baseEnd_6998352 : Nat := 3593518365354108149315171

theorem tailTrace_6998352 : CollatzResearch.WordTrace tailWord_6998352 prefixEnd_6998352 3593518365354108149315171 := by
  unfold tailWord_6998352
  simp only [CollatzResearch.WordTrace]
  refine ⟨127625433571086701105058655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170167244761448934806744873 127625433571086701105058655)
  ·
    refine ⟨191438150356630051657587983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127625433571086701105058655 191438150356630051657587983)
    ·
      refine ⟨287157225534945077486381975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191438150356630051657587983 287157225534945077486381975)
      ·
        refine ⟨430735838302417616229572963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287157225534945077486381975 430735838302417616229572963)
        ·
          refine ⟨646103757453626424344359445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430735838302417616229572963 646103757453626424344359445)
          ·
            refine ⟨30286113630638738641141849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 646103757453626424344359445 30286113630638738641141849)
            ·
              refine ⟨22714585222979053980856387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30286113630638738641141849 22714585222979053980856387)
              ·
                refine ⟨34071877834468580971284581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22714585222979053980856387 34071877834468580971284581)
                ·
                  refine ⟨6388477093962858932115859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34071877834468580971284581 6388477093962858932115859)
                  ·
                    refine ⟨9582715640944288398173789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6388477093962858932115859 9582715640944288398173789)
                    ·
                      refine ⟨3593518365354108149315171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9582715640944288398173789 3593518365354108149315171)
                      ·
                        rfl

theorem cell23_6998352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_6998352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998352 prefixEnd_6998352 := by exact prefixLift 6998352
  have htrace : WordTrace (prefixWord ++ tailWord_6998352) baseStart_6998352 baseEnd_6998352 := by
    simpa [prefixWord, tailWord_6998352, baseEnd_6998352] using wordTrace_append hprefix tailTrace_6998352
  have hstable : (prefixWord ++ tailWord_6998352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998352).length < 2 ^ (prefixWord ++ tailWord_6998352).sum := by decide
  have hdescent : baseEnd_6998352 < baseStart_6998352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998353 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 1, 2, 2]
def baseStart_6998353 : Nat := 118140960795 + 6998353 * 2 ^ 59
def prefixEnd_6998353 : Nat := 4983230072969 + 3 ^ 40 * 6998353 * 2
def baseEnd_6998353 : Nat := 3593518878834762645402667

theorem tailTrace_6998353 : CollatzResearch.WordTrace tailWord_6998353 prefixEnd_6998353 3593518878834762645402667 := by
  unfold tailWord_6998353
  simp only [CollatzResearch.WordTrace]
  refine ⟨255250903615169779380903713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170167269076779852920602475 255250903615169779380903713)
  ·
    refine ⟨191438177711377334535677785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255250903615169779380903713 191438177711377334535677785)
    ·
      refine ⟨143578633283533000901758339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191438177711377334535677785 143578633283533000901758339)
      ·
        refine ⟨215367949925299501352637509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143578633283533000901758339 215367949925299501352637509)
        ·
          refine ⟨40381490610993656503619533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215367949925299501352637509 40381490610993656503619533)
          ·
            refine ⟨15143058979122621188857325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40381490610993656503619533 15143058979122621188857325)
            ·
              refine ⟨5678647117170982945821497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15143058979122621188857325 5678647117170982945821497)
              ·
                refine ⟨4258985337878237209366123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678647117170982945821497 4258985337878237209366123)
                ·
                  refine ⟨6388478006817355814049185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258985337878237209366123 6388478006817355814049185)
                  ·
                    refine ⟨4791358505113016860536889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388478006817355814049185 4791358505113016860536889)
                    ·
                      refine ⟨3593518878834762645402667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791358505113016860536889 3593518878834762645402667)
                      ·
                        rfl

theorem cell23_6998353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_6998353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998353 prefixEnd_6998353 := by exact prefixLift 6998353
  have htrace : WordTrace (prefixWord ++ tailWord_6998353) baseStart_6998353 baseEnd_6998353 := by
    simpa [prefixWord, tailWord_6998353, baseEnd_6998353] using wordTrace_append hprefix tailTrace_6998353
  have hstable : (prefixWord ++ tailWord_6998353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998353).length < 2 ^ (prefixWord ++ tailWord_6998353).sum := by decide
  have hdescent : baseEnd_6998353 < baseStart_6998353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998362 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2]
def baseStart_6998362 : Nat := 118140960795 + 6998362 * 2 ^ 59
def prefixEnd_6998362 : Nat := 4983230072969 + 3 ^ 40 * 6998362 * 2
def baseEnd_6998362 : Nat := 3593523500160653110190125

theorem tailTrace_6998362 : CollatzResearch.WordTrace tailWord_6998362 prefixEnd_6998362 3593523500160653110190125 := by
  unfold tailWord_6998362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63812807968034293479495335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170167487914758115945320893 63812807968034293479495335)
  ·
    refine ⟨95719211952051440219243003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63812807968034293479495335 95719211952051440219243003)
    ·
      refine ⟨143578817928077160328864505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95719211952051440219243003 143578817928077160328864505)
      ·
        refine ⟨107684113446057870246648379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143578817928077160328864505 107684113446057870246648379)
        ·
          refine ⟨161526170169086805369972569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107684113446057870246648379 161526170169086805369972569)
          ·
            refine ⟨121144627626815104027479427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161526170169086805369972569 121144627626815104027479427)
            ·
              refine ⟨181716941440222656041219141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121144627626815104027479427 181716941440222656041219141)
              ·
                refine ⟨34071926520041748007728589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181716941440222656041219141 34071926520041748007728589)
                ·
                  refine ⟨12776972445015655502898221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34071926520041748007728589 12776972445015655502898221)
                  ·
                    refine ⟨4791364666880870813586833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12776972445015655502898221 4791364666880870813586833)
                    ·
                      refine ⟨3593523500160653110190125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791364666880870813586833 3593523500160653110190125)
                      ·
                        rfl

theorem cell23_6998362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_6998362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998362 prefixEnd_6998362 := by exact prefixLift 6998362
  have htrace : WordTrace (prefixWord ++ tailWord_6998362) baseStart_6998362 baseEnd_6998362 := by
    simpa [prefixWord, tailWord_6998362, baseEnd_6998362] using wordTrace_append hprefix tailTrace_6998362
  have hstable : (prefixWord ++ tailWord_6998362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998362).length < 2 ^ (prefixWord ++ tailWord_6998362).sum := by decide
  have hdescent : baseEnd_6998362 < baseStart_6998362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998395 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5]
def baseStart_6998395 : Nat := 118140960795 + 6998395 * 2 ^ 59
def prefixEnd_6998395 : Nat := 4983230072969 + 3 ^ 40 * 6998395 * 2
def baseEnd_6998395 : Nat := 3593540445022251481077473

theorem tailTrace_6998395 : CollatzResearch.WordTrace tailWord_6998395 prefixEnd_6998395 3593540445022251481077473 := by
  unfold tailWord_6998395
  simp only [CollatzResearch.WordTrace]
  refine ⟨255252435481017620553932639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170168290320678413702621759 255252435481017620553932639)
  ·
    refine ⟨382878653221526430830898959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255252435481017620553932639 382878653221526430830898959)
    ·
      refine ⟨574317979832289646246348439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382878653221526430830898959 574317979832289646246348439)
      ·
        refine ⟨861476969748434469369522659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574317979832289646246348439 861476969748434469369522659)
        ·
          refine ⟨1292215454622651704054283989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861476969748434469369522659 1292215454622651704054283989)
          ·
            refine ⟨30286299717718399313772281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1292215454622651704054283989 30286299717718399313772281)
            ·
              refine ⟨22714724788288799485329211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30286299717718399313772281 22714724788288799485329211)
              ·
                refine ⟨34072087182433199227993817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22714724788288799485329211 34072087182433199227993817)
                ·
                  refine ⟨25554065386824899420995363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34072087182433199227993817 25554065386824899420995363)
                  ·
                    refine ⟨38331098080237349131493045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25554065386824899420995363 38331098080237349131493045)
                    ·
                      refine ⟨3593540445022251481077473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38331098080237349131493045 3593540445022251481077473)
                      ·
                        rfl

theorem cell23_6998395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_6998395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998395 prefixEnd_6998395 := by exact prefixLift 6998395
  have htrace : WordTrace (prefixWord ++ tailWord_6998395) baseStart_6998395 baseEnd_6998395 := by
    simpa [prefixWord, tailWord_6998395, baseEnd_6998395] using wordTrace_append hprefix tailTrace_6998395
  have hstable : (prefixWord ++ tailWord_6998395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998395).length < 2 ^ (prefixWord ++ tailWord_6998395).sum := by decide
  have hdescent : baseEnd_6998395 < baseStart_6998395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998405 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_6998405 : Nat := 118140960795 + 6998405 * 2 ^ 59
def prefixEnd_6998405 : Nat := 4983230072969 + 3 ^ 40 * 6998405 * 2
def baseEnd_6998405 : Nat := 3593545579828796441952427

theorem tailTrace_6998405 : CollatzResearch.WordTrace tailWord_6998405 prefixEnd_6998405 3593545579828796441952427 := by
  unfold tailWord_6998405
  simp only [CollatzResearch.WordTrace]
  refine ⟨255252800210981392261796669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170168533473987594841197779 255252800210981392261796669)
  ·
    refine ⟨95719800079118022098173751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255252800210981392261796669 95719800079118022098173751)
    ·
      refine ⟨143579700118677033147260627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95719800079118022098173751 143579700118677033147260627)
      ·
        refine ⟨215369550178015549720890941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143579700118677033147260627 215369550178015549720890941)
        ·
          refine ⟨80763581316755831145334103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215369550178015549720890941 80763581316755831145334103)
          ·
            refine ⟨121145371975133746718001155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80763581316755831145334103 121145371975133746718001155)
            ·
              refine ⟨181718057962700620077001733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121145371975133746718001155 181718057962700620077001733)
              ·
                refine ⟨34072135868006366264437825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181718057962700620077001733 34072135868006366264437825)
                ·
                  refine ⟨25554101901004774698328369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34072135868006366264437825 25554101901004774698328369)
                  ·
                    refine ⟨19165576425753581023746277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25554101901004774698328369 19165576425753581023746277)
                    ·
                      refine ⟨3593545579828796441952427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19165576425753581023746277 3593545579828796441952427)
                      ·
                        rfl

theorem cell23_6998405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_6998405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998405 prefixEnd_6998405 := by exact prefixLift 6998405
  have htrace : WordTrace (prefixWord ++ tailWord_6998405) baseStart_6998405 baseEnd_6998405 := by
    simpa [prefixWord, tailWord_6998405, baseEnd_6998405] using wordTrace_append hprefix tailTrace_6998405
  have hstable : (prefixWord ++ tailWord_6998405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998405).length < 2 ^ (prefixWord ++ tailWord_6998405).sum := by decide
  have hdescent : baseEnd_6998405 < baseStart_6998405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998426 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2]
def baseStart_6998426 : Nat := 118140960795 + 6998426 * 2 ^ 59
def prefixEnd_6998426 : Nat := 4983230072969 + 3 ^ 40 * 6998426 * 2
def baseEnd_6998426 : Nat := 3593556362922540859789831

theorem tailTrace_6998426 : CollatzResearch.WordTrace tailWord_6998426 prefixEnd_6998426 3593556362922540859789831 := by
  unfold tailWord_6998426
  simp only [CollatzResearch.WordTrace]
  refine ⟨63813391535976328212077783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170169044095936875232207421 63813391535976328212077783)
  ·
    refine ⟨95720087303964492318116675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63813391535976328212077783 95720087303964492318116675)
    ·
      refine ⟨143580130955946738477175013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95720087303964492318116675 143580130955946738477175013)
      ·
        refine ⟨26921274554240013464470315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143580130955946738477175013 26921274554240013464470315)
        ·
          refine ⟨40381911831360020196705473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26921274554240013464470315 40381911831360020196705473)
          ·
            refine ⟨30286433873520015147529105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40381911831360020196705473 30286433873520015147529105)
            ·
              refine ⟨22714825405140011360646829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30286433873520015147529105 22714825405140011360646829)
              ·
                refine ⟨8518059526927504260242561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22714825405140011360646829 8518059526927504260242561)
                ·
                  refine ⟨6388544645195628195181921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8518059526927504260242561 6388544645195628195181921)
                  ·
                    refine ⟨4791408483896721146386441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388544645195628195181921 4791408483896721146386441)
                    ·
                      refine ⟨3593556362922540859789831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791408483896721146386441 3593556362922540859789831)
                      ·
                        rfl

theorem cell23_6998426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_6998426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998426 prefixEnd_6998426 := by exact prefixLift 6998426
  have htrace : WordTrace (prefixWord ++ tailWord_6998426) baseStart_6998426 baseEnd_6998426 := by
    simpa [prefixWord, tailWord_6998426, baseEnd_6998426] using wordTrace_append hprefix tailTrace_6998426
  have hstable : (prefixWord ++ tailWord_6998426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998426).length < 2 ^ (prefixWord ++ tailWord_6998426).sum := by decide
  have hdescent : baseEnd_6998426 < baseStart_6998426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998449 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 5]
def baseStart_6998449 : Nat := 118140960795 + 6998449 * 2 ^ 59
def prefixEnd_6998449 : Nat := 4983230072969 + 3 ^ 40 * 6998449 * 2
def baseEnd_6998449 : Nat := 399285352553066029978025

theorem tailTrace_6998449 : CollatzResearch.WordTrace tailWord_6998449 prefixEnd_6998449 399285352553066029978025 := by
  unfold tailWord_6998449
  simp only [CollatzResearch.WordTrace]
  refine ⟨255254405022821987776398401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170169603348547991850932267 255254405022821987776398401)
  ·
    refine ⟨191440803767116490832298801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255254405022821987776398401 191440803767116490832298801)
    ·
      refine ⟨143580602825337368124224101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191440803767116490832298801 143580602825337368124224101)
      ·
        refine ⟨26921363029750756523292019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143580602825337368124224101 26921363029750756523292019)
        ·
          refine ⟨40382044544626134784938029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26921363029750756523292019 40382044544626134784938029)
          ·
            refine ⟨15143266704234800544351761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40382044544626134784938029 15143266704234800544351761)
            ·
              refine ⟨11357450028176100408263821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15143266704234800544351761 11357450028176100408263821)
              ·
                refine ⟨4259043760566037653098933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11357450028176100408263821 4259043760566037653098933)
                ·
                  refine ⟨399285352553066029978025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259043760566037653098933 399285352553066029978025)
                  ·
                    rfl

theorem cell23_6998449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 5].length) (baseStart_6998449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998449 prefixEnd_6998449 := by exact prefixLift 6998449
  have htrace : WordTrace (prefixWord ++ tailWord_6998449) baseStart_6998449 baseEnd_6998449 := by
    simpa [prefixWord, tailWord_6998449, baseEnd_6998449] using wordTrace_append hprefix tailTrace_6998449
  have hstable : (prefixWord ++ tailWord_6998449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998449).length < 2 ^ (prefixWord ++ tailWord_6998449).sum := by decide
  have hdescent : baseEnd_6998449 < baseStart_6998449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998462 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6998462 : Nat := 118140960795 + 6998462 * 2 ^ 59
def prefixEnd_6998462 : Nat := 4983230072969 + 3 ^ 40 * 6998462 * 2
def baseEnd_6998462 : Nat := 1197858282742034239646555

theorem tailTrace_6998462 : CollatzResearch.WordTrace tailWord_6998462 prefixEnd_6998462 1197858282742034239646555 := by
  unfold tailWord_6998462
  simp only [CollatzResearch.WordTrace]
  refine ⟨31906859896471861374577705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170169919447849927331081093 31906859896471861374577705)
  ·
    refine ⟨23930144922353896030933279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31906859896471861374577705 23930144922353896030933279)
    ·
      refine ⟨35895217383530844046399919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23930144922353896030933279 35895217383530844046399919)
      ·
        refine ⟨53842826075296266069599879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35895217383530844046399919 53842826075296266069599879)
        ·
          refine ⟨80764239112944399104399819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53842826075296266069599879 80764239112944399104399819)
          ·
            refine ⟨121146358669416598656599729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80764239112944399104399819 121146358669416598656599729)
            ·
              refine ⟨90859769002062448992449797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121146358669416598656599729 90859769002062448992449797)
              ·
                refine ⟨17036206687886709186084337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90859769002062448992449797 17036206687886709186084337)
                ·
                  refine ⟨12777155015915031889563253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17036206687886709186084337 12777155015915031889563253)
                  ·
                    refine ⟨1197858282742034239646555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12777155015915031889563253 1197858282742034239646555)
                    ·
                      rfl

theorem cell23_6998462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6998462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998462 prefixEnd_6998462 := by exact prefixLift 6998462
  have htrace : WordTrace (prefixWord ++ tailWord_6998462) baseStart_6998462 baseEnd_6998462 := by
    simpa [prefixWord, tailWord_6998462, baseEnd_6998462] using wordTrace_append hprefix tailTrace_6998462
  have hstable : (prefixWord ++ tailWord_6998462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998462).length < 2 ^ (prefixWord ++ tailWord_6998462).sum := by decide
  have hdescent : baseEnd_6998462 < baseStart_6998462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998539 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 6]
def baseStart_6998539 : Nat := 118140960795 + 6998539 * 2 ^ 59
def prefixEnd_6998539 : Nat := 4983230072969 + 3 ^ 40 * 6998539 * 2
def baseEnd_6998539 : Nat := 399290487359610990852979

theorem tailTrace_6998539 : CollatzResearch.WordTrace tailWord_6998539 prefixEnd_6998539 399290487359610990852979 := by
  unfold tailWord_6998539
  simp only [CollatzResearch.WordTrace]
  refine ⟨255257687592495933147174671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170171791728330622098116447 255257687592495933147174671)
  ·
    refine ⟨382886531388743899720762007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255257687592495933147174671 382886531388743899720762007)
    ·
      refine ⟨574329797083115849581143011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382886531388743899720762007 574329797083115849581143011)
      ·
        refine ⟨861494695624673774371714517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574329797083115849581143011 861494695624673774371714517)
        ·
          refine ⟨20191281928703291586837059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 861494695624673774371714517 20191281928703291586837059)
          ·
            refine ⟨30286922893054937380255589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20191281928703291586837059 30286922893054937380255589)
            ·
              refine ⟨5678798042447800758797923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30286922893054937380255589 5678798042447800758797923)
              ·
                refine ⟨8518197063671701138196885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678798042447800758797923 8518197063671701138196885)
                ·
                  refine ⟨399290487359610990852979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8518197063671701138196885 399290487359610990852979)
                  ·
                    rfl

theorem cell23_6998539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 6].length) (baseStart_6998539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998539 prefixEnd_6998539 := by exact prefixLift 6998539
  have htrace : WordTrace (prefixWord ++ tailWord_6998539) baseStart_6998539 baseEnd_6998539 := by
    simpa [prefixWord, tailWord_6998539, baseEnd_6998539] using wordTrace_append hprefix tailTrace_6998539
  have hstable : (prefixWord ++ tailWord_6998539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998539).length < 2 ^ (prefixWord ++ tailWord_6998539).sum := by decide
  have hdescent : baseEnd_6998539 < baseStart_6998539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998545 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_6998545 : Nat := 118140960795 + 6998545 * 2 ^ 59
def prefixEnd_6998545 : Nat := 4983230072969 + 3 ^ 40 * 6998545 * 2
def baseEnd_6998545 : Nat := 3593617467120425894201783

theorem tailTrace_6998545 : CollatzResearch.WordTrace tailWord_6998545 prefixEnd_6998545 3593617467120425894201783 := by
  unfold tailWord_6998545
  simp only [CollatzResearch.WordTrace]
  refine ⟨255257906430474196171893089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170171937620316130781262059 255257906430474196171893089)
  ·
    refine ⟨191443429822855647128919817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255257906430474196171893089 191443429822855647128919817)
    ·
      refine ⟨143582572367141735346689863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191443429822855647128919817 143582572367141735346689863)
      ·
        refine ⟨215373858550712603020034795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143582572367141735346689863 215373858550712603020034795)
        ·
          refine ⟨323060787826068904530052193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215373858550712603020034795 323060787826068904530052193)
          ·
            refine ⟨242295590869551678397539145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323060787826068904530052193 242295590869551678397539145)
            ·
              refine ⟨181721693152163758798154359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242295590869551678397539145 181721693152163758798154359)
              ·
                refine ⟨272582539728245638197231539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181721693152163758798154359 272582539728245638197231539)
                ·
                  refine ⟨408873809592368457295847309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272582539728245638197231539 408873809592368457295847309)
                  ·
                    refine ⟨153327678597138171485942741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408873809592368457295847309 153327678597138171485942741)
                    ·
                      refine ⟨3593617467120425894201783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153327678597138171485942741 3593617467120425894201783)
                      ·
                        rfl

theorem cell23_6998545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_6998545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998545 prefixEnd_6998545 := by exact prefixLift 6998545
  have htrace : WordTrace (prefixWord ++ tailWord_6998545) baseStart_6998545 baseEnd_6998545 := by
    simpa [prefixWord, tailWord_6998545, baseEnd_6998545] using wordTrace_append hprefix tailTrace_6998545
  have hstable : (prefixWord ++ tailWord_6998545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998545).length < 2 ^ (prefixWord ++ tailWord_6998545).sum := by decide
  have hdescent : baseEnd_6998545 < baseStart_6998545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998549 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_6998549 : Nat := 118140960795 + 6998549 * 2 ^ 59
def prefixEnd_6998549 : Nat := 4983230072969 + 3 ^ 40 * 6998549 * 2
def baseEnd_6998549 : Nat := 3593619521043043878551765

theorem tailTrace_6998549 : CollatzResearch.WordTrace tailWord_6998549 prefixEnd_6998549 3593619521043043878551765 := by
  unfold tailWord_6998549
  simp only [CollatzResearch.WordTrace]
  refine ⟨255258052322459704855038701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170172034881639803236692467 255258052322459704855038701)
  ·
    refine ⟨95721769620922389320639513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255258052322459704855038701 95721769620922389320639513)
    ·
      refine ⟨71791327215691791990479635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95721769620922389320639513 71791327215691791990479635)
      ·
        refine ⟨107686990823537687985719453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71791327215691791990479635 107686990823537687985719453)
        ·
          refine ⟨40382621558826632994644795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107686990823537687985719453 40382621558826632994644795)
          ·
            refine ⟨60573932338239949491967193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40382621558826632994644795 60573932338239949491967193)
            ·
              refine ⟨45430449253679962118975395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60573932338239949491967193 45430449253679962118975395)
              ·
                refine ⟨68145673880519943178463093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45430449253679962118975395 68145673880519943178463093)
                ·
                  refine ⟨6388656926298744672980915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68145673880519943178463093 6388656926298744672980915)
                  ·
                    refine ⟨9582985389448117009471373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6388656926298744672980915 9582985389448117009471373)
                    ·
                      refine ⟨3593619521043043878551765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9582985389448117009471373 3593619521043043878551765)
                      ·
                        rfl

theorem cell23_6998549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_6998549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998549 prefixEnd_6998549 := by exact prefixLift 6998549
  have htrace : WordTrace (prefixWord ++ tailWord_6998549) baseStart_6998549 baseEnd_6998549 := by
    simpa [prefixWord, tailWord_6998549, baseEnd_6998549] using wordTrace_append hprefix tailTrace_6998549
  have hstable : (prefixWord ++ tailWord_6998549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998549).length < 2 ^ (prefixWord ++ tailWord_6998549).sum := by decide
  have hdescent : baseEnd_6998549 < baseStart_6998549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998589 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6998589 : Nat := 118140960795 + 6998589 * 2 ^ 59
def prefixEnd_6998589 : Nat := 4983230072969 + 3 ^ 40 * 6998589 * 2
def baseEnd_6998589 : Nat := 3593640060269223722051581

theorem tailTrace_6998589 : CollatzResearch.WordTrace tailWord_6998589 prefixEnd_6998589 3593640060269223722051581 := by
  unfold tailWord_6998589
  simp only [CollatzResearch.WordTrace]
  refine ⟨255259511242314791686494821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170173007494876527790996547 255259511242314791686494821)
  ·
    refine ⟨47861158357934023441217779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255259511242314791686494821 47861158357934023441217779)
    ·
      refine ⟨71791737536901035161826669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47861158357934023441217779 71791737536901035161826669)
      ·
        refine ⟨26921901576337888185685001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71791737536901035161826669 26921901576337888185685001)
        ·
          refine ⟨20191426182253416139263751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26921901576337888185685001 20191426182253416139263751)
          ·
            refine ⟨30287139273380124208895627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20191426182253416139263751 30287139273380124208895627)
            ·
              refine ⟨45430708910070186313343441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30287139273380124208895627 45430708910070186313343441)
              ·
                refine ⟨34073031682552639735007581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45430708910070186313343441 34073031682552639735007581)
                ·
                  refine ⟨12777386880957239900627843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34073031682552639735007581 12777386880957239900627843)
                  ·
                    refine ⟨19166080321435859850941765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12777386880957239900627843 19166080321435859850941765)
                    ·
                      refine ⟨3593640060269223722051581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19166080321435859850941765 3593640060269223722051581)
                      ·
                        rfl

theorem cell23_6998589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6998589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998589 prefixEnd_6998589 := by exact prefixLift 6998589
  have htrace : WordTrace (prefixWord ++ tailWord_6998589) baseStart_6998589 baseEnd_6998589 := by
    simpa [prefixWord, tailWord_6998589, baseEnd_6998589] using wordTrace_append hprefix tailTrace_6998589
  have hstable : (prefixWord ++ tailWord_6998589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998589).length < 2 ^ (prefixWord ++ tailWord_6998589).sum := by decide
  have hdescent : baseEnd_6998589 < baseStart_6998589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998592 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_6998592 : Nat := 118140960795 + 6998592 * 2 ^ 59
def prefixEnd_6998592 : Nat := 4983230072969 + 3 ^ 40 * 6998592 * 2
def baseEnd_6998592 : Nat := 3593641600711187210314067

theorem tailTrace_6998592 : CollatzResearch.WordTrace tailWord_6998592 prefixEnd_6998592 3593641600711187210314067 := by
  unfold tailWord_6998592
  simp only [CollatzResearch.WordTrace]
  refine ⟨127629810330651961599427015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170173080440869282132569353 127629810330651961599427015)
  ·
    refine ⟨191444715495977942399140523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127629810330651961599427015 191444715495977942399140523)
    ·
      refine ⟨287167073243966913598710785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191444715495977942399140523 287167073243966913598710785)
      ·
        refine ⟨215375304932975185199033089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287167073243966913598710785 215375304932975185199033089)
        ·
          refine ⟨161531478699731388899274817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215375304932975185199033089 161531478699731388899274817)
          ·
            refine ⟨121148609024798541674456113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161531478699731388899274817 121148609024798541674456113)
            ·
              refine ⟨90861456768598906255842085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121148609024798541674456113 90861456768598906255842085)
              ·
                refine ⟨17036523144112294922970391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90861456768598906255842085 17036523144112294922970391)
                ·
                  refine ⟨25554784716168442384455587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17036523144112294922970391 25554784716168442384455587)
                  ·
                    refine ⟨38332177074252663576683381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25554784716168442384455587 38332177074252663576683381)
                    ·
                      refine ⟨3593641600711187210314067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38332177074252663576683381 3593641600711187210314067)
                      ·
                        rfl

theorem cell23_6998592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_6998592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998592 prefixEnd_6998592 := by exact prefixLift 6998592
  have htrace : WordTrace (prefixWord ++ tailWord_6998592) baseStart_6998592 baseEnd_6998592 := by
    simpa [prefixWord, tailWord_6998592, baseEnd_6998592] using wordTrace_append hprefix tailTrace_6998592
  have hstable : (prefixWord ++ tailWord_6998592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998592).length < 2 ^ (prefixWord ++ tailWord_6998592).sum := by decide
  have hdescent : baseEnd_6998592 < baseStart_6998592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998599 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 1, 6]
def baseStart_6998599 : Nat := 118140960795 + 6998599 * 2 ^ 59
def prefixEnd_6998599 : Nat := 4983230072969 + 3 ^ 40 * 6998599 * 2
def baseEnd_6998599 : Nat := 1197881731691922894308845

theorem tailTrace_6998599 : CollatzResearch.WordTrace tailWord_6998599 prefixEnd_6998599 1197881731691922894308845 := by
  unfold tailWord_6998599
  simp only [CollatzResearch.WordTrace]
  refine ⟨255259875972278563394358851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170173250648185708929572567 255259875972278563394358851)
  ·
    refine ⟨382889813958417845091538277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255259875972278563394358851 382889813958417845091538277)
    ·
      refine ⟨71791840117203345954663427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382889813958417845091538277 71791840117203345954663427)
      ·
        refine ⟨107687760175805018931995141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71791840117203345954663427 107687760175805018931995141)
        ·
          refine ⟨20191455032963441049749089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107687760175805018931995141 20191455032963441049749089)
          ·
            refine ⟨15143591274722580787311817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20191455032963441049749089 15143591274722580787311817)
            ·
              refine ⟨11357693456041935590483863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15143591274722580787311817 11357693456041935590483863)
              ·
                refine ⟨17036540184062903385725795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357693456041935590483863 17036540184062903385725795)
                ·
                  refine ⟨25554810276094355078588693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17036540184062903385725795 25554810276094355078588693)
                  ·
                    refine ⟨1197881731691922894308845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25554810276094355078588693 1197881731691922894308845)
                    ·
                      rfl

theorem cell23_6998599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_6998599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998599 prefixEnd_6998599 := by exact prefixLift 6998599
  have htrace : WordTrace (prefixWord ++ tailWord_6998599) baseStart_6998599 baseEnd_6998599 := by
    simpa [prefixWord, tailWord_6998599, baseEnd_6998599] using wordTrace_append hprefix tailTrace_6998599
  have hstable : (prefixWord ++ tailWord_6998599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998599).length < 2 ^ (prefixWord ++ tailWord_6998599).sum := by decide
  have hdescent : baseEnd_6998599 < baseStart_6998599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998606 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_6998606 : Nat := 118140960795 + 6998606 * 2 ^ 59
def prefixEnd_6998606 : Nat := 4983230072969 + 3 ^ 40 * 6998606 * 2
def baseEnd_6998606 : Nat := 3593648789440350155539003

theorem tailTrace_6998606 : CollatzResearch.WordTrace tailWord_6998606 prefixEnd_6998606 3593648789440350155539003 := by
  unfold tailWord_6998606
  simp only [CollatzResearch.WordTrace]
  refine ⟨31907516410406650448732959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170173420855502135726575781 31907516410406650448732959)
  ·
    refine ⟨47861274615609975673099439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31907516410406650448732959 47861274615609975673099439)
    ·
      refine ⟨71791911923414963509649159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47861274615609975673099439 71791911923414963509649159)
      ·
        refine ⟨107687867885122445264473739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71791911923414963509649159 107687867885122445264473739)
        ·
          refine ⟨161531801827683667896710609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107687867885122445264473739 161531801827683667896710609)
          ·
            refine ⟨121148851370762750922532957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161531801827683667896710609 121148851370762750922532957)
            ·
              refine ⟨45430819264036031595949859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121148851370762750922532957 45430819264036031595949859)
              ·
                refine ⟨68146228896054047393924789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45430819264036031595949859 68146228896054047393924789)
                ·
                  refine ⟨6388708959005066943180449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68146228896054047393924789 6388708959005066943180449)
                  ·
                    refine ⟨4791531719253800207385337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388708959005066943180449 4791531719253800207385337)
                    ·
                      refine ⟨3593648789440350155539003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791531719253800207385337 3593648789440350155539003)
                      ·
                        rfl

theorem cell23_6998606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_6998606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998606 prefixEnd_6998606 := by exact prefixLift 6998606
  have htrace : WordTrace (prefixWord ++ tailWord_6998606) baseStart_6998606 baseEnd_6998606 := by
    simpa [prefixWord, tailWord_6998606, baseEnd_6998606] using wordTrace_append hprefix tailTrace_6998606
  have hstable : (prefixWord ++ tailWord_6998606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998606).length < 2 ^ (prefixWord ++ tailWord_6998606).sum := by decide
  have hdescent : baseEnd_6998606 < baseStart_6998606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998609 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_6998609 : Nat := 118140960795 + 6998609 * 2 ^ 59
def prefixEnd_6998609 : Nat := 4983230072969 + 3 ^ 40 * 6998609 * 2
def baseEnd_6998609 : Nat := 3593650329882313643801489

theorem tailTrace_6998609 : CollatzResearch.WordTrace tailWord_6998609 prefixEnd_6998609 3593650329882313643801489 := by
  unfold tailWord_6998609
  simp only [CollatzResearch.WordTrace]
  refine ⟨255260240702242335102222881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170173493801494890068148587 255260240702242335102222881)
  ·
    refine ⟨191445180526681751326667161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255260240702242335102222881 191445180526681751326667161)
    ·
      refine ⟨143583885395011313495000371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191445180526681751326667161 143583885395011313495000371)
      ·
        refine ⟨215375828092516970242500557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143583885395011313495000371 215375828092516970242500557)
        ·
          refine ⟨80765935534693863840937709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215375828092516970242500557 80765935534693863840937709)
          ·
            refine ⟨30287225825510198940351641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80765935534693863840937709 30287225825510198940351641)
            ·
              refine ⟨22715419369132649205263731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30287225825510198940351641 22715419369132649205263731)
              ·
                refine ⟨34073129053698973807895597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22715419369132649205263731 34073129053698973807895597)
                ·
                  refine ⟨12777423395137115177960849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34073129053698973807895597 12777423395137115177960849)
                  ·
                    refine ⟨9583067546352836383470637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12777423395137115177960849 9583067546352836383470637)
                    ·
                      refine ⟨3593650329882313643801489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583067546352836383470637 3593650329882313643801489)
                      ·
                        rfl

theorem cell23_6998609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_6998609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998609 prefixEnd_6998609 := by exact prefixLift 6998609
  have htrace : WordTrace (prefixWord ++ tailWord_6998609) baseStart_6998609 baseEnd_6998609 := by
    simpa [prefixWord, tailWord_6998609, baseEnd_6998609] using wordTrace_append hprefix tailTrace_6998609
  have hstable : (prefixWord ++ tailWord_6998609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998609).length < 2 ^ (prefixWord ++ tailWord_6998609).sum := by decide
  have hdescent : baseEnd_6998609 < baseStart_6998609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998620 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6998620 : Nat := 118140960795 + 6998620 * 2 ^ 59
def prefixEnd_6998620 : Nat := 4983230072969 + 3 ^ 40 * 6998620 * 2
def baseEnd_6998620 : Nat := 1197885326056504366921313

theorem tailTrace_6998620 : CollatzResearch.WordTrace tailWord_6998620 prefixEnd_6998620 1197885326056504366921313 := by
  unfold tailWord_6998620
  simp only [CollatzResearch.WordTrace]
  refine ⟨127630320952601241990436657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170173761270134989320582209 127630320952601241990436657)
  ·
    refine ⟨95722740714450931492827493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127630320952601241990436657 95722740714450931492827493)
    ·
      refine ⟨17948013883959549654905155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95722740714450931492827493 17948013883959549654905155)
      ·
        refine ⟨26922020825939324482357733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17948013883959549654905155 26922020825939324482357733)
        ·
          refine ⟨5047878904863623340442075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26922020825939324482357733 5047878904863623340442075)
          ·
            refine ⟨7571818357295435010663113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047878904863623340442075 7571818357295435010663113)
            ·
              refine ⟨5678863767971576257997335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7571818357295435010663113 5678863767971576257997335)
              ·
                refine ⟨8518295651957364386996003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678863767971576257997335 8518295651957364386996003)
                ·
                  refine ⟨12777443477936046580494005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518295651957364386996003 12777443477936046580494005)
                  ·
                    refine ⟨1197885326056504366921313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12777443477936046580494005 1197885326056504366921313)
                    ·
                      rfl

theorem cell23_6998620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6998620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998620 prefixEnd_6998620 := by exact prefixLift 6998620
  have htrace : WordTrace (prefixWord ++ tailWord_6998620) baseStart_6998620 baseEnd_6998620 := by
    simpa [prefixWord, tailWord_6998620, baseEnd_6998620] using wordTrace_append hprefix tailTrace_6998620
  have hstable : (prefixWord ++ tailWord_6998620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998620).length < 2 ^ (prefixWord ++ tailWord_6998620).sum := by decide
  have hdescent : baseEnd_6998620 < baseStart_6998620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998653 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_6998653 : Nat := 118140960795 + 6998653 * 2 ^ 59
def prefixEnd_6998653 : Nat := 4983230072969 + 3 ^ 40 * 6998653 * 2
def baseEnd_6998653 : Nat := 3593672923031111471651287

theorem tailTrace_6998653 : CollatzResearch.WordTrace tailWord_6998653 prefixEnd_6998653 3593672923031111471651287 := by
  unfold tailWord_6998653
  simp only [CollatzResearch.WordTrace]
  refine ⟨255261845514082930616824613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170174563676055287077883075 255261845514082930616824613)
  ·
    refine ⟨47861596033890549490654615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255261845514082930616824613 47861596033890549490654615)
    ·
      refine ⟨71792394050835824235981923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47861596033890549490654615 71792394050835824235981923)
      ·
        refine ⟨107688591076253736353972885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71792394050835824235981923 107688591076253736353972885)
        ·
          refine ⟨5047902706699393891592479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107688591076253736353972885 5047902706699393891592479)
          ·
            refine ⟨7571854060049090837388719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047902706699393891592479 7571854060049090837388719)
            ·
              refine ⟨11357781090073636256083079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571854060049090837388719 11357781090073636256083079)
              ·
                refine ⟨17036671635110454384124619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357781090073636256083079 17036671635110454384124619)
                ·
                  refine ⟨25555007452665681576186929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17036671635110454384124619 25555007452665681576186929)
                  ·
                    refine ⟨19166255589499261182140197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25555007452665681576186929 19166255589499261182140197)
                    ·
                      refine ⟨3593672923031111471651287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19166255589499261182140197 3593672923031111471651287)
                      ·
                        rfl

theorem cell23_6998653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_6998653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998653 prefixEnd_6998653 := by exact prefixLift 6998653
  have htrace : WordTrace (prefixWord ++ tailWord_6998653) baseStart_6998653 baseEnd_6998653 := by
    simpa [prefixWord, tailWord_6998653, baseEnd_6998653] using wordTrace_append hprefix tailTrace_6998653
  have hstable : (prefixWord ++ tailWord_6998653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998653).length < 2 ^ (prefixWord ++ tailWord_6998653).sum := by decide
  have hdescent : baseEnd_6998653 < baseStart_6998653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998656 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3]
def baseStart_6998656 : Nat := 118140960795 + 6998656 * 2 ^ 59
def prefixEnd_6998656 : Nat := 4983230072969 + 3 ^ 40 * 6998656 * 2
def baseEnd_6998656 : Nat := 3593674463473074959913773

theorem tailTrace_6998656 : CollatzResearch.WordTrace tailWord_6998656 prefixEnd_6998656 3593674463473074959913773 := by
  unfold tailWord_6998656
  simp only [CollatzResearch.WordTrace]
  refine ⟨127630977466536031064591911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170174636622048041419455881 127630977466536031064591911)
  ·
    refine ⟨191446466199804046596887867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127630977466536031064591911 191446466199804046596887867)
    ·
      refine ⟨287169699299706069895331801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191446466199804046596887867 287169699299706069895331801)
      ·
        refine ⟨215377274474779552421498851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287169699299706069895331801 215377274474779552421498851)
        ·
          refine ⟨323065911712169328632248277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215377274474779552421498851 323065911712169328632248277)
          ·
            refine ⟨7571857305753968639818319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 323065911712169328632248277 7571857305753968639818319)
            ·
              refine ⟨11357785958630952959727479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571857305753968639818319 11357785958630952959727479)
              ·
                refine ⟨17036678937946429439591219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357785958630952959727479 17036678937946429439591219)
                ·
                  refine ⟨25555018406919644159386829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17036678937946429439591219 25555018406919644159386829)
                  ·
                    refine ⟨9583131902594866559770061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25555018406919644159386829 9583131902594866559770061)
                    ·
                      refine ⟨3593674463473074959913773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583131902594866559770061 3593674463473074959913773)
                      ·
                        rfl

theorem cell23_6998656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_6998656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998656 prefixEnd_6998656 := by exact prefixLift 6998656
  have htrace : WordTrace (prefixWord ++ tailWord_6998656) baseStart_6998656 baseEnd_6998656 := by
    simpa [prefixWord, tailWord_6998656, baseEnd_6998656] using wordTrace_append hprefix tailTrace_6998656
  have hstable : (prefixWord ++ tailWord_6998656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998656).length < 2 ^ (prefixWord ++ tailWord_6998656).sum := by decide
  have hdescent : baseEnd_6998656 < baseStart_6998656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998753 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 5]
def baseStart_6998753 : Nat := 118140960795 + 6998753 * 2 ^ 59
def prefixEnd_6998753 : Nat := 4983230072969 + 3 ^ 40 * 6998753 * 2
def baseEnd_6998753 : Nat := 399302696788506786711203

theorem tailTrace_6998753 : CollatzResearch.WordTrace tailWord_6998753 prefixEnd_6998753 399302696788506786711203 := by
  unfold tailWord_6998753
  simp only [CollatzResearch.WordTrace]
  refine ⟨255265492813720647695464913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170176995209147098463643275 255265492813720647695464913)
  ·
    refine ⟨191449119610290485771598685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255265492813720647695464913 191449119610290485771598685)
    ·
      refine ⟨71793419853858932164349507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191449119610290485771598685 71793419853858932164349507)
      ·
        refine ⟨107690129780788398246524261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71793419853858932164349507 107690129780788398246524261)
        ·
          refine ⟨20191899333897824671223299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107690129780788398246524261 20191899333897824671223299)
          ·
            refine ⟨30287849000846737006834949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20191899333897824671223299 30287849000846737006834949)
            ·
              refine ⟨5678971687658763188781553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30287849000846737006834949 5678971687658763188781553)
              ·
                refine ⟨4259228765744072391586165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678971687658763188781553 4259228765744072391586165)
                ·
                  refine ⟨399302696788506786711203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259228765744072391586165 399302696788506786711203)
                  ·
                    rfl

theorem cell23_6998753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 5].length) (baseStart_6998753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998753 prefixEnd_6998753 := by exact prefixLift 6998753
  have htrace : WordTrace (prefixWord ++ tailWord_6998753) baseStart_6998753 baseEnd_6998753 := by
    simpa [prefixWord, tailWord_6998753, baseEnd_6998753] using wordTrace_append hprefix tailTrace_6998753
  have hstable : (prefixWord ++ tailWord_6998753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998753).length < 2 ^ (prefixWord ++ tailWord_6998753).sum := by decide
  have hdescent : baseEnd_6998753 < baseStart_6998753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998756 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_6998756 : Nat := 118140960795 + 6998756 * 2 ^ 59
def prefixEnd_6998756 : Nat := 4983230072969 + 3 ^ 40 * 6998756 * 2
def baseEnd_6998756 : Nat := 3593725811538524568663313

theorem tailTrace_6998756 : CollatzResearch.WordTrace tailWord_6998756 prefixEnd_6998756 3593725811538524568663313 := by
  unfold tailWord_6998756
  simp only [CollatzResearch.WordTrace]
  refine ⟨127632801116354889603912061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170177068155139852805216081 127632801116354889603912061)
  ·
    refine ⟨47862300418633083601467023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127632801116354889603912061 47862300418633083601467023)
    ·
      refine ⟨71793450627949625402200535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47862300418633083601467023 71793450627949625402200535)
      ·
        refine ⟨107690175941924438103300803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71793450627949625402200535 107690175941924438103300803)
        ·
          refine ⟨161535263912886657154951205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107690175941924438103300803 161535263912886657154951205)
          ·
            refine ⟨30287861983666248216553351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161535263912886657154951205 30287861983666248216553351)
            ·
              refine ⟨45431792975499372324830027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30287861983666248216553351 45431792975499372324830027)
              ·
                refine ⟨68147689463249058487245041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45431792975499372324830027 68147689463249058487245041)
                ·
                  refine ⟨51110767097436793865433781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68147689463249058487245041 51110767097436793865433781)
                  ·
                    refine ⟨4791634415384699424884417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51110767097436793865433781 4791634415384699424884417)
                    ·
                      refine ⟨3593725811538524568663313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791634415384699424884417 3593725811538524568663313)
                      ·
                        rfl

theorem cell23_6998756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_6998756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998756 prefixEnd_6998756 := by exact prefixLift 6998756
  have htrace : WordTrace (prefixWord ++ tailWord_6998756) baseStart_6998756 baseEnd_6998756 := by
    simpa [prefixWord, tailWord_6998756, baseEnd_6998756] using wordTrace_append hprefix tailTrace_6998756
  have hstable : (prefixWord ++ tailWord_6998756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998756).length < 2 ^ (prefixWord ++ tailWord_6998756).sum := by decide
  have hdescent : baseEnd_6998756 < baseStart_6998756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998769 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_6998769 : Nat := 118140960795 + 6998769 * 2 ^ 59
def prefixEnd_6998769 : Nat := 4983230072969 + 3 ^ 40 * 6998769 * 2
def baseEnd_6998769 : Nat := 3593732486787033017800753

theorem tailTrace_6998769 : CollatzResearch.WordTrace tailWord_6998769 prefixEnd_6998769 3593732486787033017800753 := by
  unfold tailWord_6998769
  simp only [CollatzResearch.WordTrace]
  refine ⟨255266076381662682428047361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170177384254441788285364907 255266076381662682428047361)
  ·
    refine ⟨191449557286247011821035521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255266076381662682428047361 191449557286247011821035521)
    ·
      refine ⟨143587167964685258865776641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191449557286247011821035521 143587167964685258865776641)
      ·
        refine ⟨107690375973513944149332481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143587167964685258865776641 107690375973513944149332481)
        ·
          refine ⟨80767781980135458111999361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107690375973513944149332481 80767781980135458111999361)
          ·
            refine ⟨60575836485101593583999521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80767781980135458111999361 60575836485101593583999521)
            ·
              refine ⟨45431877363826195187999641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60575836485101593583999521 45431877363826195187999641)
              ·
                refine ⟨34073908022869646390999731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45431877363826195187999641 34073908022869646390999731)
                ·
                  refine ⟨51110862034304469586499597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34073908022869646390999731 51110862034304469586499597)
                  ·
                    refine ⟨19166573262864176094937349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51110862034304469586499597 19166573262864176094937349)
                    ·
                      refine ⟨3593732486787033017800753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19166573262864176094937349 3593732486787033017800753)
                      ·
                        rfl

theorem cell23_6998769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_6998769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998769 prefixEnd_6998769 := by exact prefixLift 6998769
  have htrace : WordTrace (prefixWord ++ tailWord_6998769) baseStart_6998769 baseEnd_6998769 := by
    simpa [prefixWord, tailWord_6998769, baseEnd_6998769] using wordTrace_append hprefix tailTrace_6998769
  have hstable : (prefixWord ++ tailWord_6998769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998769).length < 2 ^ (prefixWord ++ tailWord_6998769).sum := by decide
  have hdescent : baseEnd_6998769 < baseStart_6998769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998809 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 6]
def baseStart_6998809 : Nat := 118140960795 + 6998809 * 2 ^ 59
def prefixEnd_6998809 : Nat := 4983230072969 + 3 ^ 40 * 6998809 * 2
def baseEnd_6998809 : Nat := 399305891779245873477841

theorem tailTrace_6998809 : CollatzResearch.WordTrace tailWord_6998809 prefixEnd_6998809 399305891779245873477841 := by
  unfold tailWord_6998809
  simp only [CollatzResearch.WordTrace]
  refine ⟨255267535301517769259503481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170178356867678512839668987 255267535301517769259503481)
  ·
    refine ⟨191450651476138326944627611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255267535301517769259503481 191450651476138326944627611)
    ·
      refine ⟨287175977214207490416941417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191450651476138326944627611 287175977214207490416941417)
      ·
        refine ⟨215381982910655617812706063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287175977214207490416941417 215381982910655617812706063)
        ·
          refine ⟨323072974365983426719059095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215381982910655617812706063 323072974365983426719059095)
          ·
            refine ⟨484609461548975140078588643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323072974365983426719059095 484609461548975140078588643)
            ·
              refine ⟨726914192323462710117882965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484609461548975140078588643 726914192323462710117882965)
              ·
                refine ⟨8518525691290578634193941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 726914192323462710117882965 8518525691290578634193941)
                ·
                  refine ⟨399305891779245873477841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8518525691290578634193941 399305891779245873477841)
                  ·
                    rfl

theorem cell23_6998809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_6998809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998809 prefixEnd_6998809 := by exact prefixLift 6998809
  have htrace : WordTrace (prefixWord ++ tailWord_6998809) baseStart_6998809 baseEnd_6998809 := by
    simpa [prefixWord, tailWord_6998809, baseEnd_6998809] using wordTrace_append hprefix tailTrace_6998809
  have hstable : (prefixWord ++ tailWord_6998809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998809).length < 2 ^ (prefixWord ++ tailWord_6998809).sum := by decide
  have hdescent : baseEnd_6998809 < baseStart_6998809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998856 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 1, 5]
def baseStart_6998856 : Nat := 118140960795 + 6998856 * 2 ^ 59
def prefixEnd_6998856 : Nat := 4983230072969 + 3 ^ 40 * 6998856 * 2
def baseEnd_6998856 : Nat := 1197925719867991392470951

theorem tailTrace_6998856 : CollatzResearch.WordTrace tailWord_6998856 prefixEnd_6998856 1197925719867991392470951 := by
  unfold tailWord_6998856
  simp only [CollatzResearch.WordTrace]
  refine ⟨127634624766173748143232211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170179499688231664190976281 127634624766173748143232211)
  ·
    refine ⟨191451937149260622214848317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127634624766173748143232211 191451937149260622214848317)
    ·
      refine ⟨71794476430972733330568119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191451937149260622214848317 71794476430972733330568119)
      ·
        refine ⟨107691714646459099995852179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71794476430972733330568119 107691714646459099995852179)
        ·
          refine ⟨161537571969688649993778269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107691714646459099995852179 161537571969688649993778269)
          ·
            refine ⟨60576589488633243747666851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161537571969688649993778269 60576589488633243747666851)
            ·
              refine ⟨90864884232949865621500277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60576589488633243747666851 90864884232949865621500277)
              ·
                refine ⟨8518582896839049902015651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90864884232949865621500277 8518582896839049902015651)
                ·
                  refine ⟨12777874345258574853023477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518582896839049902015651 12777874345258574853023477)
                  ·
                    refine ⟨1197925719867991392470951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12777874345258574853023477 1197925719867991392470951)
                    ·
                      rfl

theorem cell23_6998856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_6998856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998856 prefixEnd_6998856 := by exact prefixLift 6998856
  have htrace : WordTrace (prefixWord ++ tailWord_6998856) baseStart_6998856 baseEnd_6998856 := by
    simpa [prefixWord, tailWord_6998856, baseEnd_6998856] using wordTrace_append hprefix tailTrace_6998856
  have hstable : (prefixWord ++ tailWord_6998856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998856).length < 2 ^ (prefixWord ++ tailWord_6998856).sum := by decide
  have hdescent : baseEnd_6998856 < baseStart_6998856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998899 : List Nat := [1, 1, 1, 2, 2, 1, 6, 9]
def baseStart_6998899 : Nat := 118140960795 + 6998899 * 2 ^ 59
def prefixEnd_6998899 : Nat := 4983230072969 + 3 ^ 40 * 6998899 * 2
def baseEnd_6998899 : Nat := 133103675528596944784265

theorem tailTrace_6998899 : CollatzResearch.WordTrace tailWord_6998899 prefixEnd_6998899 133103675528596944784265 := by
  unfold tailWord_6998899
  simp only [CollatzResearch.WordTrace]
  refine ⟨255270817871191714630279751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170180545247461143086853167 255270817871191714630279751)
  ·
    refine ⟨382906226806787571945419627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255270817871191714630279751 382906226806787571945419627)
    ·
      refine ⟨574359340210181357918129441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382906226806787571945419627 574359340210181357918129441)
      ·
        refine ⟨430769505157636018438597081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574359340210181357918129441 430769505157636018438597081)
        ·
          refine ⟨323077128868227013828947811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430769505157636018438597081 323077128868227013828947811)
          ·
            refine ⟨484615693302340520743421717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323077128868227013828947811 484615693302340520743421717)
            ·
              refine ⟨22716360623547211909847893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 484615693302340520743421717 22716360623547211909847893)
              ·
                refine ⟨133103675528596944784265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22716360623547211909847893 133103675528596944784265)
                ·
                  rfl

theorem cell23_6998899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 9].length) (baseStart_6998899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998899 prefixEnd_6998899 := by exact prefixLift 6998899
  have htrace : WordTrace (prefixWord ++ tailWord_6998899) baseStart_6998899 baseEnd_6998899 := by
    simpa [prefixWord, tailWord_6998899, baseEnd_6998899] using wordTrace_append hprefix tailTrace_6998899
  have hstable : (prefixWord ++ tailWord_6998899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998899).length < 2 ^ (prefixWord ++ tailWord_6998899).sum := by decide
  have hdescent : baseEnd_6998899 < baseStart_6998899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998920 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 2, 4]
def baseStart_6998920 : Nat := 118140960795 + 6998920 * 2 ^ 59
def prefixEnd_6998920 : Nat := 4983230072969 + 3 ^ 40 * 6998920 * 2
def baseEnd_6998920 : Nat := 1197936674121953975670853

theorem tailTrace_6998920 : CollatzResearch.WordTrace tailWord_6998920 prefixEnd_6998920 1197936674121953975670853 := by
  unfold tailWord_6998920
  simp only [CollatzResearch.WordTrace]
  refine ⟨127635791902057817608397107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170181055869410423477862809 127635791902057817608397107)
  ·
    refine ⟨191453687853086726412595661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127635791902057817608397107 191453687853086726412595661)
    ·
      refine ⟨71795132944907522404723373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191453687853086726412595661 71795132944907522404723373)
      ·
        refine ⟨26923174854340320901771265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71795132944907522404723373 26923174854340320901771265)
        ·
          refine ⟨20192381140755240676328449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26923174854340320901771265 20192381140755240676328449)
          ·
            refine ⟨15144285855566430507246337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20192381140755240676328449 15144285855566430507246337)
            ·
              refine ⟨11358214391674822880434753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15144285855566430507246337 11358214391674822880434753)
              ·
                refine ⟨8518660793756117160326065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11358214391674822880434753 8518660793756117160326065)
                ·
                  refine ⟨6388995595317087870244549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8518660793756117160326065 6388995595317087870244549)
                  ·
                    refine ⟨1197936674121953975670853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6388995595317087870244549 1197936674121953975670853)
                    ·
                      rfl

theorem cell23_6998920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_6998920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998920 prefixEnd_6998920 := by exact prefixLift 6998920
  have htrace : WordTrace (prefixWord ++ tailWord_6998920) baseStart_6998920 baseEnd_6998920 := by
    simpa [prefixWord, tailWord_6998920, baseEnd_6998920] using wordTrace_append hprefix tailTrace_6998920
  have hstable : (prefixWord ++ tailWord_6998920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998920).length < 2 ^ (prefixWord ++ tailWord_6998920).sum := by decide
  have hdescent : baseEnd_6998920 < baseStart_6998920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998940 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6998940 : Nat := 118140960795 + 6998940 * 2 ^ 59
def prefixEnd_6998940 : Nat := 4983230072969 + 3 ^ 40 * 6998940 * 2
def baseEnd_6998940 : Nat := 3593820291978951848762467

theorem tailTrace_6998940 : CollatzResearch.WordTrace tailWord_6998940 prefixEnd_6998940 3593820291978951848762467 := by
  unfold tailWord_6998940
  simp only [CollatzResearch.WordTrace]
  refine ⟨127636156632021589316261137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170181542176028785755014849 127636156632021589316261137)
  ·
    refine ⟨95727117474016191987195853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127636156632021589316261137 95727117474016191987195853)
    ·
      refine ⟨35897669052756071995198445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95727117474016191987195853 35897669052756071995198445)
      ·
        refine ⟨13461625894783526998199417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35897669052756071995198445 13461625894783526998199417)
        ·
          refine ⟨10096219421087645248649563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13461625894783526998199417 10096219421087645248649563)
          ·
            refine ⟨15144329131631467872974345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10096219421087645248649563 15144329131631467872974345)
            ·
              refine ⟨11358246848723600904730759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15144329131631467872974345 11358246848723600904730759)
              ·
                refine ⟨17037370273085401357096139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11358246848723600904730759 17037370273085401357096139)
                ·
                  refine ⟨25556055409628102035644209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17037370273085401357096139 25556055409628102035644209)
                  ·
                    refine ⟨19167041557221076526733157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25556055409628102035644209 19167041557221076526733157)
                    ·
                      refine ⟨3593820291978951848762467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19167041557221076526733157 3593820291978951848762467)
                      ·
                        rfl

theorem cell23_6998940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6998940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998940 prefixEnd_6998940 := by exact prefixLift 6998940
  have htrace : WordTrace (prefixWord ++ tailWord_6998940) baseStart_6998940 baseEnd_6998940 := by
    simpa [prefixWord, tailWord_6998940, baseEnd_6998940] using wordTrace_append hprefix tailTrace_6998940
  have hstable : (prefixWord ++ tailWord_6998940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998940).length < 2 ^ (prefixWord ++ tailWord_6998940).sum := by decide
  have hdescent : baseEnd_6998940 < baseStart_6998940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998943 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_6998943 : Nat := 118140960795 + 6998943 * 2 ^ 59
def prefixEnd_6998943 : Nat := 4983230072969 + 3 ^ 40 * 6998943 * 2
def baseEnd_6998943 : Nat := 3593821832420915337024953

theorem tailTrace_6998943 : CollatzResearch.WordTrace tailWord_6998943 prefixEnd_6998943 3593821832420915337024953 := by
  unfold tailWord_6998943
  simp only [CollatzResearch.WordTrace]
  refine ⟨255272422683032310144881483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170181615122021540096587655 255272422683032310144881483)
  ·
    refine ⟨382908634024548465217322225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255272422683032310144881483 382908634024548465217322225)
    ·
      refine ⟨287181475518411348912991669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382908634024548465217322225 287181475518411348912991669)
      ·
        refine ⟨26923263329851063960592969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287181475518411348912991669 26923263329851063960592969)
        ·
          refine ⟨20192447497388297970444727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26923263329851063960592969 20192447497388297970444727)
          ·
            refine ⟨30288671246082446955667091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20192447497388297970444727 30288671246082446955667091)
            ·
              refine ⟨45433006869123670433500637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30288671246082446955667091 45433006869123670433500637)
              ·
                refine ⟨17037377575921376412562739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45433006869123670433500637 17037377575921376412562739)
                ·
                  refine ⟨25556066363882064618844109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17037377575921376412562739 25556066363882064618844109)
                  ·
                    refine ⟨9583524886455774232066541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25556066363882064618844109 9583524886455774232066541)
                    ·
                      refine ⟨3593821832420915337024953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583524886455774232066541 3593821832420915337024953)
                      ·
                        rfl

theorem cell23_6998943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_6998943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998943 prefixEnd_6998943 := by exact prefixLift 6998943
  have htrace : WordTrace (prefixWord ++ tailWord_6998943) baseStart_6998943 baseEnd_6998943 := by
    simpa [prefixWord, tailWord_6998943, baseEnd_6998943] using wordTrace_append hprefix tailTrace_6998943
  have hstable : (prefixWord ++ tailWord_6998943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998943).length < 2 ^ (prefixWord ++ tailWord_6998943).sum := by decide
  have hdescent : baseEnd_6998943 < baseStart_6998943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998953 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 3, 3, 2]
def baseStart_6998953 : Nat := 118140960795 + 6998953 * 2 ^ 59
def prefixEnd_6998953 : Nat := 4983230072969 + 3 ^ 40 * 6998953 * 2
def baseEnd_6998953 : Nat := 3593826967227460297899907

theorem tailTrace_6998953 : CollatzResearch.WordTrace tailWord_6998953 prefixEnd_6998953 3593826967227460297899907 := by
  unfold tailWord_6998953
  simp only [CollatzResearch.WordTrace]
  refine ⟨255272787412996081852745513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170181858275330721235163675 255272787412996081852745513)
  ·
    refine ⟨191454590559747061389559135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255272787412996081852745513 191454590559747061389559135)
    ·
      refine ⟨287181885839620592084338703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191454590559747061389559135 287181885839620592084338703)
      ·
        refine ⟨430772828759430888126508055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287181885839620592084338703 430772828759430888126508055)
        ·
          refine ⟨646159243139146332189762083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430772828759430888126508055 646159243139146332189762083)
          ·
            refine ⟨969238864708719498284643125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646159243139146332189762083 969238864708719498284643125)
            ·
              refine ⟨90866143566442452964185293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 969238864708719498284643125 90866143566442452964185293)
              ·
                refine ⟨34074803837415919861569485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90866143566442452964185293 34074803837415919861569485)
                ·
                  refine ⟨12778051439030969948088557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34074803837415919861569485 12778051439030969948088557)
                  ·
                    refine ⟨4791769289636613730533209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12778051439030969948088557 4791769289636613730533209)
                    ·
                      refine ⟨3593826967227460297899907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791769289636613730533209 3593826967227460297899907)
                      ·
                        rfl

theorem cell23_6998953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 3, 2].length) (baseStart_6998953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998953 prefixEnd_6998953 := by exact prefixLift 6998953
  have htrace : WordTrace (prefixWord ++ tailWord_6998953) baseStart_6998953 baseEnd_6998953 := by
    simpa [prefixWord, tailWord_6998953, baseEnd_6998953] using wordTrace_append hprefix tailTrace_6998953
  have hstable : (prefixWord ++ tailWord_6998953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998953).length < 2 ^ (prefixWord ++ tailWord_6998953).sum := by decide
  have hdescent : baseEnd_6998953 < baseStart_6998953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998964 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6998964 : Nat := 118140960795 + 6998964 * 2 ^ 59
def prefixEnd_6998964 : Nat := 4983230072969 + 3 ^ 40 * 6998964 * 2
def baseEnd_6998964 : Nat := 3593832615514659754862357

theorem tailTrace_6998964 : CollatzResearch.WordTrace tailWord_6998964 prefixEnd_6998964 3593832615514659754862357 := by
  unfold tailWord_6998964
  simp only [CollatzResearch.WordTrace]
  refine ⟨127636594307978115365697973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170182125743970820487597297 127636594307978115365697973)
  ·
    refine ⟨11965930716372948315534185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127636594307978115365697973 11965930716372948315534185)
    ·
      refine ⟨8974448037279711236650639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11965930716372948315534185 8974448037279711236650639)
      ·
        refine ⟨13461672055919566854975959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8974448037279711236650639 13461672055919566854975959)
        ·
          refine ⟨20192508083879350282463939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13461672055919566854975959 20192508083879350282463939)
          ·
            refine ⟨30288762125819025423695909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20192508083879350282463939 30288762125819025423695909)
            ·
              refine ⟨5679142898591067266942983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30288762125819025423695909 5679142898591067266942983)
              ·
                refine ⟨8518714347886600900414475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679142898591067266942983 8518714347886600900414475)
                ·
                  refine ⟨12778071521829901350621713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518714347886600900414475 12778071521829901350621713)
                  ·
                    refine ⟨9583553641372426012966285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12778071521829901350621713 9583553641372426012966285)
                    ·
                      refine ⟨3593832615514659754862357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583553641372426012966285 3593832615514659754862357)
                      ·
                        rfl

theorem cell23_6998964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6998964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998964 prefixEnd_6998964 := by exact prefixLift 6998964
  have htrace : WordTrace (prefixWord ++ tailWord_6998964) baseStart_6998964 baseEnd_6998964 := by
    simpa [prefixWord, tailWord_6998964, baseEnd_6998964] using wordTrace_append hprefix tailTrace_6998964
  have hstable : (prefixWord ++ tailWord_6998964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998964).length < 2 ^ (prefixWord ++ tailWord_6998964).sum := by decide
  have hdescent : baseEnd_6998964 < baseStart_6998964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998970 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2]
def baseStart_6998970 : Nat := 118140960795 + 6998970 * 2 ^ 59
def prefixEnd_6998970 : Nat := 4983230072969 + 3 ^ 40 * 6998970 * 2
def baseEnd_6998970 : Nat := 3593835696398586731387329

theorem tailTrace_6998970 : CollatzResearch.WordTrace tailWord_6998970 prefixEnd_6998970 3593835696398586731387329 := by
  unfold tailWord_6998970
  simp only [CollatzResearch.WordTrace]
  refine ⟨63818351863483623439028591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170182271635956329170742909 63818351863483623439028591)
  ·
    refine ⟨95727527795225435158542887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63818351863483623439028591 95727527795225435158542887)
    ·
      refine ⟨143591291692838152737814331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95727527795225435158542887 143591291692838152737814331)
      ·
        refine ⟨215386937539257229106721497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143591291692838152737814331 215386937539257229106721497)
        ·
          refine ⟨161540203154442921830041123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215386937539257229106721497 161540203154442921830041123)
          ·
            refine ⟨242310304731664382745061685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161540203154442921830041123 242310304731664382745061685)
            ·
              refine ⟨22716591068593535882349533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242310304731664382745061685 22716591068593535882349533)
              ·
                refine ⟨8518721650722575955881075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22716591068593535882349533 8518721650722575955881075)
                ·
                  refine ⟨12778082476083863933821613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518721650722575955881075 12778082476083863933821613)
                  ·
                    refine ⟨4791780928531448975183105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12778082476083863933821613 4791780928531448975183105)
                    ·
                      refine ⟨3593835696398586731387329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791780928531448975183105 3593835696398586731387329)
                      ·
                        rfl

theorem cell23_6998970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_6998970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998970 prefixEnd_6998970 := by exact prefixLift 6998970
  have htrace : WordTrace (prefixWord ++ tailWord_6998970) baseStart_6998970 baseEnd_6998970 := by
    simpa [prefixWord, tailWord_6998970, baseEnd_6998970] using wordTrace_append hprefix tailTrace_6998970
  have hstable : (prefixWord ++ tailWord_6998970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998970).length < 2 ^ (prefixWord ++ tailWord_6998970).sum := by decide
  have hdescent : baseEnd_6998970 < baseStart_6998970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998976 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_6998976 : Nat := 118140960795 + 6998976 * 2 ^ 59
def prefixEnd_6998976 : Nat := 4983230072969 + 3 ^ 40 * 6998976 * 2
def baseEnd_6998976 : Nat := 1197946259094171235970767

theorem tailTrace_6998976 : CollatzResearch.WordTrace tailWord_6998976 prefixEnd_6998976 1197946259094171235970767 := by
  unfold tailWord_6998976
  simp only [CollatzResearch.WordTrace]
  refine ⟨127636813145956378390416391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170182417527941837853888521 127636813145956378390416391)
  ·
    refine ⟨191455219718934567585624587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127636813145956378390416391 191455219718934567585624587)
    ·
      refine ⟨287182829578401851378436881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191455219718934567585624587 287182829578401851378436881)
      ·
        refine ⟨215387122183801388533827661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287182829578401851378436881 215387122183801388533827661)
        ·
          refine ⟨80770170818925520700185373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215387122183801388533827661 80770170818925520700185373)
          ·
            refine ⟨30288814057097070262569515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80770170818925520700185373 30288814057097070262569515)
            ·
              refine ⟨45433221085645605393854273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30288814057097070262569515 45433221085645605393854273)
              ·
                refine ⟨34074915814234204045390705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45433221085645605393854273 34074915814234204045390705)
                ·
                  refine ⟨25556186860675653034043029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34074915814234204045390705 25556186860675653034043029)
                  ·
                    refine ⟨1197946259094171235970767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25556186860675653034043029 1197946259094171235970767)
                    ·
                      rfl

theorem cell23_6998976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_6998976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998976 prefixEnd_6998976 := by exact prefixLift 6998976
  have htrace : WordTrace (prefixWord ++ tailWord_6998976) baseStart_6998976 baseEnd_6998976 := by
    simpa [prefixWord, tailWord_6998976, baseEnd_6998976] using wordTrace_append hprefix tailTrace_6998976
  have hstable : (prefixWord ++ tailWord_6998976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998976).length < 2 ^ (prefixWord ++ tailWord_6998976).sum := by decide
  have hdescent : baseEnd_6998976 < baseStart_6998976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998983 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_6998983 : Nat := 118140960795 + 6998983 * 2 ^ 59
def prefixEnd_6998983 : Nat := 4983230072969 + 3 ^ 40 * 6998983 * 2
def baseEnd_6998983 : Nat := 3593842371647095180524769

theorem tailTrace_6998983 : CollatzResearch.WordTrace tailWord_6998983 prefixEnd_6998983 3593842371647095180524769 := by
  unfold tailWord_6998983
  simp only [CollatzResearch.WordTrace]
  refine ⟨255273881602887396976337603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170182587735258264650891735 255273881602887396976337603)
  ·
    refine ⟨382910822404331095464506405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255273881602887396976337603 382910822404331095464506405)
    ·
      refine ⟨71795779200812080399594951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382910822404331095464506405 71795779200812080399594951)
      ·
        refine ⟨107693668801218120599392427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71795779200812080399594951 107693668801218120599392427)
        ·
          refine ⟨161540503201827180899088641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107693668801218120599392427 161540503201827180899088641)
          ·
            refine ⟨121155377401370385674316481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161540503201827180899088641 121155377401370385674316481)
            ·
              refine ⟨90866533051027789255737361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121155377401370385674316481 90866533051027789255737361)
              ·
                refine ⟨68149899788270841941803021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90866533051027789255737361 68149899788270841941803021)
                ·
                  refine ⟨25556212420601565728176133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68149899788270841941803021 25556212420601565728176133)
                  ·
                    refine ⟨4791789828862793574033025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25556212420601565728176133 4791789828862793574033025)
                    ·
                      refine ⟨3593842371647095180524769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791789828862793574033025 3593842371647095180524769)
                      ·
                        rfl

theorem cell23_6998983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_6998983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998983 prefixEnd_6998983 := by exact prefixLift 6998983
  have htrace : WordTrace (prefixWord ++ tailWord_6998983) baseStart_6998983 baseEnd_6998983 := by
    simpa [prefixWord, tailWord_6998983, baseEnd_6998983] using wordTrace_append hprefix tailTrace_6998983
  have hstable : (prefixWord ++ tailWord_6998983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998983).length < 2 ^ (prefixWord ++ tailWord_6998983).sum := by decide
  have hdescent : baseEnd_6998983 < baseStart_6998983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998986 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_6998986 : Nat := 118140960795 + 6998986 * 2 ^ 59
def prefixEnd_6998986 : Nat := 4983230072969 + 3 ^ 40 * 6998986 * 2
def baseEnd_6998986 : Nat := 3593843912089058668787255

theorem tailTrace_6998986 : CollatzResearch.WordTrace tailWord_6998986 prefixEnd_6998986 3593843912089058668787255 := by
  unfold tailWord_6998986
  simp only [CollatzResearch.WordTrace]
  refine ⟨63818497755469132122174203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170182660681251018992464541 63818497755469132122174203)
  ·
    refine ⟨95727746633203698183261305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63818497755469132122174203 95727746633203698183261305)
    ·
      refine ⟨71795809974902773637445979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95727746633203698183261305 71795809974902773637445979)
      ·
        refine ⟨107693714962354160456168969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71795809974902773637445979 107693714962354160456168969)
        ·
          refine ⟨80770286221765620342126727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107693714962354160456168969 80770286221765620342126727)
          ·
            refine ⟨121155429332648430513190091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80770286221765620342126727 121155429332648430513190091)
            ·
              refine ⟨181733143998972645769785137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121155429332648430513190091 181733143998972645769785137)
              ·
                refine ⟨136299857999229484327338853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181733143998972645769785137 136299857999229484327338853)
                ·
                  refine ⟨25556223374855528311376035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136299857999229484327338853 25556223374855528311376035)
                  ·
                    refine ⟨38334335062283292467064053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25556223374855528311376035 38334335062283292467064053)
                    ·
                      refine ⟨3593843912089058668787255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38334335062283292467064053 3593843912089058668787255)
                      ·
                        rfl

theorem cell23_6998986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_6998986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998986 prefixEnd_6998986 := by exact prefixLift 6998986
  have htrace : WordTrace (prefixWord ++ tailWord_6998986) baseStart_6998986 baseEnd_6998986 := by
    simpa [prefixWord, tailWord_6998986, baseEnd_6998986] using wordTrace_append hprefix tailTrace_6998986
  have hstable : (prefixWord ++ tailWord_6998986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998986).length < 2 ^ (prefixWord ++ tailWord_6998986).sum := by decide
  have hdescent : baseEnd_6998986 < baseStart_6998986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6998994 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_6998994 : Nat := 118140960795 + 6998994 * 2 ^ 59
def prefixEnd_6998994 : Nat := 4983230072969 + 3 ^ 40 * 6998994 * 2
def baseEnd_6998994 : Nat := 3593848019934294637487219

theorem tailTrace_6998994 : CollatzResearch.WordTrace tailWord_6998994 prefixEnd_6998994 3593848019934294637487219 := by
  unfold tailWord_6998994
  simp only [CollatzResearch.WordTrace]
  refine ⟨63818570701461886463747009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170182855203898363903325357 63818570701461886463747009)
  ·
    refine ⟨47863928026096414847810257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63818570701461886463747009 47863928026096414847810257)
    ·
      refine ⟨35897946019572311135857693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47863928026096414847810257 35897946019572311135857693)
      ·
        refine ⟨13461729757339616675946635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35897946019572311135857693 13461729757339616675946635)
        ·
          refine ⟨20192594636009425013919953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13461729757339616675946635 20192594636009425013919953)
          ·
            refine ⟨15144445977007068760439965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20192594636009425013919953 15144445977007068760439965)
            ·
              refine ⟨5679167241377650785164987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15144445977007068760439965 5679167241377650785164987)
              ·
                refine ⟨8518750862066476177747481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679167241377650785164987 8518750862066476177747481)
                ·
                  refine ⟨6389063146549857133310611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8518750862066476177747481 6389063146549857133310611)
                  ·
                    refine ⟨9583594719824785699965917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6389063146549857133310611 9583594719824785699965917)
                    ·
                      refine ⟨3593848019934294637487219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583594719824785699965917 3593848019934294637487219)
                      ·
                        rfl

theorem cell23_6998994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_6998994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6998994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6998994 prefixEnd_6998994 := by exact prefixLift 6998994
  have htrace : WordTrace (prefixWord ++ tailWord_6998994) baseStart_6998994 baseEnd_6998994 := by
    simpa [prefixWord, tailWord_6998994, baseEnd_6998994] using wordTrace_append hprefix tailTrace_6998994
  have hstable : (prefixWord ++ tailWord_6998994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6998994).length < 2 ^ (prefixWord ++ tailWord_6998994).sum := by decide
  have hdescent : baseEnd_6998994 < baseStart_6998994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6998994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999000 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 1, 4, 2]
def baseStart_6999000 : Nat := 118140960795 + 6999000 * 2 ^ 59
def prefixEnd_6999000 : Nat := 4983230072969 + 3 ^ 40 * 6999000 * 2
def baseEnd_6999000 : Nat := 3593851100818221614012191

theorem tailTrace_6999000 : CollatzResearch.WordTrace tailWord_6999000 prefixEnd_6999000 3593851100818221614012191 := by
  unfold tailWord_6999000
  simp only [CollatzResearch.WordTrace]
  refine ⟨127637250821912904439853227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170183001095883872586470969 127637250821912904439853227)
  ·
    refine ⟨191455876232869356659779841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127637250821912904439853227 191455876232869356659779841)
    ·
      refine ⟨143591907174652017494834881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191455876232869356659779841 143591907174652017494834881)
      ·
        refine ⟨107693930380989013121126161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143591907174652017494834881 107693930380989013121126161)
        ·
          refine ⟨80770447785741759840844621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107693930380989013121126161 80770447785741759840844621)
          ·
            refine ⟨30288917919653159940316733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80770447785741759840844621 30288917919653159940316733)
            ·
              refine ⟨11358344219869934977618775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30288917919653159940316733 11358344219869934977618775)
              ·
                refine ⟨17037516329804902466428163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11358344219869934977618775 17037516329804902466428163)
                ·
                  refine ⟨25556274494707353699642245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17037516329804902466428163 25556274494707353699642245)
                  ·
                    refine ⟨4791801467757628818682921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25556274494707353699642245 4791801467757628818682921)
                    ·
                      refine ⟨3593851100818221614012191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791801467757628818682921 3593851100818221614012191)
                      ·
                        rfl

theorem cell23_6999000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_6999000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999000 prefixEnd_6999000 := by exact prefixLift 6999000
  have htrace : WordTrace (prefixWord ++ tailWord_6999000) baseStart_6999000 baseEnd_6999000 := by
    simpa [prefixWord, tailWord_6999000, baseEnd_6999000] using wordTrace_append hprefix tailTrace_6999000
  have hstable : (prefixWord ++ tailWord_6999000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999000).length < 2 ^ (prefixWord ++ tailWord_6999000).sum := by decide
  have hdescent : baseEnd_6999000 < baseStart_6999000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999090 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_6999090 : Nat := 118140960795 + 6999090 * 2 ^ 59
def prefixEnd_6999090 : Nat := 4983230072969 + 3 ^ 40 * 6999090 * 2
def baseEnd_6999090 : Nat := 3593897314077126261886777

theorem tailTrace_6999090 : CollatzResearch.WordTrace tailWord_6999090 prefixEnd_6999090 3593897314077126261886777 := by
  unfold tailWord_6999090
  simp only [CollatzResearch.WordTrace]
  refine ⟨63819446053374938562620681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170185189475666502833655149 63819446053374938562620681)
  ·
    refine ⟨47864584540031203921965511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63819446053374938562620681 47864584540031203921965511)
    ·
      refine ⟨71796876810046805882948267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47864584540031203921965511 71796876810046805882948267)
      ·
        refine ⟨107695315215070208824422401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71796876810046805882948267 107695315215070208824422401)
        ·
          refine ⟨80771486411302656618316801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107695315215070208824422401 80771486411302656618316801)
          ·
            refine ⟨60578614808476992463737601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80771486411302656618316801 60578614808476992463737601)
            ·
              refine ⟨45433961106357744347803201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60578614808476992463737601 45433961106357744347803201)
              ·
                refine ⟨34075470829768308260852401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45433961106357744347803201 34075470829768308260852401)
                ·
                  refine ⟨25556603122326231195639301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34075470829768308260852401 25556603122326231195639301)
                  ·
                    refine ⟨4791863085436168349182369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25556603122326231195639301 4791863085436168349182369)
                    ·
                      refine ⟨3593897314077126261886777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4791863085436168349182369 3593897314077126261886777)
                      ·
                        rfl

theorem cell23_6999090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_6999090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999090 prefixEnd_6999090 := by exact prefixLift 6999090
  have htrace : WordTrace (prefixWord ++ tailWord_6999090) baseStart_6999090 baseEnd_6999090 := by
    simpa [prefixWord, tailWord_6999090, baseEnd_6999090] using wordTrace_append hprefix tailTrace_6999090
  have hstable : (prefixWord ++ tailWord_6999090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999090).length < 2 ^ (prefixWord ++ tailWord_6999090).sum := by decide
  have hdescent : baseEnd_6999090 < baseStart_6999090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999093 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_6999093 : Nat := 118140960795 + 6999093 * 2 ^ 59
def prefixEnd_6999093 : Nat := 4983230072969 + 3 ^ 40 * 6999093 * 2
def baseEnd_6999093 : Nat := 3593898854519089750149263

theorem tailTrace_6999093 : CollatzResearch.WordTrace tailWord_6999093 prefixEnd_6999093 3593898854519089750149263 := by
  unfold tailWord_6999093
  simp only [CollatzResearch.WordTrace]
  refine ⟨255277893632488885762841933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170185262421659257175227955 255277893632488885762841933)
  ·
    refine ⟨95729210112183332161065725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255277893632488885762841933 95729210112183332161065725)
    ·
      refine ⟨35898453792068749560399647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95729210112183332161065725 35898453792068749560399647)
      ·
        refine ⟨53847680688103124340599471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35898453792068749560399647 53847680688103124340599471)
        ·
          refine ⟨80771521032154686510899207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53847680688103124340599471 80771521032154686510899207)
          ·
            refine ⟨121157281548232029766348811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80771521032154686510899207 121157281548232029766348811)
            ·
              refine ⟨181735922322348044649523217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121157281548232029766348811 181735922322348044649523217)
              ·
                refine ⟨136301941741761033487142413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181735922322348044649523217 136301941741761033487142413)
                ·
                  refine ⟨51113228153160387557678405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136301941741761033487142413 51113228153160387557678405)
                  ·
                    refine ⟨9583730278717572667064701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51113228153160387557678405 9583730278717572667064701)
                    ·
                      refine ⟨3593898854519089750149263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583730278717572667064701 3593898854519089750149263)
                      ·
                        rfl

theorem cell23_6999093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_6999093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999093 prefixEnd_6999093 := by exact prefixLift 6999093
  have htrace : WordTrace (prefixWord ++ tailWord_6999093) baseStart_6999093 baseEnd_6999093 := by
    simpa [prefixWord, tailWord_6999093, baseEnd_6999093] using wordTrace_append hprefix tailTrace_6999093
  have hstable : (prefixWord ++ tailWord_6999093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999093).length < 2 ^ (prefixWord ++ tailWord_6999093).sum := by decide
  have hdescent : baseEnd_6999093 < baseStart_6999093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999117 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6999117 : Nat := 118140960795 + 6999117 * 2 ^ 59
def prefixEnd_6999117 : Nat := 4983230072969 + 3 ^ 40 * 6999117 * 2
def baseEnd_6999117 : Nat := 1197970392684932552083051

theorem tailTrace_6999117 : CollatzResearch.WordTrace tailWord_6999117 prefixEnd_6999117 1197970392684932552083051 := by
  unfold tailWord_6999117
  simp only [CollatzResearch.WordTrace]
  refine ⟨255278768984401937861715605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170185845989601291907810403 255278768984401937861715605)
  ·
    refine ⟨11966192296143840837267919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255278768984401937861715605 11966192296143840837267919)
    ·
      refine ⟨17949288444215761255901879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11966192296143840837267919 17949288444215761255901879)
      ·
        refine ⟨26923932666323641883852819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17949288444215761255901879 26923932666323641883852819)
        ·
          refine ⟨40385898999485462825779229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26923932666323641883852819 40385898999485462825779229)
          ·
            refine ⟨15144712124807048559667211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40385898999485462825779229 15144712124807048559667211)
            ·
              refine ⟨22717068187210572839500817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15144712124807048559667211 22717068187210572839500817)
              ·
                refine ⟨17037801140407929629625613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22717068187210572839500817 17037801140407929629625613)
                ·
                  refine ⟨6389175427652973611109605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17037801140407929629625613 6389175427652973611109605)
                  ·
                    refine ⟨1197970392684932552083051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389175427652973611109605 1197970392684932552083051)
                    ·
                      rfl

theorem cell23_6999117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6999117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999117 prefixEnd_6999117 := by exact prefixLift 6999117
  have htrace : WordTrace (prefixWord ++ tailWord_6999117) baseStart_6999117 baseEnd_6999117 := by
    simpa [prefixWord, tailWord_6999117, baseEnd_6999117] using wordTrace_append hprefix tailTrace_6999117
  have hstable : (prefixWord ++ tailWord_6999117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999117).length < 2 ^ (prefixWord ++ tailWord_6999117).sum := by decide
  have hdescent : baseEnd_6999117 < baseStart_6999117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999140 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_6999140 : Nat := 118140960795 + 6999140 * 2 ^ 59
def prefixEnd_6999140 : Nat := 4983230072969 + 3 ^ 40 * 6999140 * 2
def baseEnd_6999140 : Nat := 3593922988109851066261547

theorem tailTrace_6999140 : CollatzResearch.WordTrace tailWord_6999140 prefixEnd_6999140 3593922988109851066261547 := by
  unfold tailWord_6999140
  simp only [CollatzResearch.WordTrace]
  refine ⟨127639803931659306394901437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170186405242212408526535249 127639803931659306394901437)
  ·
    refine ⟨47864926474372239898088039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127639803931659306394901437 47864926474372239898088039)
    ·
      refine ⟨71797389711558359847132059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47864926474372239898088039 71797389711558359847132059)
      ·
        refine ⟨107696084567337539770698089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71797389711558359847132059 107696084567337539770698089)
        ·
          refine ⟨80772063425503154828023567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107696084567337539770698089 80772063425503154828023567)
          ·
            refine ⟨121158095138254732242035351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80772063425503154828023567 121158095138254732242035351)
            ·
              refine ⟨181737142707382098363053027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121158095138254732242035351 181737142707382098363053027)
              ·
                refine ⟨272605714061073147544579541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181737142707382098363053027 272605714061073147544579541)
                ·
                  refine ⟨6389196423306401895576083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 272605714061073147544579541 6389196423306401895576083)
                  ·
                    refine ⟨9583794634959602843364125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6389196423306401895576083 9583794634959602843364125)
                    ·
                      refine ⟨3593922988109851066261547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583794634959602843364125 3593922988109851066261547)
                      ·
                        rfl

theorem cell23_6999140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_6999140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999140 prefixEnd_6999140 := by exact prefixLift 6999140
  have htrace : WordTrace (prefixWord ++ tailWord_6999140) baseStart_6999140 baseEnd_6999140 := by
    simpa [prefixWord, tailWord_6999140, baseEnd_6999140] using wordTrace_append hprefix tailTrace_6999140
  have hstable : (prefixWord ++ tailWord_6999140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999140).length < 2 ^ (prefixWord ++ tailWord_6999140).sum := by decide
  have hdescent : baseEnd_6999140 < baseStart_6999140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999163 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 4]
def baseStart_6999163 : Nat := 118140960795 + 6999163 * 2 ^ 59
def prefixEnd_6999163 : Nat := 4983230072969 + 3 ^ 40 * 6999163 * 2
def baseEnd_6999163 : Nat := 3593934798164904476273941

theorem tailTrace_6999163 : CollatzResearch.WordTrace tailWord_6999163 prefixEnd_6999163 3593934798164904476273941 := by
  unfold tailWord_6999163
  simp only [CollatzResearch.WordTrace]
  refine ⟨255280446742235287717890143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170186964494823525145260095 255280446742235287717890143)
  ·
    refine ⟨382920670113352931576835215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255280446742235287717890143 382920670113352931576835215)
    ·
      refine ⟨574381005170029397365252823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382920670113352931576835215 574381005170029397365252823)
      ·
        refine ⟨861571507755044096047879235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574381005170029397365252823 861571507755044096047879235)
        ·
          refine ⟨1292357261632566144071818853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861571507755044096047879235 1292357261632566144071818853)
          ·
            refine ⟨242316986556106152013466035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1292357261632566144071818853 242316986556106152013466035)
            ·
              refine ⟨363475479834159228020199053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242316986556106152013466035 363475479834159228020199053)
              ·
                refine ⟨136303304937809710507574645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363475479834159228020199053 136303304937809710507574645)
                ·
                  refine ⟨12778434837919660360085123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136303304937809710507574645 12778434837919660360085123)
                  ·
                    refine ⟨19167652256879490540127685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12778434837919660360085123 19167652256879490540127685)
                    ·
                      refine ⟨3593934798164904476273941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19167652256879490540127685 3593934798164904476273941)
                      ·
                        rfl

theorem cell23_6999163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 4].length) (baseStart_6999163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999163 prefixEnd_6999163 := by exact prefixLift 6999163
  have htrace : WordTrace (prefixWord ++ tailWord_6999163) baseStart_6999163 baseEnd_6999163 := by
    simpa [prefixWord, tailWord_6999163, baseEnd_6999163] using wordTrace_append hprefix tailTrace_6999163
  have hstable : (prefixWord ++ tailWord_6999163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999163).length < 2 ^ (prefixWord ++ tailWord_6999163).sum := by decide
  have hdescent : baseEnd_6999163 < baseStart_6999163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999191 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 1, 1, 3]
def baseStart_6999191 : Nat := 118140960795 + 6999191 * 2 ^ 59
def prefixEnd_6999191 : Nat := 4983230072969 + 3 ^ 40 * 6999191 * 2
def baseEnd_6999191 : Nat := 3593949175623230366723813

theorem tailTrace_6999191 : CollatzResearch.WordTrace tailWord_6999191 prefixEnd_6999191 3593949175623230366723813 := by
  unfold tailWord_6999191
  simp only [CollatzResearch.WordTrace]
  refine ⟨255281467986133848499909427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170187645324089232333272951 255281467986133848499909427)
  ·
    refine ⟨382922201979200772749864141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255281467986133848499909427 382922201979200772749864141)
    ·
      refine ⟨143595825742200289781199053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382922201979200772749864141 143595825742200289781199053)
      ·
        refine ⟨53848434653325108667949645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143595825742200289781199053 53848434653325108667949645)
        ·
          refine ⟨20193162994996915750481117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53848434653325108667949645 20193162994996915750481117)
          ·
            refine ⟨7572436123123843406430419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20193162994996915750481117 7572436123123843406430419)
            ·
              refine ⟨11358654184685765109645629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572436123123843406430419 11358654184685765109645629)
              ·
                refine ⟨4259495319257161916117111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11358654184685765109645629 4259495319257161916117111)
                ·
                  refine ⟨6389242978885742874175667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259495319257161916117111 6389242978885742874175667)
                  ·
                    refine ⟨9583864468328614311263501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6389242978885742874175667 9583864468328614311263501)
                    ·
                      refine ⟨3593949175623230366723813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583864468328614311263501 3593949175623230366723813)
                      ·
                        rfl

theorem cell23_6999191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_6999191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999191 prefixEnd_6999191 := by exact prefixLift 6999191
  have htrace : WordTrace (prefixWord ++ tailWord_6999191) baseStart_6999191 baseEnd_6999191 := by
    simpa [prefixWord, tailWord_6999191, baseEnd_6999191] using wordTrace_append hprefix tailTrace_6999191
  have hstable : (prefixWord ++ tailWord_6999191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999191).length < 2 ^ (prefixWord ++ tailWord_6999191).sum := by decide
  have hdescent : baseEnd_6999191 < baseStart_6999191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999200 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_6999200 : Nat := 118140960795 + 6999200 * 2 ^ 59
def prefixEnd_6999200 : Nat := 4983230072969 + 3 ^ 40 * 6999200 * 2
def baseEnd_6999200 : Nat := 3593953796949120831511271

theorem tailTrace_6999200 : CollatzResearch.WordTrace tailWord_6999200 prefixEnd_6999200 3593953796949120831511271 := by
  unfold tailWord_6999200
  simp only [CollatzResearch.WordTrace]
  refine ⟨127640898121550621518493527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170187864162067495357991369 127640898121550621518493527)
  ·
    refine ⟨191461347182325932277740291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127640898121550621518493527 191461347182325932277740291)
    ·
      refine ⟨287192020773488898416610437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191461347182325932277740291 287192020773488898416610437)
      ·
        refine ⟨53848503895029168453114457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287192020773488898416610437 53848503895029168453114457)
        ·
          refine ⟨40386377921271876339835843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53848503895029168453114457 40386377921271876339835843)
          ·
            refine ⟨60579566881907814509753765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40386377921271876339835843 60579566881907814509753765)
            ·
              refine ⟨11358668790357715220578831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60579566881907814509753765 11358668790357715220578831)
              ·
                refine ⟨17038003185536572830868247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11358668790357715220578831 17038003185536572830868247)
                ·
                  refine ⟨25557004778304859246302371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17038003185536572830868247 25557004778304859246302371)
                  ·
                    refine ⟨38335507167457288869453557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25557004778304859246302371 38335507167457288869453557)
                    ·
                      refine ⟨3593953796949120831511271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38335507167457288869453557 3593953796949120831511271)
                      ·
                        rfl

theorem cell23_6999200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_6999200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999200 prefixEnd_6999200 := by exact prefixLift 6999200
  have htrace : WordTrace (prefixWord ++ tailWord_6999200) baseStart_6999200 baseEnd_6999200 := by
    simpa [prefixWord, tailWord_6999200, baseEnd_6999200] using wordTrace_append hprefix tailTrace_6999200
  have hstable : (prefixWord ++ tailWord_6999200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999200).length < 2 ^ (prefixWord ++ tailWord_6999200).sum := by decide
  have hdescent : baseEnd_6999200 < baseStart_6999200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999207 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6999207 : Nat := 118140960795 + 6999207 * 2 ^ 59
def prefixEnd_6999207 : Nat := 4983230072969 + 3 ^ 40 * 6999207 * 2
def baseEnd_6999207 : Nat := 1197985797104567434707913

theorem tailTrace_6999207 : CollatzResearch.WordTrace tailWord_6999207 prefixEnd_6999207 1197985797104567434707913 := by
  unfold tailWord_6999207
  simp only [CollatzResearch.WordTrace]
  refine ⟨255282051554075883232491875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170188034369383922154994583 255282051554075883232491875)
  ·
    refine ⟨382923077331113824848737813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255282051554075883232491875 382923077331113824848737813)
    ·
      refine ⟨17949519249895960539784585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 382923077331113824848737813 17949519249895960539784585)
      ·
        refine ⟨13462139437421970404838439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17949519249895960539784585 13462139437421970404838439)
        ·
          refine ⟨20193209156132955607257659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13462139437421970404838439 20193209156132955607257659)
          ·
            refine ⟨30289813734199433410886489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20193209156132955607257659 30289813734199433410886489)
            ·
              refine ⟨22717360300649575058164867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30289813734199433410886489 22717360300649575058164867)
              ·
                refine ⟨34076040450974362587247301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22717360300649575058164867 34076040450974362587247301)
                ·
                  refine ⟨6389257584557692985108869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34076040450974362587247301 6389257584557692985108869)
                  ·
                    refine ⟨1197985797104567434707913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389257584557692985108869 1197985797104567434707913)
                    ·
                      rfl

theorem cell23_6999207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6999207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999207 prefixEnd_6999207 := by exact prefixLift 6999207
  have htrace : WordTrace (prefixWord ++ tailWord_6999207) baseStart_6999207 baseEnd_6999207 := by
    simpa [prefixWord, tailWord_6999207, baseEnd_6999207] using wordTrace_append hprefix tailTrace_6999207
  have hstable : (prefixWord ++ tailWord_6999207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999207).length < 2 ^ (prefixWord ++ tailWord_6999207).sum := by decide
  have hdescent : baseEnd_6999207 < baseStart_6999207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999223 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_6999223 : Nat := 118140960795 + 6999223 * 2 ^ 59
def prefixEnd_6999223 : Nat := 4983230072969 + 3 ^ 40 * 6999223 * 2
def baseEnd_6999223 : Nat := 3593965607004174241523665

theorem tailTrace_6999223 : CollatzResearch.WordTrace tailWord_6999223 prefixEnd_6999223 3593965607004174241523665 := by
  unfold tailWord_6999223
  simp only [CollatzResearch.WordTrace]
  refine ⟨255282635122017917965074323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170188423414678611976716215 255282635122017917965074323)
  ·
    refine ⟨382923952683026876947611485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255282635122017917965074323 382923952683026876947611485)
    ·
      refine ⟨143596482256135078855354307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382923952683026876947611485 143596482256135078855354307)
      ·
        refine ⟨215394723384202618283031461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143596482256135078855354307 215394723384202618283031461)
        ·
          refine ⟨40386510634537990928068399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215394723384202618283031461 40386510634537990928068399)
          ·
            refine ⟨60579765951806986392102599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40386510634537990928068399 60579765951806986392102599)
            ·
              refine ⟨90869648927710479588153899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60579765951806986392102599 90869648927710479588153899)
              ·
                refine ⟨136304473391565719382230849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90869648927710479588153899 136304473391565719382230849)
                ·
                  refine ⟨102228355043674289536673137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136304473391565719382230849 102228355043674289536673137)
                  ·
                    refine ⟨76671266282755717152504853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102228355043674289536673137 76671266282755717152504853)
                    ·
                      refine ⟨3593965607004174241523665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76671266282755717152504853 3593965607004174241523665)
                      ·
                        rfl

theorem cell23_6999223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_6999223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999223 prefixEnd_6999223 := by exact prefixLift 6999223
  have htrace : WordTrace (prefixWord ++ tailWord_6999223) baseStart_6999223 baseEnd_6999223 := by
    simpa [prefixWord, tailWord_6999223, baseEnd_6999223] using wordTrace_append hprefix tailTrace_6999223
  have hstable : (prefixWord ++ tailWord_6999223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999223).length < 2 ^ (prefixWord ++ tailWord_6999223).sum := by decide
  have hdescent : baseEnd_6999223 < baseStart_6999223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999243 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_6999243 : Nat := 118140960795 + 6999243 * 2 ^ 59
def prefixEnd_6999243 : Nat := 4983230072969 + 3 ^ 40 * 6999243 * 2
def baseEnd_6999243 : Nat := 3593975876617264163273573

theorem tailTrace_6999243 : CollatzResearch.WordTrace tailWord_6999243 prefixEnd_6999243 3593975876617264163273573 := by
  unfold tailWord_6999243
  simp only [CollatzResearch.WordTrace]
  refine ⟨255283364581945461380802383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170188909721296974253868255 255283364581945461380802383)
  ·
    refine ⟨382925046872918192071203575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255283364581945461380802383 382925046872918192071203575)
    ·
      refine ⟨574387570309377288106805363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382925046872918192071203575 574387570309377288106805363)
      ·
        refine ⟨861581355464065932160208045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574387570309377288106805363 861581355464065932160208045)
        ·
          refine ⟨323093008299024724560078017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 861581355464065932160208045 323093008299024724560078017)
          ·
            refine ⟨242319756224268543420058513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323093008299024724560078017 242319756224268543420058513)
            ·
              refine ⟨181739817168201407565043885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242319756224268543420058513 181739817168201407565043885)
              ·
                refine ⟨68152431438075527836891457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181739817168201407565043885 68152431438075527836891457)
                ·
                  refine ⟨51114323578556645877668593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68152431438075527836891457 51114323578556645877668593)
                  ·
                    refine ⟨38335742683917484408251445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51114323578556645877668593 38335742683917484408251445)
                    ·
                      refine ⟨3593975876617264163273573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38335742683917484408251445 3593975876617264163273573)
                      ·
                        rfl

theorem cell23_6999243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_6999243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999243 prefixEnd_6999243 := by exact prefixLift 6999243
  have htrace : WordTrace (prefixWord ++ tailWord_6999243) baseStart_6999243 baseEnd_6999243 := by
    simpa [prefixWord, tailWord_6999243, baseEnd_6999243] using wordTrace_append hprefix tailTrace_6999243
  have hstable : (prefixWord ++ tailWord_6999243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999243).length < 2 ^ (prefixWord ++ tailWord_6999243).sum := by decide
  have hdescent : baseEnd_6999243 < baseStart_6999243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999264 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 2, 1, 3]
def baseStart_6999264 : Nat := 118140960795 + 6999264 * 2 ^ 59
def prefixEnd_6999264 : Nat := 4983230072969 + 3 ^ 40 * 6999264 * 2
def baseEnd_6999264 : Nat := 3593986659711008581110977

theorem tailTrace_6999264 : CollatzResearch.WordTrace tailWord_6999264 prefixEnd_6999264 3593986659711008581110977 := by
  unfold tailWord_6999264
  simp only [CollatzResearch.WordTrace]
  refine ⟨127642065257434690983658423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170189420343246254644877897 127642065257434690983658423)
  ·
    refine ⟨191463097886152036475487635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127642065257434690983658423 191463097886152036475487635)
    ·
      refine ⟨287194646829228054713231453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191463097886152036475487635 287194646829228054713231453)
      ·
        refine ⟨107697992560960520517461795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287194646829228054713231453 107697992560960520517461795)
        ·
          refine ⟨161546988841440780776192693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107697992560960520517461795 161546988841440780776192693)
          ·
            refine ⟨15145030203885073197768065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161546988841440780776192693 15145030203885073197768065)
            ·
              refine ⟨11358772652913804898326049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15145030203885073197768065 11358772652913804898326049)
              ·
                refine ⟨8519079489685353673744537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11358772652913804898326049 8519079489685353673744537)
                ·
                  refine ⟨6389309617264015255308403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8519079489685353673744537 6389309617264015255308403)
                  ·
                    refine ⟨9583964425896022882962605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6389309617264015255308403 9583964425896022882962605)
                    ·
                      refine ⟨3593986659711008581110977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9583964425896022882962605 3593986659711008581110977)
                      ·
                        rfl

theorem cell23_6999264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_6999264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999264 prefixEnd_6999264 := by exact prefixLift 6999264
  have htrace : WordTrace (prefixWord ++ tailWord_6999264) baseStart_6999264 baseEnd_6999264 := by
    simpa [prefixWord, tailWord_6999264, baseEnd_6999264] using wordTrace_append hprefix tailTrace_6999264
  have hstable : (prefixWord ++ tailWord_6999264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999264).length < 2 ^ (prefixWord ++ tailWord_6999264).sum := by decide
  have hdescent : baseEnd_6999264 < baseStart_6999264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999290 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_6999290 : Nat := 118140960795 + 6999290 * 2 ^ 59
def prefixEnd_6999290 : Nat := 4983230072969 + 3 ^ 40 * 6999290 * 2
def baseEnd_6999290 : Nat := 3594000010208025479385857

theorem tailTrace_6999290 : CollatzResearch.WordTrace tailWord_6999290 prefixEnd_6999290 3594000010208025479385857 := by
  unfold tailWord_6999290
  simp only [CollatzResearch.WordTrace]
  refine ⟨63821269703193797101940831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170190052541850125605175549 63821269703193797101940831)
  ·
    refine ⟨95731904554790695652911247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63821269703193797101940831 95731904554790695652911247)
    ·
      refine ⟨143597856832186043479366871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95731904554790695652911247 143597856832186043479366871)
      ·
        refine ⟨215396785248279065219050307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143597856832186043479366871 215396785248279065219050307)
        ·
          refine ⟨323095177872418597828575461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215396785248279065219050307 323095177872418597828575461)
          ·
            refine ⟨60580345851078487092857899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323095177872418597828575461 60580345851078487092857899)
            ·
              refine ⟨90870518776617730639286849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60580345851078487092857899 90870518776617730639286849)
              ·
                refine ⟨68152889082463297979465137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90870518776617730639286849 68152889082463297979465137)
                ·
                  refine ⟨51114666811847473484598853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68152889082463297979465137 51114666811847473484598853)
                  ·
                    refine ⟨9584000027221401278362285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51114666811847473484598853 9584000027221401278362285)
                    ·
                      refine ⟨3594000010208025479385857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9584000027221401278362285 3594000010208025479385857)
                      ·
                        rfl

theorem cell23_6999290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_6999290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999290 prefixEnd_6999290 := by exact prefixLift 6999290
  have htrace : WordTrace (prefixWord ++ tailWord_6999290) baseStart_6999290 baseEnd_6999290 := by
    simpa [prefixWord, tailWord_6999290, baseEnd_6999290] using wordTrace_append hprefix tailTrace_6999290
  have hstable : (prefixWord ++ tailWord_6999290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999290).length < 2 ^ (prefixWord ++ tailWord_6999290).sum := by decide
  have hdescent : baseEnd_6999290 < baseStart_6999290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999327 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 7]
def baseStart_6999327 : Nat := 118140960795 + 6999327 * 2 ^ 59
def prefixEnd_6999327 : Nat := 4983230072969 + 3 ^ 40 * 6999327 * 2
def baseEnd_6999327 : Nat := 399335445443582426069243

theorem tailTrace_6999327 : CollatzResearch.WordTrace tailWord_6999327 prefixEnd_6999327 399335445443582426069243 := by
  unfold tailWord_6999327
  simp only [CollatzResearch.WordTrace]
  refine ⟨255286428313641143726860235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170190952209094095817906823 255286428313641143726860235)
  ·
    refine ⟨382929642470461715590290353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255286428313641143726860235 382929642470461715590290353)
    ·
      refine ⟨287197231852846286692717765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382929642470461715590290353 287197231852846286692717765)
      ·
        refine ⟨53849480972408678754884581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287197231852846286692717765 53849480972408678754884581)
        ·
          refine ⟨10096777682326627266540859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53849480972408678754884581 10096777682326627266540859)
          ·
            refine ⟨15145166523489940899811289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10096777682326627266540859 15145166523489940899811289)
            ·
              refine ⟨11358874892617455674858467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15145166523489940899811289 11358874892617455674858467)
              ·
                refine ⟨17038312338926183512287701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11358874892617455674858467 17038312338926183512287701)
                ·
                  refine ⟨399335445443582426069243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17038312338926183512287701 399335445443582426069243)
                  ·
                    rfl

theorem cell23_6999327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 7].length) (baseStart_6999327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999327 prefixEnd_6999327 := by exact prefixLift 6999327
  have htrace : WordTrace (prefixWord ++ tailWord_6999327) baseStart_6999327 baseEnd_6999327 := by
    simpa [prefixWord, tailWord_6999327, baseEnd_6999327] using wordTrace_append hprefix tailTrace_6999327
  have hstable : (prefixWord ++ tailWord_6999327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999327).length < 2 ^ (prefixWord ++ tailWord_6999327).sum := by decide
  have hdescent : baseEnd_6999327 < baseStart_6999327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999360 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_6999360 : Nat := 118140960795 + 6999360 * 2 ^ 59
def prefixEnd_6999360 : Nat := 4983230072969 + 3 ^ 40 * 6999360 * 2
def baseEnd_6999360 : Nat := 3594035953853840205510535

theorem tailTrace_6999360 : CollatzResearch.WordTrace tailWord_6999360 prefixEnd_6999360 3594035953853840205510535 := by
  unfold tailWord_6999360
  simp only [CollatzResearch.WordTrace]
  refine ⟨127643815961260795181405767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170191754615014393575207689 127643815961260795181405767)
  ·
    refine ⟨191465723941891192772108651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127643815961260795181405767 191465723941891192772108651)
    ·
      refine ⟨287198585912836789158162977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191465723941891192772108651 287198585912836789158162977)
      ·
        refine ⟨215398939434627591868622233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287198585912836789158162977 215398939434627591868622233)
        ·
          refine ⟨161549204575970693901466675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215398939434627591868622233 161549204575970693901466675)
          ·
            refine ⟨242323806863956040852200013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161549204575970693901466675 242323806863956040852200013)
            ·
              refine ⟨90871427573983515319575005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242323806863956040852200013 90871427573983515319575005)
              ·
                refine ⟨34076785340243818244840627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90871427573983515319575005 34076785340243818244840627)
                ·
                  refine ⟨51115178010365727367260941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34076785340243818244840627 51115178010365727367260941)
                  ·
                    refine ⟨19168191753887147762722853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51115178010365727367260941 19168191753887147762722853)
                    ·
                      refine ⟨3594035953853840205510535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19168191753887147762722853 3594035953853840205510535)
                      ·
                        rfl

theorem cell23_6999360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_6999360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999360 prefixEnd_6999360 := by exact prefixLift 6999360
  have htrace : WordTrace (prefixWord ++ tailWord_6999360) baseStart_6999360 baseEnd_6999360 := by
    simpa [prefixWord, tailWord_6999360, baseEnd_6999360] using wordTrace_append hprefix tailTrace_6999360
  have hstable : (prefixWord ++ tailWord_6999360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999360).length < 2 ^ (prefixWord ++ tailWord_6999360).sum := by decide
  have hdescent : baseEnd_6999360 < baseStart_6999360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999361 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 5]
def baseStart_6999361 : Nat := 118140960795 + 6999361 * 2 ^ 59
def prefixEnd_6999361 : Nat := 4983230072969 + 3 ^ 40 * 6999361 * 2
def baseEnd_6999361 : Nat := 399337385259388300177559

theorem tailTrace_6999361 : CollatzResearch.WordTrace tailWord_6999361 prefixEnd_6999361 399337385259388300177559 := by
  unfold tailWord_6999361
  simp only [CollatzResearch.WordTrace]
  refine ⟨255287668395517967533597937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170191778930345311689065291 255287668395517967533597937)
  ·
    refine ⟨191465751296638475650198453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255287668395517967533597937 191465751296638475650198453)
    ·
      refine ⟨17949914184059857092206105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191465751296638475650198453 17949914184059857092206105)
      ·
        refine ⟨13462435638044892819154579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17949914184059857092206105 13462435638044892819154579)
        ·
          refine ⟨20193653457067339228731869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13462435638044892819154579 20193653457067339228731869)
          ·
            refine ⟨7572620046400252210774451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20193653457067339228731869 7572620046400252210774451)
            ·
              refine ⟨11358930069600378316161677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572620046400252210774451 11358930069600378316161677)
              ·
                refine ⟨4259598776100141868560629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11358930069600378316161677 4259598776100141868560629)
                ·
                  refine ⟨399337385259388300177559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259598776100141868560629 399337385259388300177559)
                  ·
                    rfl

theorem cell23_6999361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 5].length) (baseStart_6999361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999361 prefixEnd_6999361 := by exact prefixLift 6999361
  have htrace : WordTrace (prefixWord ++ tailWord_6999361) baseStart_6999361 baseEnd_6999361 := by
    simpa [prefixWord, tailWord_6999361, baseEnd_6999361] using wordTrace_append hprefix tailTrace_6999361
  have hstable : (prefixWord ++ tailWord_6999361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999361).length < 2 ^ (prefixWord ++ tailWord_6999361).sum := by decide
  have hdescent : baseEnd_6999361 < baseStart_6999361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999377 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_6999377 : Nat := 118140960795 + 6999377 * 2 ^ 59
def prefixEnd_6999377 : Nat := 4983230072969 + 3 ^ 40 * 6999377 * 2
def baseEnd_6999377 : Nat := 3594044683024966638997957

theorem tailTrace_6999377 : CollatzResearch.WordTrace tailWord_6999377 prefixEnd_6999377 3594044683024966638997957 := by
  unfold tailWord_6999377
  simp only [CollatzResearch.WordTrace]
  refine ⟨255288251963460002266180385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170192167975640001510786923 255288251963460002266180385)
  ·
    refine ⟨191466188972595001699635289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255288251963460002266180385 191466188972595001699635289)
    ·
      refine ⟨143599641729446251274726467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191466188972595001699635289 143599641729446251274726467)
      ·
        refine ⟨215399462594169376912089701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143599641729446251274726467 215399462594169376912089701)
        ·
          refine ⟨40387399236406758171016819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215399462594169376912089701 40387399236406758171016819)
          ·
            refine ⟨60581098854610137256525229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40387399236406758171016819 60581098854610137256525229)
            ·
              refine ⟨22717912070478801471196961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60581098854610137256525229 22717912070478801471196961)
              ·
                refine ⟨17038434052859101103397721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22717912070478801471196961 17038434052859101103397721)
                ·
                  refine ⟨12778825539644325827548291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17038434052859101103397721 12778825539644325827548291)
                  ·
                    refine ⟨19168238309466488741322437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12778825539644325827548291 19168238309466488741322437)
                    ·
                      refine ⟨3594044683024966638997957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19168238309466488741322437 3594044683024966638997957)
                      ·
                        rfl

theorem cell23_6999377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_6999377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999377 prefixEnd_6999377 := by exact prefixLift 6999377
  have htrace : WordTrace (prefixWord ++ tailWord_6999377) baseStart_6999377 baseEnd_6999377 := by
    simpa [prefixWord, tailWord_6999377, baseEnd_6999377] using wordTrace_append hprefix tailTrace_6999377
  have hstable : (prefixWord ++ tailWord_6999377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999377).length < 2 ^ (prefixWord ++ tailWord_6999377).sum := by decide
  have hdescent : baseEnd_6999377 < baseStart_6999377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999389 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6999389 : Nat := 118140960795 + 6999389 * 2 ^ 59
def prefixEnd_6999389 : Nat := 4983230072969 + 3 ^ 40 * 6999389 * 2
def baseEnd_6999389 : Nat := 3594050844792820592047903

theorem tailTrace_6999389 : CollatzResearch.WordTrace tailWord_6999389 prefixEnd_6999389 3594050844792820592047903 := by
  unfold tailWord_6999389
  simp only [CollatzResearch.WordTrace]
  refine ⟨255288689639416528315617221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170192459759611018877078147 255288689639416528315617221)
  ·
    refine ⟨47866629307390599059178229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255288689639416528315617221 47866629307390599059178229)
    ·
      refine ⟨4487496497567868661797959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47866629307390599059178229 4487496497567868661797959)
      ·
        refine ⟨6731244746351802992696939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4487496497567868661797959 6731244746351802992696939)
        ·
          refine ⟨10096867119527704489045409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6731244746351802992696939 10096867119527704489045409)
          ·
            refine ⟨7572650339645778366784057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10096867119527704489045409 7572650339645778366784057)
            ·
              refine ⟨5679487754734333775088043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7572650339645778366784057 5679487754734333775088043)
              ·
                refine ⟨8519231632101500662632065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679487754734333775088043 8519231632101500662632065)
                ·
                  refine ⟨6389423724076125496974049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8519231632101500662632065 6389423724076125496974049)
                  ·
                    refine ⟨4792067793057094122730537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6389423724076125496974049 4792067793057094122730537)
                    ·
                      refine ⟨3594050844792820592047903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792067793057094122730537 3594050844792820592047903)
                      ·
                        rfl

theorem cell23_6999389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6999389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999389 prefixEnd_6999389 := by exact prefixLift 6999389
  have htrace : WordTrace (prefixWord ++ tailWord_6999389) baseStart_6999389 baseEnd_6999389 := by
    simpa [prefixWord, tailWord_6999389, baseEnd_6999389] using wordTrace_append hprefix tailTrace_6999389
  have hstable : (prefixWord ++ tailWord_6999389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999389).length < 2 ^ (prefixWord ++ tailWord_6999389).sum := by decide
  have hdescent : baseEnd_6999389 < baseStart_6999389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999394 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_6999394 : Nat := 118140960795 + 6999394 * 2 ^ 59
def prefixEnd_6999394 : Nat := 4983230072969 + 3 ^ 40 * 6999394 * 2
def baseEnd_6999394 : Nat := 3594053412196093072485379

theorem tailTrace_6999394 : CollatzResearch.WordTrace tailWord_6999394 prefixEnd_6999394 3594053412196093072485379 := by
  unfold tailWord_6999394
  simp only [CollatzResearch.WordTrace]
  refine ⟨63822218001099603542387309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170192581336265609446366157 63822218001099603542387309)
  ·
    refine ⟨23933331750412351328395241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63822218001099603542387309 23933331750412351328395241)
    ·
      refine ⟨17949998812809263496296431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23933331750412351328395241 17949998812809263496296431)
      ·
        refine ⟨26924998219213895244444647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17949998812809263496296431 26924998219213895244444647)
        ·
          refine ⟨40387497328820842866666971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26924998219213895244444647 40387497328820842866666971)
          ·
            refine ⟨60581245993231264300000457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40387497328820842866666971 60581245993231264300000457)
            ·
              refine ⟨45435934494923448225000343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60581245993231264300000457 45435934494923448225000343)
              ·
                refine ⟨68153901742385172337500515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45435934494923448225000343 68153901742385172337500515)
                ·
                  refine ⟨102230852613577758506250773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68153901742385172337500515 102230852613577758506250773)
                  ·
                    refine ⟨4792071216261457429980505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102230852613577758506250773 4792071216261457429980505)
                    ·
                      refine ⟨3594053412196093072485379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792071216261457429980505 3594053412196093072485379)
                      ·
                        rfl

theorem cell23_6999394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_6999394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999394 prefixEnd_6999394 := by exact prefixLift 6999394
  have htrace : WordTrace (prefixWord ++ tailWord_6999394) baseStart_6999394 baseEnd_6999394 := by
    simpa [prefixWord, tailWord_6999394, baseEnd_6999394] using wordTrace_append hprefix tailTrace_6999394
  have hstable : (prefixWord ++ tailWord_6999394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999394).length < 2 ^ (prefixWord ++ tailWord_6999394).sum := by decide
  have hdescent : baseEnd_6999394 < baseStart_6999394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999397 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_6999397 : Nat := 118140960795 + 6999397 * 2 ^ 59
def prefixEnd_6999397 : Nat := 4983230072969 + 3 ^ 40 * 6999397 * 2
def baseEnd_6999397 : Nat := 3594054952638056560747865

theorem tailTrace_6999397 : CollatzResearch.WordTrace tailWord_6999397 prefixEnd_6999397 3594054952638056560747865 := by
  unfold tailWord_6999397
  simp only [CollatzResearch.WordTrace]
  refine ⟨255288981423387545681908445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170192654282258363787938963 255288981423387545681908445)
  ·
    refine ⟨95733368033770329630715667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255288981423387545681908445 95733368033770329630715667)
    ·
      refine ⟨143600052050655494446073501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95733368033770329630715667 143600052050655494446073501)
      ·
        refine ⟨53850019518995810417277563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143600052050655494446073501 53850019518995810417277563)
        ·
          refine ⟨80775029278493715625916345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53850019518995810417277563 80775029278493715625916345)
          ·
            refine ⟨60581271958870286719437259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80775029278493715625916345 60581271958870286719437259)
            ·
              refine ⟨90871907938305430079155889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60581271958870286719437259 90871907938305430079155889)
              ·
                refine ⟨68153930953729072559366917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90871907938305430079155889 68153930953729072559366917)
                ·
                  refine ⟨12778862053824201104881297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68153930953729072559366917 12778862053824201104881297)
                  ·
                    refine ⟨9584146540368150828660973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12778862053824201104881297 9584146540368150828660973)
                    ·
                      refine ⟨3594054952638056560747865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9584146540368150828660973 3594054952638056560747865)
                      ·
                        rfl

theorem cell23_6999397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_6999397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999397 prefixEnd_6999397 := by exact prefixLift 6999397
  have htrace : WordTrace (prefixWord ++ tailWord_6999397) baseStart_6999397 baseEnd_6999397 := by
    simpa [prefixWord, tailWord_6999397, baseEnd_6999397] using wordTrace_append hprefix tailTrace_6999397
  have hstable : (prefixWord ++ tailWord_6999397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999397).length < 2 ^ (prefixWord ++ tailWord_6999397).sum := by decide
  have hdescent : baseEnd_6999397 < baseStart_6999397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999438 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_6999438 : Nat := 118140960795 + 6999438 * 2 ^ 59
def prefixEnd_6999438 : Nat := 4983230072969 + 3 ^ 40 * 6999438 * 2
def baseEnd_6999438 : Nat := 1198025335114963633445059

theorem tailTrace_6999438 : CollatzResearch.WordTrace tailWord_6999438 prefixEnd_6999438 1198025335114963633445059 := by
  unfold tailWord_6999438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31911309602029876210518871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170193651210826006456100645 31911309602029876210518871)
  ·
    refine ⟨47866964403044814315778307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31911309602029876210518871 47866964403044814315778307)
    ·
      refine ⟨71800446604567221473667461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47866964403044814315778307 71800446604567221473667461)
      ·
        refine ⟨13462583738356354026312649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71800446604567221473667461 13462583738356354026312649)
        ·
          refine ⟨10096937803767265519734487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13462583738356354026312649 10096937803767265519734487)
          ·
            refine ⟨15145406705650898279601731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10096937803767265519734487 15145406705650898279601731)
            ·
              refine ⟨22718110058476347419402597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15145406705650898279601731 22718110058476347419402597)
              ·
                refine ⟨4259645635964315141137987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22718110058476347419402597 4259645635964315141137987)
                ·
                  refine ⟨6389468453946472711706981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259645635964315141137987 6389468453946472711706981)
                  ·
                    refine ⟨1198025335114963633445059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389468453946472711706981 1198025335114963633445059)
                    ·
                      rfl

theorem cell23_6999438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_6999438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999438 prefixEnd_6999438 := by exact prefixLift 6999438
  have htrace : WordTrace (prefixWord ++ tailWord_6999438) baseStart_6999438 baseEnd_6999438 := by
    simpa [prefixWord, tailWord_6999438, baseEnd_6999438] using wordTrace_append hprefix tailTrace_6999438
  have hstable : (prefixWord ++ tailWord_6999438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999438).length < 2 ^ (prefixWord ++ tailWord_6999438).sum := by decide
  have hdescent : baseEnd_6999438 < baseStart_6999438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999514 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_6999514 : Nat := 118140960795 + 6999514 * 2 ^ 59
def prefixEnd_6999514 : Nat := 4983230072969 + 3 ^ 40 * 6999514 * 2
def baseEnd_6999514 : Nat := 3594115029874632602984827

theorem tailTrace_6999514 : CollatzResearch.WordTrace tailWord_6999514 prefixEnd_6999514 3594115029874632602984827 := by
  unfold tailWord_6999514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63823312190990918665979399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170195499175975783109278397 63823312190990918665979399)
  ·
    refine ⟨95734968286486377998969099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63823312190990918665979399 95734968286486377998969099)
    ·
      refine ⟨143602452429729566998453649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95734968286486377998969099 143602452429729566998453649)
      ·
        refine ⟨107701839322297175248840237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143602452429729566998453649 107701839322297175248840237)
        ·
          refine ⟨40388189745861440718315089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107701839322297175248840237 40388189745861440718315089)
          ·
            refine ⟨30291142309396080538736317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40388189745861440718315089 30291142309396080538736317)
            ·
              refine ⟨11359178366023530202026119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30291142309396080538736317 11359178366023530202026119)
              ·
                refine ⟨17038767549035295303039179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359178366023530202026119 17038767549035295303039179)
                ·
                  refine ⟨25558151323552942954558769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17038767549035295303039179 25558151323552942954558769)
                  ·
                    refine ⟨19168613492664707215919077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25558151323552942954558769 19168613492664707215919077)
                    ·
                      refine ⟨3594115029874632602984827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19168613492664707215919077 3594115029874632602984827)
                      ·
                        rfl

theorem cell23_6999514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_6999514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999514 prefixEnd_6999514 := by exact prefixLift 6999514
  have htrace : WordTrace (prefixWord ++ tailWord_6999514) baseStart_6999514 baseEnd_6999514 := by
    simpa [prefixWord, tailWord_6999514, baseEnd_6999514] using wordTrace_append hprefix tailTrace_6999514
  have hstable : (prefixWord ++ tailWord_6999514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999514).length < 2 ^ (prefixWord ++ tailWord_6999514).sum := by decide
  have hdescent : baseEnd_6999514 < baseStart_6999514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999521 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_6999521 : Nat := 118140960795 + 6999521 * 2 ^ 59
def prefixEnd_6999521 : Nat := 4983230072969 + 3 ^ 40 * 6999521 * 2
def baseEnd_6999521 : Nat := 3594118624239214075597295

theorem tailTrace_6999521 : CollatzResearch.WordTrace tailWord_6999521 prefixEnd_6999521 3594118624239214075597295 := by
  unfold tailWord_6999521
  simp only [CollatzResearch.WordTrace]
  refine ⟨255293504074938314859422417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170195669383292209906281611 255293504074938314859422417)
  ·
    refine ⟨191470128056203736144566813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255293504074938314859422417 191470128056203736144566813)
    ·
      refine ⟨71801298021076401054212555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191470128056203736144566813 71801298021076401054212555)
      ·
        refine ⟨107701947031614601581318833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71801298021076401054212555 107701947031614601581318833)
        ·
          refine ⟨80776460273710951185989125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107701947031614601581318833 80776460273710951185989125)
          ·
            refine ⟨15145586301320803347372961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80776460273710951185989125 15145586301320803347372961)
            ·
              refine ⟨11359189725990602510529721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15145586301320803347372961 11359189725990602510529721)
              ·
                refine ⟨8519392294492951882897291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11359189725990602510529721 8519392294492951882897291)
                ·
                  refine ⟨12779088441739427824345937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8519392294492951882897291 12779088441739427824345937)
                  ·
                    refine ⟨9584316331304570868259453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12779088441739427824345937 9584316331304570868259453)
                    ·
                      refine ⟨3594118624239214075597295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9584316331304570868259453 3594118624239214075597295)
                      ·
                        rfl

theorem cell23_6999521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_6999521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999521 prefixEnd_6999521 := by exact prefixLift 6999521
  have htrace : WordTrace (prefixWord ++ tailWord_6999521) baseStart_6999521 baseEnd_6999521 := by
    simpa [prefixWord, tailWord_6999521, baseEnd_6999521] using wordTrace_append hprefix tailTrace_6999521
  have hstable : (prefixWord ++ tailWord_6999521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999521).length < 2 ^ (prefixWord ++ tailWord_6999521).sum := by decide
  have hdescent : baseEnd_6999521 < baseStart_6999521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999534 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_6999534 : Nat := 118140960795 + 6999534 * 2 ^ 59
def prefixEnd_6999534 : Nat := 4983230072969 + 3 ^ 40 * 6999534 * 2
def baseEnd_6999534 : Nat := 3594125299487722524734735

theorem tailTrace_6999534 : CollatzResearch.WordTrace tailWord_6999534 prefixEnd_6999534 3594125299487722524734735 := by
  unfold tailWord_6999534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31911747277986402259955707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170195985482594145386430437 31911747277986402259955707)
  ·
    refine ⟨47867620916979603389933561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31911747277986402259955707 47867620916979603389933561)
    ·
      refine ⟨35900715687734702542450171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47867620916979603389933561 35900715687734702542450171)
      ·
        refine ⟨53851073531602053813675257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35900715687734702542450171 53851073531602053813675257)
        ·
          refine ⟨40388305148701540360256443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53851073531602053813675257 40388305148701540360256443)
          ·
            refine ⟨60582457723052310540384665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40388305148701540360256443 60582457723052310540384665)
            ·
              refine ⟨45436843292289232905288499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60582457723052310540384665 45436843292289232905288499)
              ·
                refine ⟨68155264938433849357932749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45436843292289232905288499 68155264938433849357932749)
                ·
                  refine ⟨25558224351912693509224781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68155264938433849357932749 25558224351912693509224781)
                  ·
                    refine ⟨9584334131967260065959293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25558224351912693509224781 9584334131967260065959293)
                    ·
                      refine ⟨3594125299487722524734735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9584334131967260065959293 3594125299487722524734735)
                      ·
                        rfl

theorem cell23_6999534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_6999534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999534 prefixEnd_6999534 := by exact prefixLift 6999534
  have htrace : WordTrace (prefixWord ++ tailWord_6999534) baseStart_6999534 baseEnd_6999534 := by
    simpa [prefixWord, tailWord_6999534, baseEnd_6999534] using wordTrace_append hprefix tailTrace_6999534
  have hstable : (prefixWord ++ tailWord_6999534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999534).length < 2 ^ (prefixWord ++ tailWord_6999534).sum := by decide
  have hdescent : baseEnd_6999534 < baseStart_6999534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999557 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_6999557 : Nat := 118140960795 + 6999557 * 2 ^ 59
def prefixEnd_6999557 : Nat := 4983230072969 + 3 ^ 40 * 6999557 * 2
def baseEnd_6999557 : Nat := 3594137109542775934747129

theorem tailTrace_6999557 : CollatzResearch.WordTrace tailWord_6999557 prefixEnd_6999557 3594137109542775934747129 := by
  unfold tailWord_6999557
  simp only [CollatzResearch.WordTrace]
  refine ⟨255294817102807893007732925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170196544735205262005155283 255294817102807893007732925)
  ·
    refine ⟨95735556413552959877899847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255294817102807893007732925 95735556413552959877899847)
    ·
      refine ⟨143603334620329439816849771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95735556413552959877899847 143603334620329439816849771)
      ·
        refine ⟨215405001930494159725274657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143603334620329439816849771 215405001930494159725274657)
        ·
          refine ⟨161553751447870619793955993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215405001930494159725274657 161553751447870619793955993)
          ·
            refine ⟨121165313585902964845466995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161553751447870619793955993 121165313585902964845466995)
            ·
              refine ⟨181747970378854447268200493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121165313585902964845466995 181747970378854447268200493)
              ·
                refine ⟨68155488892070417725575185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181747970378854447268200493 68155488892070417725575185)
                ·
                  refine ⟨51116616669052813294181389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68155488892070417725575185 51116616669052813294181389)
                  ·
                    refine ⟨19168731250894804985318021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51116616669052813294181389 19168731250894804985318021)
                    ·
                      refine ⟨3594137109542775934747129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19168731250894804985318021 3594137109542775934747129)
                      ·
                        rfl

theorem cell23_6999557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_6999557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999557 prefixEnd_6999557 := by exact prefixLift 6999557
  have htrace : WordTrace (prefixWord ++ tailWord_6999557) baseStart_6999557 baseEnd_6999557 := by
    simpa [prefixWord, tailWord_6999557, baseEnd_6999557] using wordTrace_append hprefix tailTrace_6999557
  have hstable : (prefixWord ++ tailWord_6999557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999557).length < 2 ^ (prefixWord ++ tailWord_6999557).sum := by decide
  have hdescent : baseEnd_6999557 < baseStart_6999557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999572 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6999572 : Nat := 118140960795 + 6999572 * 2 ^ 59
def prefixEnd_6999572 : Nat := 4983230072969 + 3 ^ 40 * 6999572 * 2
def baseEnd_6999572 : Nat := 3594144811752593376059561

theorem tailTrace_6999572 : CollatzResearch.WordTrace tailWord_6999572 prefixEnd_6999572 3594144811752593376059561 := by
  unfold tailWord_6999572
  simp only [CollatzResearch.WordTrace]
  refine ⟨127647682098876775284764485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170196909465169033713019313 127647682098876775284764485)
  ·
    refine ⟨23933940393539395365893341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127647682098876775284764485 23933940393539395365893341)
    ·
      refine ⟨8975227647577273262210003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23933940393539395365893341 8975227647577273262210003)
      ·
        refine ⟨13462841471365909893315005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8975227647577273262210003 13462841471365909893315005)
        ·
          refine ⟨5048565551762216209993127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13462841471365909893315005 5048565551762216209993127)
          ·
            refine ⟨7572848327643324314989691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048565551762216209993127 7572848327643324314989691)
            ·
              refine ⟨11359272491464986472484537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572848327643324314989691 11359272491464986472484537)
              ·
                refine ⟨8519454368598739854363403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11359272491464986472484537 8519454368598739854363403)
                ·
                  refine ⟨12779181552898109781545105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8519454368598739854363403 12779181552898109781545105)
                  ·
                    refine ⟨9584386164673582336158829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12779181552898109781545105 9584386164673582336158829)
                    ·
                      refine ⟨3594144811752593376059561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9584386164673582336158829 3594144811752593376059561)
                      ·
                        rfl

theorem cell23_6999572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6999572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999572 prefixEnd_6999572 := by exact prefixLift 6999572
  have htrace : WordTrace (prefixWord ++ tailWord_6999572) baseStart_6999572 baseEnd_6999572 := by
    simpa [prefixWord, tailWord_6999572, baseEnd_6999572] using wordTrace_append hprefix tailTrace_6999572
  have hstable : (prefixWord ++ tailWord_6999572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999572).length < 2 ^ (prefixWord ++ tailWord_6999572).sum := by decide
  have hdescent : baseEnd_6999572 < baseStart_6999572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999594 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6999594 : Nat := 118140960795 + 6999594 * 2 ^ 59
def prefixEnd_6999594 : Nat := 4983230072969 + 3 ^ 40 * 6999594 * 2
def baseEnd_6999594 : Nat := 3594156108326992289984459

theorem tailTrace_6999594 : CollatzResearch.WordTrace tailWord_6999594 prefixEnd_6999594 3594156108326992289984459 := by
  unfold tailWord_6999594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63824041650918462081707459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170197444402449232217886557 63824041650918462081707459)
  ·
    refine ⟨95736062476377693122561189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63824041650918462081707459 95736062476377693122561189)
    ·
      refine ⟨17950511714320817460480223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95736062476377693122561189 17950511714320817460480223)
      ·
        refine ⟨26925767571481226190720335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17950511714320817460480223 26925767571481226190720335)
        ·
          refine ⟨40388651357221839286080503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26925767571481226190720335 40388651357221839286080503)
          ·
            refine ⟨60582977035832758929120755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40388651357221839286080503 60582977035832758929120755)
            ·
              refine ⟨90874465553749138393681133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60582977035832758929120755 90874465553749138393681133)
              ·
                refine ⟨34077924582655926897630425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90874465553749138393681133 34077924582655926897630425)
                ·
                  refine ⟨25558443436991945173222819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34077924582655926897630425 25558443436991945173222819)
                  ·
                    refine ⟨38337665155487917759834229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25558443436991945173222819 38337665155487917759834229)
                    ·
                      refine ⟨3594156108326992289984459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38337665155487917759834229 3594156108326992289984459)
                      ·
                        rfl

theorem cell23_6999594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6999594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999594 prefixEnd_6999594 := by exact prefixLift 6999594
  have htrace : WordTrace (prefixWord ++ tailWord_6999594) baseStart_6999594 baseEnd_6999594 := by
    simpa [prefixWord, tailWord_6999594, baseEnd_6999594] using wordTrace_append hprefix tailTrace_6999594
  have hstable : (prefixWord ++ tailWord_6999594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999594).length < 2 ^ (prefixWord ++ tailWord_6999594).sum := by decide
  have hdescent : baseEnd_6999594 < baseStart_6999594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999608 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 2, 2, 2]
def baseStart_6999608 : Nat := 118140960795 + 6999608 * 2 ^ 59
def prefixEnd_6999608 : Nat := 4983230072969 + 3 ^ 40 * 6999608 * 2
def baseEnd_6999608 : Nat := 3594163297056155235209395

theorem tailTrace_6999608 : CollatzResearch.WordTrace tailWord_6999608 prefixEnd_6999608 3594163297056155235209395 := by
  unfold tailWord_6999608
  simp only [CollatzResearch.WordTrace]
  refine ⟨127648338612811564358919739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170197784817082085811892985 127648338612811564358919739)
  ·
    refine ⟨191472507919217346538379609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127648338612811564358919739 191472507919217346538379609)
    ·
      refine ⟨143604380939413009903784707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191472507919217346538379609 143604380939413009903784707)
      ·
        refine ⟨215406571409119514855677061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143604380939413009903784707 215406571409119514855677061)
        ·
          refine ⟨40388732139209909035439449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215406571409119514855677061 40388732139209909035439449)
          ·
            refine ⟨30291549104407431776579587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40388732139209909035439449 30291549104407431776579587)
            ·
              refine ⟨45437323656611147664869381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30291549104407431776579587 45437323656611147664869381)
              ·
                refine ⟨8519498185614590187163009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45437323656611147664869381 8519498185614590187163009)
                ·
                  refine ⟨6389623639210942640372257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8519498185614590187163009 6389623639210942640372257)
                  ·
                    refine ⟨4792217729408206980279193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6389623639210942640372257 4792217729408206980279193)
                    ·
                      refine ⟨3594163297056155235209395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792217729408206980279193 3594163297056155235209395)
                      ·
                        rfl

theorem cell23_6999608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_6999608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999608 prefixEnd_6999608 := by exact prefixLift 6999608
  have htrace : WordTrace (prefixWord ++ tailWord_6999608) baseStart_6999608 baseEnd_6999608 := by
    simpa [prefixWord, tailWord_6999608, baseEnd_6999608] using wordTrace_append hprefix tailTrace_6999608
  have hstable : (prefixWord ++ tailWord_6999608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999608).length < 2 ^ (prefixWord ++ tailWord_6999608).sum := by decide
  have hdescent : baseEnd_6999608 < baseStart_6999608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999627 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 1, 7]
def baseStart_6999627 : Nat := 118140960795 + 6999627 * 2 ^ 59
def prefixEnd_6999627 : Nat := 4983230072969 + 3 ^ 40 * 6999627 * 2
def baseEnd_6999627 : Nat := 1198057684396196886957269

theorem tailTrace_6999627 : CollatzResearch.WordTrace tailWord_6999627 prefixEnd_6999627 1198057684396196886957269 := by
  unfold tailWord_6999627
  simp only [CollatzResearch.WordTrace]
  refine ⟨255297370212554294962781135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170198246808369529975187423 255297370212554294962781135)
  ·
    refine ⟨382946055318831442444171703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255297370212554294962781135 382946055318831442444171703)
    ·
      refine ⟨574419082978247163666257555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382946055318831442444171703 574419082978247163666257555)
      ·
        refine ⟨861628624467370745499386333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574419082978247163666257555 861628624467370745499386333)
        ·
          refine ⟨323110734175264029562269875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 861628624467370745499386333 323110734175264029562269875)
          ·
            refine ⟨484666101262896044343404813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323110734175264029562269875 484666101262896044343404813)
            ·
              refine ⟨181749787973586016628776805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484666101262896044343404813 181749787973586016628776805)
              ·
                refine ⟨34078085245047378117895651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181749787973586016628776805 34078085245047378117895651)
                ·
                  refine ⟨51117127867571067176843477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34078085245047378117895651 51117127867571067176843477)
                  ·
                    refine ⟨1198057684396196886957269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51117127867571067176843477 1198057684396196886957269)
                    ·
                      rfl

theorem cell23_6999627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_6999627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999627 prefixEnd_6999627 := by exact prefixLift 6999627
  have htrace : WordTrace (prefixWord ++ tailWord_6999627) baseStart_6999627 baseEnd_6999627 := by
    simpa [prefixWord, tailWord_6999627, baseEnd_6999627] using wordTrace_append hprefix tailTrace_6999627
  have hstable : (prefixWord ++ tailWord_6999627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999627).length < 2 ^ (prefixWord ++ tailWord_6999627).sum := by decide
  have hdescent : baseEnd_6999627 < baseStart_6999627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999704 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 8]
def baseStart_6999704 : Nat := 118140960795 + 6999704 * 2 ^ 59
def prefixEnd_6999704 : Nat := 4983230072969 + 3 ^ 40 * 6999704 * 2
def baseEnd_6999704 : Nat := 399356954577665206623217

theorem tailTrace_6999704 : CollatzResearch.WordTrace tailWord_6999704 prefixEnd_6999704 399356954577665206623217 := by
  unfold tailWord_6999704
  simp only [CollatzResearch.WordTrace]
  refine ⟨127650089316637668556667083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170200119088850224742222777 127650089316637668556667083)
  ·
    refine ⟨191475133974956502835000625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127650089316637668556667083 191475133974956502835000625)
    ·
      refine ⟨143606350481217377126250469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191475133974956502835000625 143606350481217377126250469)
      ·
        refine ⟨26926190715228258211171963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143606350481217377126250469 26926190715228258211171963)
        ·
          refine ⟨40389286072842387316757945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26926190715228258211171963 40389286072842387316757945)
          ·
            refine ⟨30291964554631790487568459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40389286072842387316757945 30291964554631790487568459)
            ·
              refine ⟨45437946831947685731352689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30291964554631790487568459 45437946831947685731352689)
              ·
                refine ⟨34078460123960764298514517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45437946831947685731352689 34078460123960764298514517)
                ·
                  refine ⟨399356954577665206623217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34078460123960764298514517 399356954577665206623217)
                  ·
                    rfl

theorem cell23_6999704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_6999704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999704 prefixEnd_6999704 := by exact prefixLift 6999704
  have htrace : WordTrace (prefixWord ++ tailWord_6999704) baseStart_6999704 baseEnd_6999704 := by
    simpa [prefixWord, tailWord_6999704, baseEnd_6999704] using wordTrace_append hprefix tailTrace_6999704
  have hstable : (prefixWord ++ tailWord_6999704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999704).length < 2 ^ (prefixWord ++ tailWord_6999704).sum := by decide
  have hdescent : baseEnd_6999704 < baseStart_6999704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999738 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_6999738 : Nat := 118140960795 + 6999738 * 2 ^ 59
def prefixEnd_6999738 : Nat := 4983230072969 + 3 ^ 40 * 6999738 * 2
def baseEnd_6999738 : Nat := 399358894393471080731533

theorem tailTrace_6999738 : CollatzResearch.WordTrace tailWord_6999738 prefixEnd_6999738 399358894393471080731533 := by
  unfold tailWord_6999738
  simp only [CollatzResearch.WordTrace]
  refine ⟨63825354678788040230017967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170200945810101440613381245 63825354678788040230017967)
  ·
    refine ⟨95738032018182060345026951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63825354678788040230017967 95738032018182060345026951)
    ·
      refine ⟨143607048027273090517540427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95738032018182060345026951 143607048027273090517540427)
      ·
        refine ⟨215410572040909635776310641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143607048027273090517540427 215410572040909635776310641)
        ·
          refine ⟨161557929030682226832232981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215410572040909635776310641 161557929030682226832232981)
          ·
            refine ⟨7573027923313229382760921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161557929030682226832232981 7573027923313229382760921)
            ·
              refine ⟨5679770942484922037070691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573027923313229382760921 5679770942484922037070691)
              ·
                refine ⟨8519656413727383055606037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679770942484922037070691 8519656413727383055606037)
                ·
                  refine ⟨399358894393471080731533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8519656413727383055606037 399358894393471080731533)
                  ·
                    rfl

theorem cell23_6999738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_6999738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999738 prefixEnd_6999738 := by exact prefixLift 6999738
  have htrace : WordTrace (prefixWord ++ tailWord_6999738) baseStart_6999738 baseEnd_6999738 := by
    simpa [prefixWord, tailWord_6999738, baseEnd_6999738] using wordTrace_append hprefix tailTrace_6999738
  have hstable : (prefixWord ++ tailWord_6999738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999738).length < 2 ^ (prefixWord ++ tailWord_6999738).sum := by decide
  have hdescent : baseEnd_6999738 < baseStart_6999738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999748 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_6999748 : Nat := 118140960795 + 6999748 * 2 ^ 59
def prefixEnd_6999748 : Nat := 4983230072969 + 3 ^ 40 * 6999748 * 2
def baseEnd_6999748 : Nat := 3594235184347784687458751

theorem tailTrace_6999748 : CollatzResearch.WordTrace tailWord_6999748 prefixEnd_6999748 3594235184347784687458751 := by
  unfold tailWord_6999748
  simp only [CollatzResearch.WordTrace]
  refine ⟨127650891722557966313967949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170201188963410621751957265 127650891722557966313967949)
  ·
    refine ⟨47869084395959237367737981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127650891722557966313967949 47869084395959237367737981)
    ·
      refine ⟨17950906648484714012901743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47869084395959237367737981 17950906648484714012901743)
      ·
        refine ⟨26926359972727071019352615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17950906648484714012901743 26926359972727071019352615)
        ·
          refine ⟨40389539959090606529028923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26926359972727071019352615 40389539959090606529028923)
          ·
            refine ⟨60584309938635909793543385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40389539959090606529028923 60584309938635909793543385)
            ·
              refine ⟨45438232453976932345157539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60584309938635909793543385 45438232453976932345157539)
              ·
                refine ⟨68157348680965398517736309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45438232453976932345157539 68157348680965398517736309)
                ·
                  refine ⟨6389751438840506111037779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68157348680965398517736309 6389751438840506111037779)
                  ·
                    refine ⟨9584627158260759166556669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6389751438840506111037779 9584627158260759166556669)
                    ·
                      refine ⟨3594235184347784687458751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9584627158260759166556669 3594235184347784687458751)
                      ·
                        rfl

theorem cell23_6999748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_6999748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999748 prefixEnd_6999748 := by exact prefixLift 6999748
  have htrace : WordTrace (prefixWord ++ tailWord_6999748) baseStart_6999748 baseEnd_6999748 := by
    simpa [prefixWord, tailWord_6999748, baseEnd_6999748] using wordTrace_append hprefix tailTrace_6999748
  have hstable : (prefixWord ++ tailWord_6999748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999748).length < 2 ^ (prefixWord ++ tailWord_6999748).sum := by decide
  have hdescent : baseEnd_6999748 < baseStart_6999748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999768 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 1, 5]
def baseStart_6999768 : Nat := 118140960795 + 6999768 * 2 ^ 59
def prefixEnd_6999768 : Nat := 4983230072969 + 3 ^ 40 * 6999768 * 2
def baseEnd_6999768 : Nat := 1198081817986958203069553

theorem tailTrace_6999768 : CollatzResearch.WordTrace tailWord_6999768 prefixEnd_6999768 1198081817986958203069553 := by
  unfold tailWord_6999768
  simp only [CollatzResearch.WordTrace]
  refine ⟨127651256452521738021831979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170201675270028984029109305 127651256452521738021831979)
  ·
    refine ⟨191476884678782607032747969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127651256452521738021831979 191476884678782607032747969)
    ·
      refine ⟨143607663509086955274560977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191476884678782607032747969 143607663509086955274560977)
      ·
        refine ⟨107705747631815216455920733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143607663509086955274560977 107705747631815216455920733)
        ·
          refine ⟨40389655361930706170970275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107705747631815216455920733 40389655361930706170970275)
          ·
            refine ⟨60584483042896059256455413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40389655361930706170970275 60584483042896059256455413)
            ·
              refine ⟨5679795285271505555292695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60584483042896059256455413 5679795285271505555292695)
              ·
                refine ⟨8519692927907258332939043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679795285271505555292695 8519692927907258332939043)
                ·
                  refine ⟨12779539391860887499408565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8519692927907258332939043 12779539391860887499408565)
                  ·
                    refine ⟨1198081817986958203069553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12779539391860887499408565 1198081817986958203069553)
                    ·
                      rfl

theorem cell23_6999768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_6999768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999768 prefixEnd_6999768 := by exact prefixLift 6999768
  have htrace : WordTrace (prefixWord ++ tailWord_6999768) baseStart_6999768 baseEnd_6999768 := by
    simpa [prefixWord, tailWord_6999768, baseEnd_6999768] using wordTrace_append hprefix tailTrace_6999768
  have hstable : (prefixWord ++ tailWord_6999768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999768).length < 2 ^ (prefixWord ++ tailWord_6999768).sum := by decide
  have hdescent : baseEnd_6999768 < baseStart_6999768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999791 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_6999791 : Nat := 118140960795 + 6999791 * 2 ^ 59
def prefixEnd_6999791 : Nat := 4983230072969 + 3 ^ 40 * 6999791 * 2
def baseEnd_6999791 : Nat := 3594257264015928019221053

theorem tailTrace_6999791 : CollatzResearch.WordTrace tailWord_6999791 prefixEnd_6999791 3594257264015928019221053 := by
  unfold tailWord_6999791
  simp only [CollatzResearch.WordTrace]
  refine ⟨255303351783960150971751227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170202234522640100647834151 255303351783960150971751227)
  ·
    refine ⟨382955027675940226457626841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255303351783960150971751227 382955027675940226457626841)
    ·
      refine ⟨287216270756955169843220131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382955027675940226457626841 287216270756955169843220131)
      ·
        refine ⟨430824406135432754764830197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287216270756955169843220131 430824406135432754764830197)
        ·
          refine ⟨40389788075196820759202831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 430824406135432754764830197 40389788075196820759202831)
          ·
            refine ⟨60584682112795231138804247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40389788075196820759202831 60584682112795231138804247)
            ·
              refine ⟨90877023169192846708206371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60584682112795231138804247 90877023169192846708206371)
              ·
                refine ⟨136315534753789270062309557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90877023169192846708206371 136315534753789270062309557)
                ·
                  refine ⟨12779581383167744068341521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136315534753789270062309557 12779581383167744068341521)
                  ·
                    refine ⟨9584686037375808051256141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12779581383167744068341521 9584686037375808051256141)
                    ·
                      refine ⟨3594257264015928019221053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9584686037375808051256141 3594257264015928019221053)
                      ·
                        rfl

theorem cell23_6999791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_6999791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999791 prefixEnd_6999791 := by exact prefixLift 6999791
  have htrace : WordTrace (prefixWord ++ tailWord_6999791) baseStart_6999791 baseEnd_6999791 := by
    simpa [prefixWord, tailWord_6999791, baseEnd_6999791] using wordTrace_append hprefix tailTrace_6999791
  have hstable : (prefixWord ++ tailWord_6999791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999791).length < 2 ^ (prefixWord ++ tailWord_6999791).sum := by decide
  have hdescent : baseEnd_6999791 < baseStart_6999791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999798 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_6999798 : Nat := 118140960795 + 6999798 * 2 ^ 59
def prefixEnd_6999798 : Nat := 4983230072969 + 3 ^ 40 * 6999798 * 2
def baseEnd_6999798 : Nat := 1198086952793503163944507

theorem tailTrace_6999798 : CollatzResearch.WordTrace tailWord_6999798 prefixEnd_6999798 1198086952793503163944507 := by
  unfold tailWord_6999798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956475443433424447953503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170202404729956527444837365 15956475443433424447953503)
  ·
    refine ⟨23934713165150136671930255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956475443433424447953503 23934713165150136671930255)
    ·
      refine ⟨35902069747725205007895383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23934713165150136671930255 35902069747725205007895383)
      ·
        refine ⟨53853104621587807511843075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35902069747725205007895383 53853104621587807511843075)
        ·
          refine ⟨80779656932381711267764613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53853104621587807511843075 80779656932381711267764613)
          ·
            refine ⟨15146185674821570862705865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80779656932381711267764613 15146185674821570862705865)
            ·
              refine ⟨11359639256116178147029399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15146185674821570862705865 11359639256116178147029399)
              ·
                refine ⟨17039458884174267220544099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359639256116178147029399 17039458884174267220544099)
                ·
                  refine ⟨25559188326261400830816149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17039458884174267220544099 25559188326261400830816149)
                  ·
                    refine ⟨1198086952793503163944507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25559188326261400830816149 1198086952793503163944507)
                    ·
                      rfl

theorem cell23_6999798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_6999798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999798 prefixEnd_6999798 := by exact prefixLift 6999798
  have htrace : WordTrace (prefixWord ++ tailWord_6999798) baseStart_6999798 baseEnd_6999798 := by
    simpa [prefixWord, tailWord_6999798, baseEnd_6999798] using wordTrace_append hprefix tailTrace_6999798
  have hstable : (prefixWord ++ tailWord_6999798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999798).length < 2 ^ (prefixWord ++ tailWord_6999798).sum := by decide
  have hdescent : baseEnd_6999798 < baseStart_6999798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999822 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_6999822 : Nat := 118140960795 + 6999822 * 2 ^ 59
def prefixEnd_6999822 : Nat := 4983230072969 + 3 ^ 40 * 6999822 * 2
def baseEnd_6999822 : Nat := 3594273181916217397933411

theorem tailTrace_6999822 : CollatzResearch.WordTrace tailWord_6999822 prefixEnd_6999822 3594273181916217397933411 := by
  unfold tailWord_6999822
  simp only [CollatzResearch.WordTrace]
  refine ⟨31913060305855980408266215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170202988297898562177419813 31913060305855980408266215)
  ·
    refine ⟨47869590458783970612399323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31913060305855980408266215 47869590458783970612399323)
    ·
      refine ⟨71804385688175955918598985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47869590458783970612399323 71804385688175955918598985)
      ·
        refine ⟨53853289266131966938949239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71804385688175955918598985 53853289266131966938949239)
        ·
          refine ⟨80779933899197950408423859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53853289266131966938949239 80779933899197950408423859)
          ·
            refine ⟨121169900848796925612635789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80779933899197950408423859 121169900848796925612635789)
            ·
              refine ⟨45438712818298847104738421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121169900848796925612635789 45438712818298847104738421)
              ·
                refine ⟨4259879326715516916069227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45438712818298847104738421 4259879326715516916069227)
                ·
                  refine ⟨6389818990073275374103841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259879326715516916069227 6389818990073275374103841)
                  ·
                    refine ⟨4792364242554956530577881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6389818990073275374103841 4792364242554956530577881)
                    ·
                      refine ⟨3594273181916217397933411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792364242554956530577881 3594273181916217397933411)
                      ·
                        rfl

theorem cell23_6999822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_6999822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999822 prefixEnd_6999822 := by exact prefixLift 6999822
  have htrace : WordTrace (prefixWord ++ tailWord_6999822) baseStart_6999822 baseEnd_6999822 := by
    simpa [prefixWord, tailWord_6999822, baseEnd_6999822] using wordTrace_append hprefix tailTrace_6999822
  have hstable : (prefixWord ++ tailWord_6999822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999822).length < 2 ^ (prefixWord ++ tailWord_6999822).sum := by decide
  have hdescent : baseEnd_6999822 < baseStart_6999822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999881 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_6999881 : Nat := 118140960795 + 6999881 * 2 ^ 59
def prefixEnd_6999881 : Nat := 4983230072969 + 3 ^ 40 * 6999881 * 2
def baseEnd_6999881 : Nat := 3594303477274832667095639

theorem tailTrace_6999881 : CollatzResearch.WordTrace tailWord_6999881 prefixEnd_6999881 3594303477274832667095639 := by
  unfold tailWord_6999881
  simp only [CollatzResearch.WordTrace]
  refine ⟨255306634353634096342527497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170204422902422730895018331 255306634353634096342527497)
  ·
    refine ⟨191479975765225572256895623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255306634353634096342527497 191479975765225572256895623)
    ·
      refine ⟨287219963647838358385343435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191479975765225572256895623 287219963647838358385343435)
      ·
        refine ⟨430829945471757537578015153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287219963647838358385343435 430829945471757537578015153)
        ·
          refine ⟨323122459103818153183511365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430829945471757537578015153 323122459103818153183511365)
          ·
            refine ⟨60585461081965903721908381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323122459103818153183511365 60585461081965903721908381)
            ·
              refine ⟨22719547905737213895715643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60585461081965903721908381 22719547905737213895715643)
              ·
                refine ⟨34079321858605820843573465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22719547905737213895715643 34079321858605820843573465)
                ·
                  refine ⟨25559491393954365632680099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34079321858605820843573465 25559491393954365632680099)
                  ·
                    refine ⟨38339237090931548449020149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25559491393954365632680099 38339237090931548449020149)
                    ·
                      refine ⟨3594303477274832667095639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38339237090931548449020149 3594303477274832667095639)
                      ·
                        rfl

theorem cell23_6999881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_6999881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999881 prefixEnd_6999881 := by exact prefixLift 6999881
  have htrace : WordTrace (prefixWord ++ tailWord_6999881) baseStart_6999881 baseEnd_6999881 := by
    simpa [prefixWord, tailWord_6999881, baseEnd_6999881] using wordTrace_append hprefix tailTrace_6999881
  have hstable : (prefixWord ++ tailWord_6999881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999881).length < 2 ^ (prefixWord ++ tailWord_6999881).sum := by decide
  have hdescent : baseEnd_6999881 < baseStart_6999881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999912 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6999912 : Nat := 118140960795 + 6999912 * 2 ^ 59
def prefixEnd_6999912 : Nat := 4983230072969 + 3 ^ 40 * 6999912 * 2
def baseEnd_6999912 : Nat := 3594319395175122045807997

theorem tailTrace_6999912 : CollatzResearch.WordTrace tailWord_6999912 prefixEnd_6999912 3594319395175122045807997 := by
  unfold tailWord_6999912
  simp only [CollatzResearch.WordTrace]
  refine ⟨127653882508260894318452995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170205176677681192424603993 127653882508260894318452995)
  ·
    refine ⟨191480823762391341477679493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127653882508260894318452995 191480823762391341477679493)
    ·
      refine ⟨35902654455448376527064905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191480823762391341477679493 35902654455448376527064905)
      ·
        refine ⟨26926990841586282395298679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35902654455448376527064905 26926990841586282395298679)
        ·
          refine ⟨40390486262379423592948019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26926990841586282395298679 40390486262379423592948019)
          ·
            refine ⟨60585729393569135389422029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40390486262379423592948019 60585729393569135389422029)
            ·
              refine ⟨22719648522588425771033261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60585729393569135389422029 22719648522588425771033261)
              ·
                refine ⟨8519868195970659664137473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22719648522588425771033261 8519868195970659664137473)
                ·
                  refine ⟨6389901146977994748103105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8519868195970659664137473 6389901146977994748103105)
                  ·
                    refine ⟨4792425860233496061077329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6389901146977994748103105 4792425860233496061077329)
                    ·
                      refine ⟨3594319395175122045807997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792425860233496061077329 3594319395175122045807997)
                      ·
                        rfl

theorem cell23_6999912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6999912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999912 prefixEnd_6999912 := by exact prefixLift 6999912
  have htrace : WordTrace (prefixWord ++ tailWord_6999912) baseStart_6999912 baseEnd_6999912 := by
    simpa [prefixWord, tailWord_6999912, baseEnd_6999912] using wordTrace_append hprefix tailTrace_6999912
  have hstable : (prefixWord ++ tailWord_6999912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999912).length < 2 ^ (prefixWord ++ tailWord_6999912).sum := by decide
  have hdescent : baseEnd_6999912 < baseStart_6999912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999941 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_6999941 : Nat := 118140960795 + 6999941 * 2 ^ 59
def prefixEnd_6999941 : Nat := 4983230072969 + 3 ^ 40 * 6999941 * 2
def baseEnd_6999941 : Nat := 3594334286114102432345363

theorem tailTrace_6999941 : CollatzResearch.WordTrace tailWord_6999941 prefixEnd_6999941 3594334286114102432345363 := by
  unfold tailWord_6999941
  simp only [CollatzResearch.WordTrace]
  refine ⟨255308822733416726589711677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170205881822277817726474451 255308822733416726589711677)
  ·
    refine ⟨95740808525031272471141879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255308822733416726589711677 95740808525031272471141879)
    ·
      refine ⟨143611212787546908706712819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95740808525031272471141879 143611212787546908706712819)
      ·
        refine ⟨215416819181320363060069229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143611212787546908706712819 215416819181320363060069229)
        ·
          refine ⟨80781307192995136147525961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215416819181320363060069229 80781307192995136147525961)
          ·
            refine ⟨60585980394746352110644471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80781307192995136147525961 60585980394746352110644471)
            ·
              refine ⟨90878970592119528165966707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60585980394746352110644471 90878970592119528165966707)
              ·
                refine ⟨136318455888179292248950061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90878970592119528165966707 136318455888179292248950061)
                ·
                  refine ⟨51119420958067234593356273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136318455888179292248950061 51119420958067234593356273)
                  ·
                    refine ⟨38339565718550425945017205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51119420958067234593356273 38339565718550425945017205)
                    ·
                      refine ⟨3594334286114102432345363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38339565718550425945017205 3594334286114102432345363)
                      ·
                        rfl

theorem cell23_6999941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_6999941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999941 prefixEnd_6999941 := by exact prefixLift 6999941
  have htrace : WordTrace (prefixWord ++ tailWord_6999941) baseStart_6999941 baseEnd_6999941 := by
    simpa [prefixWord, tailWord_6999941, baseEnd_6999941] using wordTrace_append hprefix tailTrace_6999941
  have hstable : (prefixWord ++ tailWord_6999941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999941).length < 2 ^ (prefixWord ++ tailWord_6999941).sum := by decide
  have hdescent : baseEnd_6999941 < baseStart_6999941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999985 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_6999985 : Nat := 118140960795 + 6999985 * 2 ^ 59
def prefixEnd_6999985 : Nat := 4983230072969 + 3 ^ 40 * 6999985 * 2
def baseEnd_6999985 : Nat := 3594356879262900260195161

theorem tailTrace_6999985 : CollatzResearch.WordTrace tailWord_6999985 prefixEnd_6999985 3594356879262900260195161 := by
  unfold tailWord_6999985
  simp only [CollatzResearch.WordTrace]
  refine ⟨255310427545257322104313409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170206951696838214736208939 255310427545257322104313409)
  ·
    refine ⟨191482820658942991578235057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255310427545257322104313409 191482820658942991578235057)
    ·
      refine ⟨143612115494207243683676293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191482820658942991578235057 143612115494207243683676293)
      ·
        refine ⟨26927271655163858190689305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143612115494207243683676293 26927271655163858190689305)
        ·
          refine ⟨20195453741372893643016979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26927271655163858190689305 20195453741372893643016979)
          ·
            refine ⟨30293180612059340464525469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20195453741372893643016979 30293180612059340464525469)
            ·
              refine ⟨11359942729522252674197051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30293180612059340464525469 11359942729522252674197051)
              ·
                refine ⟨17039914094283379011295577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359942729522252674197051 17039914094283379011295577)
                ·
                  refine ⟨12779935570712534258471683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17039914094283379011295577 12779935570712534258471683)
                  ·
                    refine ⟨19169903356068801387707525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12779935570712534258471683 19169903356068801387707525)
                    ·
                      refine ⟨3594356879262900260195161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19169903356068801387707525 3594356879262900260195161)
                      ·
                        rfl

theorem cell23_6999985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_6999985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999985 prefixEnd_6999985 := by exact prefixLift 6999985
  have htrace : WordTrace (prefixWord ++ tailWord_6999985) baseStart_6999985 baseEnd_6999985 := by
    simpa [prefixWord, tailWord_6999985, baseEnd_6999985] using wordTrace_append hprefix tailTrace_6999985
  have hstable : (prefixWord ++ tailWord_6999985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999985).length < 2 ^ (prefixWord ++ tailWord_6999985).sum := by decide
  have hdescent : baseEnd_6999985 < baseStart_6999985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999991 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 8]
def baseStart_6999991 : Nat := 118140960795 + 6999991 * 2 ^ 59
def prefixEnd_6999991 : Nat := 4983230072969 + 3 ^ 40 * 6999991 * 2
def baseEnd_6999991 : Nat := 399373328905203026302237

theorem tailTrace_6999991 : CollatzResearch.WordTrace tailWord_6999991 prefixEnd_6999991 399373328905203026302237 := by
  unfold tailWord_6999991
  simp only [CollatzResearch.WordTrace]
  refine ⟨255310646383235585129031827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170207097588823723419354551 255310646383235585129031827)
  ·
    refine ⟨382965969574853377693547741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255310646383235585129031827 382965969574853377693547741)
    ·
      refine ⟨143612238590570016635080403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382965969574853377693547741 143612238590570016635080403)
      ·
        refine ⟨215418357885855024952620605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143612238590570016635080403 215418357885855024952620605)
        ·
          refine ⟨80781884207195634357232727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215418357885855024952620605 80781884207195634357232727)
          ·
            refine ⟨121172826310793451535849091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80781884207195634357232727 121172826310793451535849091)
            ·
              refine ⟨181759239466190177303773637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121172826310793451535849091 181759239466190177303773637)
              ·
                refine ⟨34079857399910658244457557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181759239466190177303773637 34079857399910658244457557)
                ·
                  refine ⟨399373328905203026302237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34079857399910658244457557 399373328905203026302237)
                  ·
                    rfl

theorem cell23_6999991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 8].length) (baseStart_6999991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999991 prefixEnd_6999991 := by exact prefixLift 6999991
  have htrace : WordTrace (prefixWord ++ tailWord_6999991) baseStart_6999991 baseEnd_6999991 := by
    simpa [prefixWord, tailWord_6999991, baseEnd_6999991] using wordTrace_append hprefix tailTrace_6999991
  have hstable : (prefixWord ++ tailWord_6999991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999991).length < 2 ^ (prefixWord ++ tailWord_6999991).sum := by decide
  have hdescent : baseEnd_6999991 < baseStart_6999991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999995 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 1, 4]
def baseStart_6999995 : Nat := 118140960795 + 6999995 * 2 ^ 59
def prefixEnd_6999995 : Nat := 4983230072969 + 3 ^ 40 * 6999995 * 2
def baseEnd_6999995 : Nat := 1198120671356481740356705

theorem tailTrace_6999995 : CollatzResearch.WordTrace tailWord_6999995 prefixEnd_6999995 1198120671356481740356705 := by
  unfold tailWord_6999995
  simp only [CollatzResearch.WordTrace]
  refine ⟨255310792275221093812177439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170207194850147395874784959 255310792275221093812177439)
  ·
    refine ⟨382966188412831640718266159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255310792275221093812177439 382966188412831640718266159)
    ·
      refine ⟨574449282619247461077399239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382966188412831640718266159 574449282619247461077399239)
      ·
        refine ⟨861673923928871191616098859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574449282619247461077399239 861673923928871191616098859)
        ·
          refine ⟨1292510885893306787424148289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861673923928871191616098859 1292510885893306787424148289)
          ·
            refine ⟨969383164419980090568111217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292510885893306787424148289 969383164419980090568111217)
            ·
              refine ⟨727037373314985067926083413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969383164419980090568111217 727037373314985067926083413)
              ·
                refine ⟨4259984609267490632379395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 727037373314985067926083413 4259984609267490632379395)
                ·
                  refine ⟨6389976913901235948569093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259984609267490632379395 6389976913901235948569093)
                  ·
                    refine ⟨1198120671356481740356705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389976913901235948569093 1198120671356481740356705)
                    ·
                      rfl

theorem cell23_6999995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 4].length) (baseStart_6999995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999995 prefixEnd_6999995 := by exact prefixLift 6999995
  have htrace : WordTrace (prefixWord ++ tailWord_6999995) baseStart_6999995 baseEnd_6999995 := by
    simpa [prefixWord, tailWord_6999995, baseEnd_6999995] using wordTrace_append hprefix tailTrace_6999995
  have hstable : (prefixWord ++ tailWord_6999995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999995).length < 2 ^ (prefixWord ++ tailWord_6999995).sum := by decide
  have hdescent : baseEnd_6999995 < baseStart_6999995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6999998 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_6999998 : Nat := 118140960795 + 6999998 * 2 ^ 59
def prefixEnd_6999998 : Nat := 4983230072969 + 3 ^ 40 * 6999998 * 2
def baseEnd_6999998 : Nat := 3594363554511408709332601

theorem tailTrace_6999998 : CollatzResearch.WordTrace tailWord_6999998 prefixEnd_6999998 3594363554511408709332601 := by
  unfold tailWord_6999998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31913862711776278165567081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170207267796140150216357765 31913862711776278165567081)
  ·
    refine ⟨23935397033832208624175311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31913862711776278165567081 23935397033832208624175311)
    ·
      refine ⟨35903095550748312936262967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23935397033832208624175311 35903095550748312936262967)
      ·
        refine ⟨53854643326122469404394451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35903095550748312936262967 53854643326122469404394451)
        ·
          refine ⟨80781964989183704106591677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53854643326122469404394451 80781964989183704106591677)
          ·
            refine ⟨30293236870943889039971879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80781964989183704106591677 30293236870943889039971879)
            ·
              refine ⟨45439855306415833559957819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30293236870943889039971879 45439855306415833559957819)
              ·
                refine ⟨68159782959623750339936729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45439855306415833559957819 68159782959623750339936729)
                ·
                  refine ⟨51119837219717812754952547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68159782959623750339936729 51119837219717812754952547)
                  ·
                    refine ⟨76679755829576719132428821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51119837219717812754952547 76679755829576719132428821)
                    ·
                      refine ⟨3594363554511408709332601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76679755829576719132428821 3594363554511408709332601)
                      ·
                        rfl

theorem cell23_6999998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_6999998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6999998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6999998 prefixEnd_6999998 := by exact prefixLift 6999998
  have htrace : WordTrace (prefixWord ++ tailWord_6999998) baseStart_6999998 baseEnd_6999998 := by
    simpa [prefixWord, tailWord_6999998, baseEnd_6999998] using wordTrace_append hprefix tailTrace_6999998
  have hstable : (prefixWord ++ tailWord_6999998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6999998).length < 2 ^ (prefixWord ++ tailWord_6999998).sum := by decide
  have hdescent : baseEnd_6999998 < baseStart_6999998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6999998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000008 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 8]
def baseStart_7000008 : Nat := 118140960795 + 7000008 * 2 ^ 59
def prefixEnd_7000008 : Nat := 4983230072969 + 3 ^ 40 * 7000008 * 2
def baseEnd_7000008 : Nat := 399374298813105963356395

theorem tailTrace_7000008 : CollatzResearch.WordTrace tailWord_7000008 prefixEnd_7000008 399374298813105963356395 := by
  unfold tailWord_7000008
  simp only [CollatzResearch.WordTrace]
  refine ⟨127655633212086998516200339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170207510949449331354933785 127655633212086998516200339)
  ·
    refine ⟨191483449818130497774300509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127655633212086998516200339 191483449818130497774300509)
    ·
      refine ⟨71806293681798936665362691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191483449818130497774300509 71806293681798936665362691)
      ·
        refine ⟨107709440522698404998044037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71806293681798936665362691 107709440522698404998044037)
        ·
          refine ⟨20195520098005950937133257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107709440522698404998044037 20195520098005950937133257)
          ·
            refine ⟨15146640073504463202849943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20195520098005950937133257 15146640073504463202849943)
            ·
              refine ⟨22719960110256694804274915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15146640073504463202849943 22719960110256694804274915)
              ·
                refine ⟨34079940165385042206412373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22719960110256694804274915 34079940165385042206412373)
                ·
                  refine ⟨399374298813105963356395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34079940165385042206412373 399374298813105963356395)
                  ·
                    rfl

theorem cell23_7000008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_7000008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000008 prefixEnd_7000008 := by exact prefixLift 7000008
  have htrace : WordTrace (prefixWord ++ tailWord_7000008) baseStart_7000008 baseEnd_7000008 := by
    simpa [prefixWord, tailWord_7000008, baseEnd_7000008] using wordTrace_append hprefix tailTrace_7000008
  have hstable : (prefixWord ++ tailWord_7000008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000008).length < 2 ^ (prefixWord ++ tailWord_7000008).sum := by decide
  have hdescent : baseEnd_7000008 < baseStart_7000008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000011 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_7000011 : Nat := 118140960795 + 7000011 * 2 ^ 59
def prefixEnd_7000011 : Nat := 4983230072969 + 3 ^ 40 * 7000011 * 2
def baseEnd_7000011 : Nat := 3594370229759917158470041

theorem tailTrace_7000011 : CollatzResearch.WordTrace tailWord_7000011 prefixEnd_7000011 3594370229759917158470041 := by
  unfold tailWord_7000011
  simp only [CollatzResearch.WordTrace]
  refine ⟨255311375843163128544759887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170207583895442085696506591 255311375843163128544759887)
  ·
    refine ⟨382967063764744692817139831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255311375843163128544759887 382967063764744692817139831)
    ·
      refine ⟨574450595647117039225709747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382967063764744692817139831 574450595647117039225709747)
      ·
        refine ⟨861675893470675558838564621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574450595647117039225709747 861675893470675558838564621)
        ·
          refine ⟨323128460051503334564461733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 861675893470675558838564621 323128460051503334564461733)
          ·
            refine ⟨60586586259656875230836575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323128460051503334564461733 60586586259656875230836575)
            ·
              refine ⟨90879879389485312846254863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60586586259656875230836575 90879879389485312846254863)
              ·
                refine ⟨136319819084227969269382295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90879879389485312846254863 136319819084227969269382295)
                ·
                  refine ⟨204479728626341953904073443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136319819084227969269382295 204479728626341953904073443)
                  ·
                    refine ⟨306719592939512930856110165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204479728626341953904073443 306719592939512930856110165)
                    ·
                      refine ⟨3594370229759917158470041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 306719592939512930856110165 3594370229759917158470041)
                      ·
                        rfl

theorem cell23_7000011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_7000011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000011 prefixEnd_7000011 := by exact prefixLift 7000011
  have htrace : WordTrace (prefixWord ++ tailWord_7000011) baseStart_7000011 baseEnd_7000011 := by
    simpa [prefixWord, tailWord_7000011, baseEnd_7000011] using wordTrace_append hprefix tailTrace_7000011
  have hstable : (prefixWord ++ tailWord_7000011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000011).length < 2 ^ (prefixWord ++ tailWord_7000011).sum := by decide
  have hdescent : baseEnd_7000011 < baseStart_7000011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000012 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_7000012 : Nat := 118140960795 + 7000012 * 2 ^ 59
def prefixEnd_7000012 : Nat := 4983230072969 + 3 ^ 40 * 7000012 * 2
def baseEnd_7000012 : Nat := 1198123581080190551519179

theorem tailTrace_7000012 : CollatzResearch.WordTrace tailWord_7000012 prefixEnd_7000012 1198123581080190551519179 := by
  unfold tailWord_7000012
  simp only [CollatzResearch.WordTrace]
  refine ⟨127655706158079752857773145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170207608210773003810364193 127655706158079752857773145)
  ·
    refine ⟨95741779618559814643329859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127655706158079752857773145 95741779618559814643329859)
    ·
      refine ⟨143612669427839721964994789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95741779618559814643329859 143612669427839721964994789)
      ·
        refine ⟨26927375517719947868436523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143612669427839721964994789 26927375517719947868436523)
        ·
          refine ⟨40391063276579921802654785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26927375517719947868436523 40391063276579921802654785)
          ·
            refine ⟨30293297457434941351991089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40391063276579921802654785 30293297457434941351991089)
            ·
              refine ⟨22719973093076206013993317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30293297457434941351991089 22719973093076206013993317)
              ·
                refine ⟨4259994954951788627623747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22719973093076206013993317 4259994954951788627623747)
                ·
                  refine ⟨6389992432427682941435621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259994954951788627623747 6389992432427682941435621)
                  ·
                    refine ⟨1198123581080190551519179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389992432427682941435621 1198123581080190551519179)
                    ·
                      rfl

theorem cell23_7000012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_7000012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000012 prefixEnd_7000012 := by exact prefixLift 7000012
  have htrace : WordTrace (prefixWord ++ tailWord_7000012) baseStart_7000012 baseEnd_7000012 := by
    simpa [prefixWord, tailWord_7000012, baseEnd_7000012] using wordTrace_append hprefix tailTrace_7000012
  have hstable : (prefixWord ++ tailWord_7000012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000012).length < 2 ^ (prefixWord ++ tailWord_7000012).sum := by decide
  have hdescent : baseEnd_7000012 < baseStart_7000012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000058 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_7000058 : Nat := 118140960795 + 7000058 * 2 ^ 59
def prefixEnd_7000058 : Nat := 4983230072969 + 3 ^ 40 * 7000058 * 2
def baseEnd_7000058 : Nat := 3594394363350678474582325

theorem tailTrace_7000058 : CollatzResearch.WordTrace tailWord_7000058 prefixEnd_7000058 3594394363350678474582325 := by
  unfold tailWord_7000058
  simp only [CollatzResearch.WordTrace]
  refine ⟨63828272518498213892930207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170208726715995237047813885 63828272518498213892930207)
  ·
    refine ⟨95742408777747320839395311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63828272518498213892930207 95742408777747320839395311)
    ·
      refine ⟨143613613166620981259092967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95742408777747320839395311 143613613166620981259092967)
      ·
        refine ⟨215420419749931471888639451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143613613166620981259092967 215420419749931471888639451)
        ·
          refine ⟨323130629624897207832959177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215420419749931471888639451 323130629624897207832959177)
          ·
            refine ⟨242347972218672905874719383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323130629624897207832959177 242347972218672905874719383)
            ·
              refine ⟨363521958328009358812079075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242347972218672905874719383 363521958328009358812079075)
              ·
                refine ⟨545282937492014038218118613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363521958328009358812079075 545282937492014038218118613)
                ·
                  refine ⟨12780068847469079020737155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 545282937492014038218118613 12780068847469079020737155)
                  ·
                    refine ⟨19170103271203618531105733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12780068847469079020737155 19170103271203618531105733)
                    ·
                      refine ⟨3594394363350678474582325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19170103271203618531105733 3594394363350678474582325)
                      ·
                        rfl

theorem cell23_7000058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_7000058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000058 prefixEnd_7000058 := by exact prefixLift 7000058
  have htrace : WordTrace (prefixWord ++ tailWord_7000058) baseStart_7000058 baseEnd_7000058 := by
    simpa [prefixWord, tailWord_7000058, baseEnd_7000058] using wordTrace_append hprefix tailTrace_7000058
  have hstable : (prefixWord ++ tailWord_7000058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000058).length < 2 ^ (prefixWord ++ tailWord_7000058).sum := by decide
  have hdescent : baseEnd_7000058 < baseStart_7000058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000088 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7000088 : Nat := 118140960795 + 7000088 * 2 ^ 59
def prefixEnd_7000088 : Nat := 4983230072969 + 3 ^ 40 * 7000088 * 2
def baseEnd_7000088 : Nat := 3594409767770313357207187

theorem tailTrace_7000088 : CollatzResearch.WordTrace tailWord_7000088 prefixEnd_7000088 3594409767770313357207187 := by
  unfold tailWord_7000088
  simp only [CollatzResearch.WordTrace]
  refine ⟨127657092131942085347656459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170209456175922780463541945 127657092131942085347656459)
  ·
    refine ⟨191485638197913128021484689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127657092131942085347656459 191485638197913128021484689)
    ·
      refine ⟨143614228648434846016113517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191485638197913128021484689 143614228648434846016113517)
      ·
        refine ⟨53855335743163067256042569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143614228648434846016113517 53855335743163067256042569)
        ·
          refine ⟨40391501807372300442031927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53855335743163067256042569 40391501807372300442031927)
          ·
            refine ⟨60587252711058450663047891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40391501807372300442031927 60587252711058450663047891)
            ·
              refine ⟨90880879066587675994571837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60587252711058450663047891 90880879066587675994571837)
              ·
                refine ⟨34080329649970378497964439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90880879066587675994571837 34080329649970378497964439)
                ·
                  refine ⟨51120494474955567746946659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34080329649970378497964439 51120494474955567746946659)
                  ·
                    refine ⟨76680741712433351620419989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51120494474955567746946659 76680741712433351620419989)
                    ·
                      refine ⟨3594409767770313357207187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76680741712433351620419989 3594409767770313357207187)
                      ·
                        rfl

theorem cell23_7000088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7000088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000088 prefixEnd_7000088 := by exact prefixLift 7000088
  have htrace : WordTrace (prefixWord ++ tailWord_7000088) baseStart_7000088 baseEnd_7000088 := by
    simpa [prefixWord, tailWord_7000088, baseEnd_7000088] using wordTrace_append hprefix tailTrace_7000088
  have hstable : (prefixWord ++ tailWord_7000088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000088).length < 2 ^ (prefixWord ++ tailWord_7000088).sum := by decide
  have hdescent : baseEnd_7000088 < baseStart_7000088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000092 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_7000092 : Nat := 118140960795 + 7000092 * 2 ^ 59
def prefixEnd_7000092 : Nat := 4983230072969 + 3 ^ 40 * 7000092 * 2
def baseEnd_7000092 : Nat := 3594411821692931341557169

theorem tailTrace_7000092 : CollatzResearch.WordTrace tailWord_7000092 prefixEnd_7000092 3594411821692931341557169 := by
  unfold tailWord_7000092
  simp only [CollatzResearch.WordTrace]
  refine ⟨127657165077934839689229265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170209553437246452918972353 127657165077934839689229265)
  ·
    refine ⟨95742873808451129766921949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127657165077934839689229265 95742873808451129766921949)
    ·
      refine ⟨35903577678169173662595731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95742873808451129766921949 35903577678169173662595731)
      ·
        refine ⟨53855366517253760493893597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35903577678169173662595731 53855366517253760493893597)
        ·
          refine ⟨20195762443970160185210099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53855366517253760493893597 20195762443970160185210099)
          ·
            refine ⟨30293643665955240277815149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20195762443970160185210099 30293643665955240277815149)
            ·
              refine ⟨11360116374733215104180681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30293643665955240277815149 11360116374733215104180681)
              ·
                refine ⟨8520087281049911328135511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11360116374733215104180681 8520087281049911328135511)
                ·
                  refine ⟨12780130921574866992203267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8520087281049911328135511 12780130921574866992203267)
                  ·
                    refine ⟨19170196382362300488304901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12780130921574866992203267 19170196382362300488304901)
                    ·
                      refine ⟨3594411821692931341557169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19170196382362300488304901 3594411821692931341557169)
                      ·
                        rfl

theorem cell23_7000092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_7000092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000092 prefixEnd_7000092 := by exact prefixLift 7000092
  have htrace : WordTrace (prefixWord ++ tailWord_7000092) baseStart_7000092 baseEnd_7000092 := by
    simpa [prefixWord, tailWord_7000092, baseEnd_7000092] using wordTrace_append hprefix tailTrace_7000092
  have hstable : (prefixWord ++ tailWord_7000092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000092).length < 2 ^ (prefixWord ++ tailWord_7000092).sum := by decide
  have hdescent : baseEnd_7000092 < baseStart_7000092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000095 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_7000095 : Nat := 118140960795 + 7000095 * 2 ^ 59
def prefixEnd_7000095 : Nat := 4983230072969 + 3 ^ 40 * 7000095 * 2
def baseEnd_7000095 : Nat := 3594413362134894829819655

theorem tailTrace_7000095 : CollatzResearch.WordTrace tailWord_7000095 prefixEnd_7000095 3594413362134894829819655 := by
  unfold tailWord_7000095
  simp only [CollatzResearch.WordTrace]
  refine ⟨255314439574858810890817739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170209626383239207260545159 255314439574858810890817739)
  ·
    refine ⟨382971659362288216336226609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255314439574858810890817739 382971659362288216336226609)
    ·
      refine ⟨287228744521716162252169957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382971659362288216336226609 287228744521716162252169957)
      ·
        refine ⟨53855389597821780422281867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287228744521716162252169957 53855389597821780422281867)
        ·
          refine ⟨80783084396732670633422801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53855389597821780422281867 80783084396732670633422801)
          ·
            refine ⟨60587313297549502975067101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80783084396732670633422801 60587313297549502975067101)
            ·
              refine ⟨22720242486581063615650163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60587313297549502975067101 22720242486581063615650163)
              ·
                refine ⟨34080363729871595423475245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22720242486581063615650163 34080363729871595423475245)
                ·
                  refine ⟨12780136398701848283803217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34080363729871595423475245 12780136398701848283803217)
                  ·
                    refine ⟨9585102299026386212852413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12780136398701848283803217 9585102299026386212852413)
                    ·
                      refine ⟨3594413362134894829819655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585102299026386212852413 3594413362134894829819655)
                      ·
                        rfl

theorem cell23_7000095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_7000095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000095 prefixEnd_7000095 := by exact prefixLift 7000095
  have htrace : WordTrace (prefixWord ++ tailWord_7000095) baseStart_7000095 baseEnd_7000095 := by
    simpa [prefixWord, tailWord_7000095, baseEnd_7000095] using wordTrace_append hprefix tailTrace_7000095
  have hstable : (prefixWord ++ tailWord_7000095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000095).length < 2 ^ (prefixWord ++ tailWord_7000095).sum := by decide
  have hdescent : baseEnd_7000095 < baseStart_7000095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000098 : List Nat := [3, 3, 1, 1, 1, 2, 1, 11]
def baseStart_7000098 : Nat := 118140960795 + 7000098 * 2 ^ 59
def prefixEnd_7000098 : Nat := 4983230072969 + 3 ^ 40 * 7000098 * 2
def baseEnd_7000098 : Nat := 133126477873216974743783

theorem tailTrace_7000098 : CollatzResearch.WordTrace tailWord_7000098 prefixEnd_7000098 133126477873216974743783 := by
  unfold tailWord_7000098
  simp only [CollatzResearch.WordTrace]
  refine ⟨63828637248461985600794237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170209699329231961602117965 63828637248461985600794237)
  ·
    refine ⟨23935738968173244600297839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63828637248461985600794237 23935738968173244600297839)
    ·
      refine ⟨35903608452259866900446759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23935738968173244600297839 35903608452259866900446759)
      ·
        refine ⟨53855412678389800350670139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35903608452259866900446759 53855412678389800350670139)
        ·
          refine ⟨80783119017584700526005209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53855412678389800350670139 80783119017584700526005209)
          ·
            refine ⟨60587339263188525394503907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80783119017584700526005209 60587339263188525394503907)
            ·
              refine ⟨90881008894782788091755861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60587339263188525394503907 90881008894782788091755861)
              ·
                refine ⟨133126477873216974743783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90881008894782788091755861 133126477873216974743783)
                ·
                  rfl

theorem cell23_7000098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_7000098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000098 prefixEnd_7000098 := by exact prefixLift 7000098
  have htrace : WordTrace (prefixWord ++ tailWord_7000098) baseStart_7000098 baseEnd_7000098 := by
    simpa [prefixWord, tailWord_7000098, baseEnd_7000098] using wordTrace_append hprefix tailTrace_7000098
  have hstable : (prefixWord ++ tailWord_7000098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000098).length < 2 ^ (prefixWord ++ tailWord_7000098).sum := by decide
  have hdescent : baseEnd_7000098 < baseStart_7000098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000125 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_7000125 : Nat := 118140960795 + 7000125 * 2 ^ 59
def prefixEnd_7000125 : Nat := 4983230072969 + 3 ^ 40 * 7000125 * 2
def baseEnd_7000125 : Nat := 3594428766554529712444517

theorem tailTrace_7000125 : CollatzResearch.WordTrace tailWord_7000125 prefixEnd_7000125 3594428766554529712444517 := by
  unfold tailWord_7000125
  simp only [CollatzResearch.WordTrace]
  refine ⟨255315533764750126014409829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170210355843166750676273219 255315533764750126014409829)
  ·
    refine ⟨47871662580890648627701843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255315533764750126014409829 47871662580890648627701843)
    ·
      refine ⟨71807493871335972941552765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47871662580890648627701843 71807493871335972941552765)
      ·
        refine ⟨26927810201750989853082287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71807493871335972941552765 26927810201750989853082287)
        ·
          refine ⟨40391715302626484779623431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26927810201750989853082287 40391715302626484779623431)
          ·
            refine ⟨60587572953939727169435147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40391715302626484779623431 60587572953939727169435147)
            ·
              refine ⟨90881359430909590754152721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60587572953939727169435147 90881359430909590754152721)
              ·
                refine ⟨68161019573182193065614541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90881359430909590754152721 68161019573182193065614541)
                ·
                  refine ⟨25560382339943322399605453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68161019573182193065614541 25560382339943322399605453)
                  ·
                    refine ⟨9585143377478745899852045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25560382339943322399605453 9585143377478745899852045)
                    ·
                      refine ⟨3594428766554529712444517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585143377478745899852045 3594428766554529712444517)
                      ·
                        rfl

theorem cell23_7000125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_7000125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000125 prefixEnd_7000125 := by exact prefixLift 7000125
  have htrace : WordTrace (prefixWord ++ tailWord_7000125) baseStart_7000125 baseEnd_7000125 := by
    simpa [prefixWord, tailWord_7000125, baseEnd_7000125] using wordTrace_append hprefix tailTrace_7000125
  have hstable : (prefixWord ++ tailWord_7000125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000125).length < 2 ^ (prefixWord ++ tailWord_7000125).sum := by decide
  have hdescent : baseEnd_7000125 < baseStart_7000125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000128 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_7000128 : Nat := 118140960795 + 7000128 * 2 ^ 59
def prefixEnd_7000128 : Nat := 4983230072969 + 3 ^ 40 * 7000128 * 2
def baseEnd_7000128 : Nat := 1198143435665497733569001

theorem tailTrace_7000128 : CollatzResearch.WordTrace tailWord_7000128 prefixEnd_7000128 1198143435665497733569001 := by
  unfold tailWord_7000128
  simp only [CollatzResearch.WordTrace]
  refine ⟨127657821591869628763384519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170210428789159505017846025 127657821591869628763384519)
  ·
    refine ⟨191486732387804443145076779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127657821591869628763384519 191486732387804443145076779)
    ·
      refine ⟨287230098581706664717615169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191486732387804443145076779 287230098581706664717615169)
      ·
        refine ⟨215422573936279998538211377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287230098581706664717615169 215422573936279998538211377)
        ·
          refine ⟨161566930452209998903658533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215422573936279998538211377 161566930452209998903658533)
          ·
            refine ⟨30293799459789374794435975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161566930452209998903658533 30293799459789374794435975)
            ·
              refine ⟨45440699189684062191653963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30293799459789374794435975 45440699189684062191653963)
              ·
                refine ⟨68161048784526093287480945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45440699189684062191653963 68161048784526093287480945)
                ·
                  refine ⟨51120786588394569965610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68161048784526093287480945 51120786588394569965610709)
                  ·
                    refine ⟨1198143435665497733569001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51120786588394569965610709 1198143435665497733569001)
                    ·
                      rfl

theorem cell23_7000128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_7000128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000128 prefixEnd_7000128 := by exact prefixLift 7000128
  have htrace : WordTrace (prefixWord ++ tailWord_7000128) baseStart_7000128 baseEnd_7000128 := by
    simpa [prefixWord, tailWord_7000128, baseEnd_7000128] using wordTrace_append hprefix tailTrace_7000128
  have hstable : (prefixWord ++ tailWord_7000128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000128).length < 2 ^ (prefixWord ++ tailWord_7000128).sum := by decide
  have hdescent : baseEnd_7000128 < baseStart_7000128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000138 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_7000138 : Nat := 118140960795 + 7000138 * 2 ^ 59
def prefixEnd_7000138 : Nat := 4983230072969 + 3 ^ 40 * 7000138 * 2
def baseEnd_7000138 : Nat := 3594435441803038161581957

theorem tailTrace_7000138 : CollatzResearch.WordTrace tailWord_7000138 prefixEnd_7000138 3594435441803038161581957 := by
  unfold tailWord_7000138
  simp only [CollatzResearch.WordTrace]
  refine ⟨63829001978425757308658267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170210671942468686156422045 63829001978425757308658267)
  ·
    refine ⟨95743502967638635962987401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63829001978425757308658267 95743502967638635962987401)
    ·
      refine ⟨71807627225728976972240551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95743502967638635962987401 71807627225728976972240551)
      ·
        refine ⟨107711440838593465458360827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71807627225728976972240551 107711440838593465458360827)
        ·
          refine ⟨161567161257890198187541241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107711440838593465458360827 161567161257890198187541241)
          ·
            refine ⟨121175370943417648640655931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161567161257890198187541241 121175370943417648640655931)
            ·
              refine ⟨181763056415126472960983897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121175370943417648640655931 181763056415126472960983897)
              ·
                refine ⟨136322292311344854720737923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181763056415126472960983897 136322292311344854720737923)
                ·
                  refine ⟨204483438467017282081106885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136322292311344854720737923 204483438467017282081106885)
                  ·
                    refine ⟨38340644712565740390207541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204483438467017282081106885 38340644712565740390207541)
                    ·
                      refine ⟨3594435441803038161581957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38340644712565740390207541 3594435441803038161581957)
                      ·
                        rfl

theorem cell23_7000138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_7000138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000138 prefixEnd_7000138 := by exact prefixLift 7000138
  have htrace : WordTrace (prefixWord ++ tailWord_7000138) baseStart_7000138 baseEnd_7000138 := by
    simpa [prefixWord, tailWord_7000138, baseEnd_7000138] using wordTrace_append hprefix tailTrace_7000138
  have hstable : (prefixWord ++ tailWord_7000138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000138).length < 2 ^ (prefixWord ++ tailWord_7000138).sum := by decide
  have hdescent : baseEnd_7000138 < baseStart_7000138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000142 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_7000142 : Nat := 118140960795 + 7000142 * 2 ^ 59
def prefixEnd_7000142 : Nat := 4983230072969 + 3 ^ 40 * 7000142 * 2
def baseEnd_7000142 : Nat := 3594437495725656145931939

theorem tailTrace_7000142 : CollatzResearch.WordTrace tailWord_7000142 prefixEnd_7000142 3594437495725656145931939 := by
  unfold tailWord_7000142
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914519225711067239722335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170210769203792358611852453 31914519225711067239722335)
  ·
    refine ⟨47871778838566600859583503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31914519225711067239722335 47871778838566600859583503)
    ·
      refine ⟨71807668257849901289375255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47871778838566600859583503 71807668257849901289375255)
      ·
        refine ⟨107711502386774851934062883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71807668257849901289375255 107711502386774851934062883)
        ·
          refine ⟨161567253580162277901094325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107711502386774851934062883 161567253580162277901094325)
          ·
            refine ⟨15146930023140213553227593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161567253580162277901094325 15146930023140213553227593)
            ·
              refine ⟨11360197517355160164920695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15146930023140213553227593 11360197517355160164920695)
              ·
                refine ⟨17040296276032740247381043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11360197517355160164920695 17040296276032740247381043)
                ·
                  refine ⟨25560444414049110371071565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17040296276032740247381043 25560444414049110371071565)
                  ·
                    refine ⟨9585166655268416389151837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25560444414049110371071565 9585166655268416389151837)
                    ·
                      refine ⟨3594437495725656145931939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585166655268416389151837 3594437495725656145931939)
                      ·
                        rfl

theorem cell23_7000142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_7000142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000142 prefixEnd_7000142 := by exact prefixLift 7000142
  have htrace : WordTrace (prefixWord ++ tailWord_7000142) baseStart_7000142 baseEnd_7000142 := by
    simpa [prefixWord, tailWord_7000142, baseEnd_7000142] using wordTrace_append hprefix tailTrace_7000142
  have hstable : (prefixWord ++ tailWord_7000142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000142).length < 2 ^ (prefixWord ++ tailWord_7000142).sum := by decide
  have hdescent : baseEnd_7000142 < baseStart_7000142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000152 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 3, 3, 2]
def baseStart_7000152 : Nat := 118140960795 + 7000152 * 2 ^ 59
def prefixEnd_7000152 : Nat := 4983230072969 + 3 ^ 40 * 7000152 * 2
def baseEnd_7000152 : Nat := 3594442630532201106806893

theorem tailTrace_7000152 : CollatzResearch.WordTrace tailWord_7000152 prefixEnd_7000152 3594442630532201106806893 := by
  unfold tailWord_7000152
  simp only [CollatzResearch.WordTrace]
  refine ⟨127658259267826154812821355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170211012357101539750428473 127658259267826154812821355)
  ·
    refine ⟨191487388901739232219232033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127658259267826154812821355 191487388901739232219232033)
    ·
      refine ⟨143615541676304424164424025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191487388901739232219232033 143615541676304424164424025)
      ·
        refine ⟨107711656257228318123318019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143615541676304424164424025 107711656257228318123318019)
        ·
          refine ⟨161567484385842477184977029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107711656257228318123318019 161567484385842477184977029)
          ·
            refine ⟨30293903322345464472183193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161567484385842477184977029 30293903322345464472183193)
            ·
              refine ⟨22720427491759098354137395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30293903322345464472183193 22720427491759098354137395)
              ·
                refine ⟨34080641237638647531206093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22720427491759098354137395 34080641237638647531206093)
                ·
                  refine ⟨12780240464114492824202285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34080641237638647531206093 12780240464114492824202285)
                  ·
                    refine ⟨4792590174042934809075857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12780240464114492824202285 4792590174042934809075857)
                    ·
                      refine ⟨3594442630532201106806893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792590174042934809075857 3594442630532201106806893)
                      ·
                        rfl

theorem cell23_7000152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_7000152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000152 prefixEnd_7000152 := by exact prefixLift 7000152
  have htrace : WordTrace (prefixWord ++ tailWord_7000152) baseStart_7000152 baseEnd_7000152 := by
    simpa [prefixWord, tailWord_7000152, baseEnd_7000152] using wordTrace_append hprefix tailTrace_7000152
  have hstable : (prefixWord ++ tailWord_7000152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000152).length < 2 ^ (prefixWord ++ tailWord_7000152).sum := by decide
  have hdescent : baseEnd_7000152 < baseStart_7000152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000195 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4]
def baseStart_7000195 : Nat := 118140960795 + 7000195 * 2 ^ 59
def prefixEnd_7000195 : Nat := 4983230072969 + 3 ^ 40 * 7000195 * 2
def baseEnd_7000195 : Nat := 3594464710200344438569195

theorem tailTrace_7000195 : CollatzResearch.WordTrace tailWord_7000195 prefixEnd_7000195 3594464710200344438569195 := by
  unfold tailWord_7000195
  simp only [CollatzResearch.WordTrace]
  refine ⟨255318086874496527969458039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170212057916331018646305359 255318086874496527969458039)
  ·
    refine ⟨382977130311744791954187059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255318086874496527969458039 382977130311744791954187059)
    ·
      refine ⟨574465695467617187931280589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382977130311744791954187059 574465695467617187931280589)
      ·
        refine ⟨215424635800356445474230221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574465695467617187931280589 215424635800356445474230221)
        ·
          refine ⟨80784238425133667052836333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215424635800356445474230221 80784238425133667052836333)
          ·
            refine ⟨30294089409425125144813625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80784238425133667052836333 30294089409425125144813625)
            ·
              refine ⟨22720567057068843858610219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30294089409425125144813625 22720567057068843858610219)
              ·
                refine ⟨34080850585603265787915329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22720567057068843858610219 34080850585603265787915329)
                ·
                  refine ⟨25560637939202449340936497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34080850585603265787915329 25560637939202449340936497)
                  ·
                    refine ⟨19170478454401837005702373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25560637939202449340936497 19170478454401837005702373)
                    ·
                      refine ⟨3594464710200344438569195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19170478454401837005702373 3594464710200344438569195)
                      ·
                        rfl

theorem cell23_7000195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_7000195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000195 prefixEnd_7000195 := by exact prefixLift 7000195
  have htrace : WordTrace (prefixWord ++ tailWord_7000195) baseStart_7000195 baseEnd_7000195 := by
    simpa [prefixWord, tailWord_7000195, baseEnd_7000195] using wordTrace_append hprefix tailTrace_7000195
  have hstable : (prefixWord ++ tailWord_7000195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000195).length < 2 ^ (prefixWord ++ tailWord_7000195).sum := by decide
  have hdescent : baseEnd_7000195 < baseStart_7000195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000199 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_7000199 : Nat := 118140960795 + 7000199 * 2 ^ 59
def prefixEnd_7000199 : Nat := 4983230072969 + 3 ^ 40 * 7000199 * 2
def baseEnd_7000199 : Nat := 3594466764122962422919177

theorem tailTrace_7000199 : CollatzResearch.WordTrace tailWord_7000199 prefixEnd_7000199 3594466764122962422919177 := by
  unfold tailWord_7000199
  simp only [CollatzResearch.WordTrace]
  refine ⟨255318232766482036652603651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170212155177654691101735767 255318232766482036652603651)
  ·
    refine ⟨382977349149723054978905477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255318232766482036652603651 382977349149723054978905477)
    ·
      refine ⟨71808252965573072808544777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382977349149723054978905477 71808252965573072808544777)
      ·
        refine ⟨53856189724179804606408583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71808252965573072808544777 53856189724179804606408583)
        ·
          refine ⟨80784284586269706909612875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53856189724179804606408583 80784284586269706909612875)
          ·
            refine ⟨121176426879404560364419313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80784284586269706909612875 121176426879404560364419313)
            ·
              refine ⟨90882320159553420273314485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121176426879404560364419313 90882320159553420273314485)
              ·
                refine ⟨8520217514958133150623233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90882320159553420273314485 8520217514958133150623233)
                ·
                  refine ⟨6390163136218599862967425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8520217514958133150623233 6390163136218599862967425)
                  ·
                    refine ⟨4792622352163949897225569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6390163136218599862967425 4792622352163949897225569)
                    ·
                      refine ⟨3594466764122962422919177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792622352163949897225569 3594466764122962422919177)
                      ·
                        rfl

theorem cell23_7000199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_7000199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000199 prefixEnd_7000199 := by exact prefixLift 7000199
  have htrace : WordTrace (prefixWord ++ tailWord_7000199) baseStart_7000199 baseEnd_7000199 := by
    simpa [prefixWord, tailWord_7000199, baseEnd_7000199] using wordTrace_append hprefix tailTrace_7000199
  have hstable : (prefixWord ++ tailWord_7000199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000199).length < 2 ^ (prefixWord ++ tailWord_7000199).sum := by decide
  have hdescent : baseEnd_7000199 < baseStart_7000199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000242 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_7000242 : Nat := 118140960795 + 7000242 * 2 ^ 59
def prefixEnd_7000242 : Nat := 4983230072969 + 3 ^ 40 * 7000242 * 2
def baseEnd_7000242 : Nat := 3594488843791105754681479

theorem tailTrace_7000242 : CollatzResearch.WordTrace tailWord_7000242 prefixEnd_7000242 3594488843791105754681479 := by
  unfold tailWord_7000242
  simp only [CollatzResearch.WordTrace]
  refine ⟨63829950276331563749104745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170213200736884169997612653 63829950276331563749104745)
  ·
    refine ⟨47872462707248672811828559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63829950276331563749104745 47872462707248672811828559)
    ·
      refine ⟨71808694060873009217742839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47872462707248672811828559 71808694060873009217742839)
      ·
        refine ⟨107713041091309513826614259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71808694060873009217742839 107713041091309513826614259)
        ·
          refine ⟨161569561636964270739921389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107713041091309513826614259 161569561636964270739921389)
          ·
            refine ⟨60588585613861601527470521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161569561636964270739921389 60588585613861601527470521)
            ·
              refine ⟨45441439210396201145602891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60588585613861601527470521 45441439210396201145602891)
              ·
                refine ⟨68162158815594301718404337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45441439210396201145602891 68162158815594301718404337)
                ·
                  refine ⟨51121619111695726288803253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68162158815594301718404337 51121619111695726288803253)
                  ·
                    refine ⟨4792651791721474339575305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51121619111695726288803253 4792651791721474339575305)
                    ·
                      refine ⟨3594488843791105754681479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792651791721474339575305 3594488843791105754681479)
                      ·
                        rfl

theorem cell23_7000242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_7000242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000242 prefixEnd_7000242 := by exact prefixLift 7000242
  have htrace : WordTrace (prefixWord ++ tailWord_7000242) baseStart_7000242 baseEnd_7000242 := by
    simpa [prefixWord, tailWord_7000242, baseEnd_7000242] using wordTrace_append hprefix tailTrace_7000242
  have hstable : (prefixWord ++ tailWord_7000242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000242).length < 2 ^ (prefixWord ++ tailWord_7000242).sum := by decide
  have hdescent : baseEnd_7000242 < baseStart_7000242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000244 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7000244 : Nat := 118140960795 + 7000244 * 2 ^ 59
def prefixEnd_7000244 : Nat := 4983230072969 + 3 ^ 40 * 7000244 * 2
def baseEnd_7000244 : Nat := 3594489870752414746856471

theorem tailTrace_7000244 : CollatzResearch.WordTrace tailWord_7000244 prefixEnd_7000244 3594489870752414746856471 := by
  unfold tailWord_7000244
  simp only [CollatzResearch.WordTrace]
  refine ⟨127659937025659504668995893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170213249367546006225327857 127659937025659504668995893)
  ·
    refine ⟨11968119096155578562718365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127659937025659504668995893 11968119096155578562718365)
    ·
      refine ⟨4488044661058341961019387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11968119096155578562718365 4488044661058341961019387)
      ·
        refine ⟨6732066991587512941529081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4488044661058341961019387 6732066991587512941529081)
        ·
          refine ⟨5049050243690634706146811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6732066991587512941529081 5049050243690634706146811)
          ·
            refine ⟨7573575365535952059220217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049050243690634706146811 7573575365535952059220217)
            ·
              refine ⟨5680181524151964044415163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573575365535952059220217 5680181524151964044415163)
              ·
                refine ⟨8520272286227946066622745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680181524151964044415163 8520272286227946066622745)
                ·
                  refine ⟨6390204214670959549967059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8520272286227946066622745 6390204214670959549967059)
                  ·
                    refine ⟨9585306322006439324950589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390204214670959549967059 9585306322006439324950589)
                    ·
                      refine ⟨3594489870752414746856471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585306322006439324950589 3594489870752414746856471)
                      ·
                        rfl

theorem cell23_7000244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7000244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000244 prefixEnd_7000244 := by exact prefixLift 7000244
  have htrace : WordTrace (prefixWord ++ tailWord_7000244) baseStart_7000244 baseEnd_7000244 := by
    simpa [prefixWord, tailWord_7000244, baseEnd_7000244] using wordTrace_append hprefix tailTrace_7000244
  have hstable : (prefixWord ++ tailWord_7000244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000244).length < 2 ^ (prefixWord ++ tailWord_7000244).sum := by decide
  have hdescent : baseEnd_7000244 < baseStart_7000244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000255 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_7000255 : Nat := 118140960795 + 7000255 * 2 ^ 59
def prefixEnd_7000255 : Nat := 4983230072969 + 3 ^ 40 * 7000255 * 2
def baseEnd_7000255 : Nat := 3594495519039614203818919

theorem tailTrace_7000255 : CollatzResearch.WordTrace tailWord_7000255 prefixEnd_7000255 3594495519039614203818919 := by
  unfold tailWord_7000255
  simp only [CollatzResearch.WordTrace]
  refine ⟨255320275254279158216642219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170213516836186105477761479 255320275254279158216642219)
  ·
    refine ⟨382980412881418737324963329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255320275254279158216642219 382980412881418737324963329)
    ·
      refine ⟨287235309661064052993722497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382980412881418737324963329 287235309661064052993722497)
      ·
        refine ⟨215426482245798039745291873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287235309661064052993722497 215426482245798039745291873)
        ·
          refine ⟨161569861684348529808968905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215426482245798039745291873 161569861684348529808968905)
          ·
            refine ⟨121177396263261397356726679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161569861684348529808968905 121177396263261397356726679)
            ·
              refine ⟨181766094394892096035090019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121177396263261397356726679 181766094394892096035090019)
              ·
                refine ⟨272649141592338144052635029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181766094394892096035090019 272649141592338144052635029)
                ·
                  refine ⟨12780428512140850502467267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 272649141592338144052635029 12780428512140850502467267)
                  ·
                    refine ⟨19170642768211275753700901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12780428512140850502467267 19170642768211275753700901)
                    ·
                      refine ⟨3594495519039614203818919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19170642768211275753700901 3594495519039614203818919)
                      ·
                        rfl

theorem cell23_7000255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_7000255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000255 prefixEnd_7000255 := by exact prefixLift 7000255
  have htrace : WordTrace (prefixWord ++ tailWord_7000255) baseStart_7000255 baseEnd_7000255 := by
    simpa [prefixWord, tailWord_7000255, baseEnd_7000255] using wordTrace_append hprefix tailTrace_7000255
  have hstable : (prefixWord ++ tailWord_7000255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000255).length < 2 ^ (prefixWord ++ tailWord_7000255).sum := by decide
  have hdescent : baseEnd_7000255 < baseStart_7000255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000299 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 1, 4]
def baseStart_7000299 : Nat := 118140960795 + 7000299 * 2 ^ 59
def prefixEnd_7000299 : Nat := 4983230072969 + 3 ^ 40 * 7000299 * 2
def baseEnd_7000299 : Nat := 1198172704062804010556239

theorem tailTrace_7000299 : CollatzResearch.WordTrace tailWord_7000299 prefixEnd_7000299 1198172704062804010556239 := by
  unfold tailWord_7000299
  simp only [CollatzResearch.WordTrace]
  refine ⟨255321880066119753731243951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170214586710746502487495967 255321880066119753731243951)
  ·
    refine ⟨382982820099179630596865927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255321880066119753731243951 382982820099179630596865927)
    ·
      refine ⟨574474230148769445895298891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382982820099179630596865927 574474230148769445895298891)
      ·
        refine ⟨861711345223154168842948337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574474230148769445895298891 861711345223154168842948337)
        ·
          refine ⟨646283508917365626632211253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861711345223154168842948337 646283508917365626632211253)
          ·
            refine ⟨60589078961003027496769805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 646283508917365626632211253 60589078961003027496769805)
            ·
              refine ⟨22720904610376135311288677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60589078961003027496769805 22720904610376135311288677)
              ·
                refine ⟨4260169614445525370866627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22720904610376135311288677 4260169614445525370866627)
                ·
                  refine ⟨6390254421668288056299941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260169614445525370866627 6390254421668288056299941)
                  ·
                    refine ⟨1198172704062804010556239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390254421668288056299941 1198172704062804010556239)
                    ·
                      rfl

theorem cell23_7000299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 4].length) (baseStart_7000299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000299 prefixEnd_7000299 := by exact prefixLift 7000299
  have htrace : WordTrace (prefixWord ++ tailWord_7000299) baseStart_7000299 baseEnd_7000299 := by
    simpa [prefixWord, tailWord_7000299, baseEnd_7000299] using wordTrace_append hprefix tailTrace_7000299
  have hstable : (prefixWord ++ tailWord_7000299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000299).length < 2 ^ (prefixWord ++ tailWord_7000299).sum := by decide
  have hdescent : baseEnd_7000299 < baseStart_7000299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000346 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_7000346 : Nat := 118140960795 + 7000346 * 2 ^ 59
def prefixEnd_7000346 : Nat := 4983230072969 + 3 ^ 40 * 7000346 * 2
def baseEnd_7000346 : Nat := 399393582864352594197889

theorem tailTrace_7000346 : CollatzResearch.WordTrace tailWord_7000346 prefixEnd_7000346 399393582864352594197889 := by
  unfold tailWord_7000346
  simp only [CollatzResearch.WordTrace]
  refine ⟨63830898574237370189551223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170215729531299653838803261 63830898574237370189551223)
  ·
    refine ⟨95746347861356055284326835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63830898574237370189551223 95746347861356055284326835)
    ·
      refine ⟨143619521792034082926490253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95746347861356055284326835 143619521792034082926490253)
      ·
        refine ⟨53857320672012781097433845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143619521792034082926490253 53857320672012781097433845)
        ·
          refine ⟨5049123813001198227884423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53857320672012781097433845 5049123813001198227884423)
          ·
            refine ⟨7573685719501797341826635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049123813001198227884423 7573685719501797341826635)
            ·
              refine ⟨11360528579252696012739953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573685719501797341826635 11360528579252696012739953)
              ·
                refine ⟨8520396434439522009554965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11360528579252696012739953 8520396434439522009554965)
                ·
                  refine ⟨399393582864352594197889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8520396434439522009554965 399393582864352594197889)
                  ·
                    rfl

theorem cell23_7000346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_7000346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000346 prefixEnd_7000346 := by exact prefixLift 7000346
  have htrace : WordTrace (prefixWord ++ tailWord_7000346) baseStart_7000346 baseEnd_7000346 := by
    simpa [prefixWord, tailWord_7000346, baseEnd_7000346] using wordTrace_append hprefix tailTrace_7000346
  have hstable : (prefixWord ++ tailWord_7000346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000346).length < 2 ^ (prefixWord ++ tailWord_7000346).sum := by decide
  have hdescent : baseEnd_7000346 < baseStart_7000346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000356 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_7000356 : Nat := 118140960795 + 7000356 * 2 ^ 59
def prefixEnd_7000356 : Nat := 4983230072969 + 3 ^ 40 * 7000356 * 2
def baseEnd_7000356 : Nat := 3594547380585718308655955

theorem tailTrace_7000356 : CollatzResearch.WordTrace tailWord_7000356 prefixEnd_7000356 3594547380585718308655955 := by
  unfold tailWord_7000356
  simp only [CollatzResearch.WordTrace]
  refine ⟨127661979513456626233034461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170215972684608834977379281 127661979513456626233034461)
  ·
    refine ⟨47873242317546234837387923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127661979513456626233034461 47873242317546234837387923)
    ·
      refine ⟨71809863476319352256081885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47873242317546234837387923 71809863476319352256081885)
      ·
        refine ⟨26928698803619757096030707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71809863476319352256081885 26928698803619757096030707)
        ·
          refine ⟨40393048205429635644046061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26928698803619757096030707 40393048205429635644046061)
          ·
            refine ⟨15147393077036113366517273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40393048205429635644046061 15147393077036113366517273)
            ·
              refine ⟨11360544807777085024887955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15147393077036113366517273 11360544807777085024887955)
              ·
                refine ⟨17040817211665627537331933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11360544807777085024887955 17040817211665627537331933)
                ·
                  refine ⟨6390306454374610326499475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17040817211665627537331933 6390306454374610326499475)
                  ·
                    refine ⟨9585459681561915489749213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390306454374610326499475 9585459681561915489749213)
                    ·
                      refine ⟨3594547380585718308655955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585459681561915489749213 3594547380585718308655955)
                      ·
                        rfl

theorem cell23_7000356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_7000356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000356 prefixEnd_7000356 := by exact prefixLift 7000356
  have htrace : WordTrace (prefixWord ++ tailWord_7000356) baseStart_7000356 baseEnd_7000356 := by
    simpa [prefixWord, tailWord_7000356, baseEnd_7000356] using wordTrace_append hprefix tailTrace_7000356
  have hstable : (prefixWord ++ tailWord_7000356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000356).length < 2 ^ (prefixWord ++ tailWord_7000356).sum := by decide
  have hdescent : baseEnd_7000356 < baseStart_7000356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000392 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_7000392 : Nat := 118140960795 + 7000392 * 2 ^ 59
def prefixEnd_7000392 : Nat := 4983230072969 + 3 ^ 40 * 7000392 * 2
def baseEnd_7000392 : Nat := 3594565865889280167805789

theorem tailTrace_7000392 : CollatzResearch.WordTrace tailWord_7000392 prefixEnd_7000392 3594565865889280167805789 := by
  unfold tailWord_7000392
  simp only [CollatzResearch.WordTrace]
  refine ⟨127662636027391415307189715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170216848036521887076252953 127662636027391415307189715)
  ·
    refine ⟨191493954041087122960784573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127662636027391415307189715 191493954041087122960784573)
    ·
      refine ⟨71810232765407671110294215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191493954041087122960784573 71810232765407671110294215)
      ·
        refine ⟨107715349148111506665441323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71810232765407671110294215 107715349148111506665441323)
        ·
          refine ⟨161573023722167259998161985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107715349148111506665441323 161573023722167259998161985)
          ·
            refine ⟨121179767791625444998621489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161573023722167259998161985 121179767791625444998621489)
            ·
              refine ⟨90884825843719083748966117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121179767791625444998621489 90884825843719083748966117)
              ·
                refine ⟨17040904845697328202931147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90884825843719083748966117 17040904845697328202931147)
                ·
                  refine ⟨25561357268545992304396721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17040904845697328202931147 25561357268545992304396721)
                  ·
                    refine ⟨19171017951409494228297541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25561357268545992304396721 19171017951409494228297541)
                    ·
                      refine ⟨3594565865889280167805789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19171017951409494228297541 3594565865889280167805789)
                      ·
                        rfl

theorem cell23_7000392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_7000392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000392 prefixEnd_7000392 := by exact prefixLift 7000392
  have htrace : WordTrace (prefixWord ++ tailWord_7000392) baseStart_7000392 baseEnd_7000392 := by
    simpa [prefixWord, tailWord_7000392, baseEnd_7000392] using wordTrace_append hprefix tailTrace_7000392
  have hstable : (prefixWord ++ tailWord_7000392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000392).length < 2 ^ (prefixWord ++ tailWord_7000392).sum := by decide
  have hdescent : baseEnd_7000392 < baseStart_7000392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000414 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7000414 : Nat := 118140960795 + 7000414 * 2 ^ 59
def prefixEnd_7000414 : Nat := 4983230072969 + 3 ^ 40 * 7000414 * 2
def baseEnd_7000414 : Nat := 399397462495964342414521

theorem tailTrace_7000414 : CollatzResearch.WordTrace tailWord_7000414 prefixEnd_7000414 399397462495964342414521 := by
  unfold tailWord_7000414
  simp only [CollatzResearch.WordTrace]
  refine ⟨31915759307587891046460037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170217382973802085581120197 31915759307587891046460037)
  ·
    refine ⟨5984204870172729571211257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31915759307587891046460037 5984204870172729571211257)
    ·
      refine ⟨4488153652629547178408443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5984204870172729571211257 4488153652629547178408443)
      ·
        refine ⟨6732230478944320767612665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4488153652629547178408443 6732230478944320767612665)
        ·
          refine ⟨5049172859208240575709499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6732230478944320767612665 5049172859208240575709499)
          ·
            refine ⟨7573759288812360863564249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049172859208240575709499 7573759288812360863564249)
            ·
              refine ⟨5680319466609270647673187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573759288812360863564249 5680319466609270647673187)
              ·
                refine ⟨8520479199913905971509781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680319466609270647673187 8520479199913905971509781)
                ·
                  refine ⟨399397462495964342414521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8520479199913905971509781 399397462495964342414521)
                  ·
                    rfl

theorem cell23_7000414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7000414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000414 prefixEnd_7000414 := by exact prefixLift 7000414
  have htrace : WordTrace (prefixWord ++ tailWord_7000414) baseStart_7000414 baseEnd_7000414 := by
    simpa [prefixWord, tailWord_7000414, baseEnd_7000414] using wordTrace_append hprefix tailTrace_7000414
  have hstable : (prefixWord ++ tailWord_7000414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000414).length < 2 ^ (prefixWord ++ tailWord_7000414).sum := by decide
  have hdescent : baseEnd_7000414 < baseStart_7000414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000423 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 2, 4]
def baseStart_7000423 : Nat := 118140960795 + 7000423 * 2 ^ 59
def prefixEnd_7000423 : Nat := 4983230072969 + 3 ^ 40 * 7000423 * 2
def baseEnd_7000423 : Nat := 1198193927929856515506049

theorem tailTrace_7000423 : CollatzResearch.WordTrace tailWord_7000423 prefixEnd_7000423 1198193927929856515506049 := by
  unfold tailWord_7000423
  simp only [CollatzResearch.WordTrace]
  refine ⟨255326402717670522908757923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170217601811780348605838615 255326402717670522908757923)
  ·
    refine ⟨382989604076505784363136885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255326402717670522908757923 382989604076505784363136885)
    ·
      refine ⟨35905275382172417284044083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382989604076505784363136885 35905275382172417284044083)
      ·
        refine ⟨53857913073258625926066125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35905275382172417284044083 53857913073258625926066125)
        ·
          refine ⟨20196717402471984722274797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53857913073258625926066125 20196717402471984722274797)
          ·
            refine ⟨7573769025926994270853049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20196717402471984722274797 7573769025926994270853049)
            ·
              refine ⟨5680326769445245703139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573769025926994270853049 5680326769445245703139787)
              ·
                refine ⟨8520490154167868554709681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680326769445245703139787 8520490154167868554709681)
                ·
                  refine ⟨6390367615625901416032261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8520490154167868554709681 6390367615625901416032261)
                  ·
                    refine ⟨1198193927929856515506049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390367615625901416032261 1198193927929856515506049)
                    ·
                      rfl

theorem cell23_7000423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_7000423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000423 prefixEnd_7000423 := by exact prefixLift 7000423
  have htrace : WordTrace (prefixWord ++ tailWord_7000423) baseStart_7000423 baseEnd_7000423 := by
    simpa [prefixWord, tailWord_7000423, baseEnd_7000423] using wordTrace_append hprefix tailTrace_7000423
  have hstable : (prefixWord ++ tailWord_7000423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000423).length < 2 ^ (prefixWord ++ tailWord_7000423).sum := by decide
  have hdescent : baseEnd_7000423 < baseStart_7000423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000429 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7000429 : Nat := 118140960795 + 7000429 * 2 ^ 59
def prefixEnd_7000429 : Nat := 4983230072969 + 3 ^ 40 * 7000429 * 2
def baseEnd_7000429 : Nat := 3594584864673496523043119

theorem tailTrace_7000429 : CollatzResearch.WordTrace tailWord_7000429 prefixEnd_7000429 3594584864673496523043119 := by
  unfold tailWord_7000429
  simp only [CollatzResearch.WordTrace]
  refine ⟨255326621555648785933476341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170217747703765857288984227 255326621555648785933476341)
  ·
    refine ⟨23936870770842073681263407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255326621555648785933476341 23936870770842073681263407)
    ·
      refine ⟨35905306156263110521895111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23936870770842073681263407 35905306156263110521895111)
      ·
        refine ⟨53857959234394665782842667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35905306156263110521895111 53857959234394665782842667)
        ·
          refine ⟨80786938851591998674264001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53857959234394665782842667 80786938851591998674264001)
          ·
            refine ⟨60590204138693999005698001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80786938851591998674264001 60590204138693999005698001)
            ·
              refine ⟨45442653104020499254273501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60590204138693999005698001 45442653104020499254273501)
              ·
                refine ⟨17040994914007687220352563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45442653104020499254273501 17040994914007687220352563)
                ·
                  refine ⟨25561492371011530830528845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17040994914007687220352563 25561492371011530830528845)
                  ·
                    refine ⟨9585559639129324061448317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25561492371011530830528845 9585559639129324061448317)
                    ·
                      refine ⟨3594584864673496523043119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585559639129324061448317 3594584864673496523043119)
                      ·
                        rfl

theorem cell23_7000429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7000429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000429 prefixEnd_7000429 := by exact prefixLift 7000429
  have htrace : WordTrace (prefixWord ++ tailWord_7000429) baseStart_7000429 baseEnd_7000429 := by
    simpa [prefixWord, tailWord_7000429, baseEnd_7000429] using wordTrace_append hprefix tailTrace_7000429
  have hstable : (prefixWord ++ tailWord_7000429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000429).length < 2 ^ (prefixWord ++ tailWord_7000429).sum := by decide
  have hdescent : baseEnd_7000429 < baseStart_7000429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000450 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7000450 : Nat := 118140960795 + 7000450 * 2 ^ 59
def prefixEnd_7000450 : Nat := 4983230072969 + 3 ^ 40 * 7000450 * 2
def baseEnd_7000450 : Nat := 3594595647767240940880523

theorem tailTrace_7000450 : CollatzResearch.WordTrace tailWord_7000450 prefixEnd_7000450 3594595647767240940880523 := by
  unfold tailWord_7000450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63831846872143176629997701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170218258325715137679993869 63831846872143176629997701)
  ·
    refine ⟨11968471288526845618124569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63831846872143176629997701 11968471288526845618124569)
    ·
      refine ⟨8976353466395134213593427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11968471288526845618124569 8976353466395134213593427)
      ·
        refine ⟨13464530199592701320390141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976353466395134213593427 13464530199592701320390141)
        ·
          refine ⟨5049198824847262995146303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13464530199592701320390141 5049198824847262995146303)
          ·
            refine ⟨7573798237270894492719455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049198824847262995146303 7573798237270894492719455)
            ·
              refine ⟨11360697355906341739079183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573798237270894492719455 11360697355906341739079183)
              ·
                refine ⟨17041046033859512608618775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11360697355906341739079183 17041046033859512608618775)
                ·
                  refine ⟨25561569050789268912928163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17041046033859512608618775 25561569050789268912928163)
                  ·
                    refine ⟨38342353576183903369392245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25561569050789268912928163 38342353576183903369392245)
                    ·
                      refine ⟨3594595647767240940880523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38342353576183903369392245 3594595647767240940880523)
                      ·
                        rfl

theorem cell23_7000450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7000450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000450 prefixEnd_7000450 := by exact prefixLift 7000450
  have htrace : WordTrace (prefixWord ++ tailWord_7000450) baseStart_7000450 baseEnd_7000450 := by
    simpa [prefixWord, tailWord_7000450, baseEnd_7000450] using wordTrace_append hprefix tailTrace_7000450
  have hstable : (prefixWord ++ tailWord_7000450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000450).length < 2 ^ (prefixWord ++ tailWord_7000450).sum := by decide
  have hdescent : baseEnd_7000450 < baseStart_7000450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000469 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_7000469 : Nat := 118140960795 + 7000469 * 2 ^ 59
def prefixEnd_7000469 : Nat := 4983230072969 + 3 ^ 40 * 7000469 * 2
def baseEnd_7000469 : Nat := 3594605403899676366542935

theorem tailTrace_7000469 : CollatzResearch.WordTrace tailWord_7000469 prefixEnd_7000469 3594605403899676366542935 := by
  unfold tailWord_7000469
  simp only [CollatzResearch.WordTrace]
  refine ⟨255328080475503872764932461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170218720317002581843288307 255328080475503872764932461)
  ·
    refine ⟨95748030178313952286849673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255328080475503872764932461 95748030178313952286849673)
    ·
      refine ⟨71811022633735464215137255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95748030178313952286849673 71811022633735464215137255)
      ·
        refine ⟨107716533950603196322705883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71811022633735464215137255 107716533950603196322705883)
        ·
          refine ⟨161574800925904794484058825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107716533950603196322705883 161574800925904794484058825)
          ·
            refine ⟨121181100694428595863044119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161574800925904794484058825 121181100694428595863044119)
            ·
              refine ⟨181771651041642893794566179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121181100694428595863044119 181771651041642893794566179)
              ·
                refine ⟨272657476562464340691849269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181771651041642893794566179 272657476562464340691849269)
                ·
                  refine ⟨25561638427731031939860869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272657476562464340691849269 25561638427731031939860869)
                  ·
                    refine ⟨4792807205199568488723913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25561638427731031939860869 4792807205199568488723913)
                    ·
                      refine ⟨3594605403899676366542935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792807205199568488723913 3594605403899676366542935)
                      ·
                        rfl

theorem cell23_7000469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_7000469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000469 prefixEnd_7000469 := by exact prefixLift 7000469
  have htrace : WordTrace (prefixWord ++ tailWord_7000469) baseStart_7000469 baseEnd_7000469 := by
    simpa [prefixWord, tailWord_7000469, baseEnd_7000469] using wordTrace_append hprefix tailTrace_7000469
  have hstable : (prefixWord ++ tailWord_7000469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000469).length < 2 ^ (prefixWord ++ tailWord_7000469).sum := by decide
  have hdescent : baseEnd_7000469 < baseStart_7000469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000470 : List Nat := [5, 3, 1, 2, 1, 2, 1, 8]
def baseStart_7000470 : Nat := 118140960795 + 7000470 * 2 ^ 59
def prefixEnd_7000470 : Nat := 4983230072969 + 3 ^ 40 * 7000470 * 2
def baseEnd_7000470 : Nat := 133133552495567809727053

theorem tailTrace_7000470 : CollatzResearch.WordTrace tailWord_7000470 prefixEnd_7000470 133133552495567809727053 := by
  unfold tailWord_7000470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958007309281265620982429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170218744632333499957145909 15958007309281265620982429)
  ·
    refine ⟨5984252740980474607868411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15958007309281265620982429 5984252740980474607868411)
    ·
      refine ⟨8976379111470711911802617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5984252740980474607868411 8976379111470711911802617)
      ·
        refine ⟨6732284333603033933851963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8976379111470711911802617 6732284333603033933851963)
        ·
          refine ⟨10098426500404550900777945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6732284333603033933851963 10098426500404550900777945)
          ·
            refine ⟨7573819875303413175583459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10098426500404550900777945 7573819875303413175583459)
            ·
              refine ⟨11360729812955119763375189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573819875303413175583459 11360729812955119763375189)
              ·
                refine ⟨133133552495567809727053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11360729812955119763375189 133133552495567809727053)
                ·
                  rfl

theorem cell23_7000470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_7000470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000470 prefixEnd_7000470 := by exact prefixLift 7000470
  have htrace : WordTrace (prefixWord ++ tailWord_7000470) baseStart_7000470 baseEnd_7000470 := by
    simpa [prefixWord, tailWord_7000470, baseEnd_7000470] using wordTrace_append hprefix tailTrace_7000470
  have hstable : (prefixWord ++ tailWord_7000470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000470).length < 2 ^ (prefixWord ++ tailWord_7000470).sum := by decide
  have hdescent : baseEnd_7000470 < baseStart_7000470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000519 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_7000519 : Nat := 118140960795 + 7000519 * 2 ^ 59
def prefixEnd_7000519 : Nat := 4983230072969 + 3 ^ 40 * 7000519 * 2
def baseEnd_7000519 : Nat := 3594631077932401170917705

theorem tailTrace_7000519 : CollatzResearch.WordTrace tailWord_7000519 prefixEnd_7000519 3594631077932401170917705 := by
  unfold tailWord_7000519
  simp only [CollatzResearch.WordTrace]
  refine ⟨255329904125322731304252611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170219936083548487536168407 255329904125322731304252611)
  ·
    refine ⟨382994856187984096956378917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255329904125322731304252611 382994856187984096956378917)
    ·
      refine ⟨71811535535247018179321047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382994856187984096956378917 71811535535247018179321047)
      ·
        refine ⟨107717303302870527268981571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71811535535247018179321047 107717303302870527268981571)
        ·
          refine ⟨161575954954305790903472357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107717303302870527268981571 161575954954305790903472357)
          ·
            refine ⟨30295491553932335794401067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161575954954305790903472357 30295491553932335794401067)
            ·
              refine ⟨45443237330898503691601601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30295491553932335794401067 45443237330898503691601601)
              ·
                refine ⟨34082427998173877768701201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45443237330898503691601601 34082427998173877768701201)
                ·
                  refine ⟨25561820998630408326525901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34082427998173877768701201 25561820998630408326525901)
                  ·
                    refine ⟨9585682874486403122447213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25561820998630408326525901 9585682874486403122447213)
                    ·
                      refine ⟨3594631077932401170917705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585682874486403122447213 3594631077932401170917705)
                      ·
                        rfl

theorem cell23_7000519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_7000519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000519 prefixEnd_7000519 := by exact prefixLift 7000519
  have htrace : WordTrace (prefixWord ++ tailWord_7000519) baseStart_7000519 baseEnd_7000519 := by
    simpa [prefixWord, tailWord_7000519, baseEnd_7000519] using wordTrace_append hprefix tailTrace_7000519
  have hstable : (prefixWord ++ tailWord_7000519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000519).length < 2 ^ (prefixWord ++ tailWord_7000519).sum := by decide
  have hdescent : baseEnd_7000519 < baseStart_7000519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000520 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_7000520 : Nat := 118140960795 + 7000520 * 2 ^ 59
def prefixEnd_7000520 : Nat := 4983230072969 + 3 ^ 40 * 7000520 * 2
def baseEnd_7000520 : Nat := 3594631591413055667005201

theorem tailTrace_7000520 : CollatzResearch.WordTrace tailWord_7000520 prefixEnd_7000520 3594631591413055667005201 := by
  unfold tailWord_7000520
  simp only [CollatzResearch.WordTrace]
  refine ⟨127664970299159554237519507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170219960398879405650026009 127664970299159554237519507)
  ·
    refine ⟨191497455448739331356279261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127664970299159554237519507 191497455448739331356279261)
    ·
      refine ⟨71811545793277249258604723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191497455448739331356279261 71811545793277249258604723)
      ·
        refine ⟨107717318689915873887907085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71811545793277249258604723 107717318689915873887907085)
        ·
          refine ⟨40393994508718452707965157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107717318689915873887907085 40393994508718452707965157)
          ·
            refine ⟨7573873970384709882743467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40393994508718452707965157 7573873970384709882743467)
            ·
              refine ⟨11360810955577064824115201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573873970384709882743467 11360810955577064824115201)
              ·
                refine ⟨8520608216682798618086401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11360810955577064824115201 8520608216682798618086401)
                ·
                  refine ⟨6390456162512098963564801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8520608216682798618086401 6390456162512098963564801)
                  ·
                    refine ⟨4792842121884074222673601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6390456162512098963564801 4792842121884074222673601)
                    ·
                      refine ⟨3594631591413055667005201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792842121884074222673601 3594631591413055667005201)
                      ·
                        rfl

theorem cell23_7000520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_7000520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000520 prefixEnd_7000520 := by exact prefixLift 7000520
  have htrace : WordTrace (prefixWord ++ tailWord_7000520) baseStart_7000520 baseEnd_7000520 := by
    simpa [prefixWord, tailWord_7000520, baseEnd_7000520] using wordTrace_append hprefix tailTrace_7000520
  have hstable : (prefixWord ++ tailWord_7000520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000520).length < 2 ^ (prefixWord ++ tailWord_7000520).sum := by decide
  have hdescent : baseEnd_7000520 < baseStart_7000520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000529 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 7, 2]
def baseStart_7000529 : Nat := 118140960795 + 7000529 * 2 ^ 59
def prefixEnd_7000529 : Nat := 4983230072969 + 3 ^ 40 * 7000529 * 2
def baseEnd_7000529 : Nat := 3594636212738946131792659

theorem tailTrace_7000529 : CollatzResearch.WordTrace tailWord_7000529 prefixEnd_7000529 3594636212738946131792659 := by
  unfold tailWord_7000529
  simp only [CollatzResearch.WordTrace]
  refine ⟨255330268855286503012116641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170220179236857668674744427 255330268855286503012116641)
  ·
    refine ⟨191497701641464877259087481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255330268855286503012116641 191497701641464877259087481)
    ·
      refine ⟨143623276231098657944315611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191497701641464877259087481 143623276231098657944315611)
      ·
        refine ⟨215434914346647986916473417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143623276231098657944315611 215434914346647986916473417)
        ·
          refine ⟨161576185759985990187355063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215434914346647986916473417 161576185759985990187355063)
          ·
            refine ⟨242364278639978985281032595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161576185759985990187355063 242364278639978985281032595)
            ·
              refine ⟨363546417959968477921548893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242364278639978985281032595 363546417959968477921548893)
              ·
                refine ⟨136329906734988179220580835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363546417959968477921548893 136329906734988179220580835)
                ·
                  refine ⟨204494860102482268830871253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136329906734988179220580835 204494860102482268830871253)
                  ·
                    refine ⟨4792848283651928175723545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 204494860102482268830871253 4792848283651928175723545)
                    ·
                      refine ⟨3594636212738946131792659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4792848283651928175723545 3594636212738946131792659)
                      ·
                        rfl

theorem cell23_7000529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_7000529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000529 prefixEnd_7000529 := by exact prefixLift 7000529
  have htrace : WordTrace (prefixWord ++ tailWord_7000529) baseStart_7000529 baseEnd_7000529 := by
    simpa [prefixWord, tailWord_7000529, baseEnd_7000529] using wordTrace_append hprefix tailTrace_7000529
  have hstable : (prefixWord ++ tailWord_7000529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000529).length < 2 ^ (prefixWord ++ tailWord_7000529).sum := by decide
  have hdescent : baseEnd_7000529 < baseStart_7000529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000559 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_7000559 : Nat := 118140960795 + 7000559 * 2 ^ 59
def prefixEnd_7000559 : Nat := 4983230072969 + 3 ^ 40 * 7000559 * 2
def baseEnd_7000559 : Nat := 3594651617158581014417521

theorem tailTrace_7000559 : CollatzResearch.WordTrace tailWord_7000559 prefixEnd_7000559 3594651617158581014417521 := by
  unfold tailWord_7000559
  simp only [CollatzResearch.WordTrace]
  refine ⟨255331363045177818135708731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170220908696785212090472487 255331363045177818135708731)
  ·
    refine ⟨382997044567766727203563097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255331363045177818135708731 382997044567766727203563097)
    ·
      refine ⟨287247783425825045402672323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382997044567766727203563097 287247783425825045402672323)
      ·
        refine ⟨430871675138737568104008485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287247783425825045402672323 430871675138737568104008485)
        ·
          refine ⟨80788439088513294019501591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430871675138737568104008485 80788439088513294019501591)
          ·
            refine ⟨121182658632769941029252387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80788439088513294019501591 121182658632769941029252387)
            ·
              refine ⟨181773987949154911543878581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121182658632769941029252387 181773987949154911543878581)
              ·
                refine ⟨17041311370233272957238617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181773987949154911543878581 17041311370233272957238617)
                ·
                  refine ⟨12780983527674954717928963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17041311370233272957238617 12780983527674954717928963)
                  ·
                    refine ⟨19171475291512432076893445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12780983527674954717928963 19171475291512432076893445)
                    ·
                      refine ⟨3594651617158581014417521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19171475291512432076893445 3594651617158581014417521)
                      ·
                        rfl

theorem cell23_7000559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_7000559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000559 prefixEnd_7000559 := by exact prefixLift 7000559
  have htrace : WordTrace (prefixWord ++ tailWord_7000559) baseStart_7000559 baseEnd_7000559 := by
    simpa [prefixWord, tailWord_7000559, baseEnd_7000559] using wordTrace_append hprefix tailTrace_7000559
  have hstable : (prefixWord ++ tailWord_7000559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000559).length < 2 ^ (prefixWord ++ tailWord_7000559).sum := by decide
  have hdescent : baseEnd_7000559 < baseStart_7000559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000569 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 5, 4]
def baseStart_7000569 : Nat := 118140960795 + 7000569 * 2 ^ 59
def prefixEnd_7000569 : Nat := 4983230072969 + 3 ^ 40 * 7000569 * 2
def baseEnd_7000569 : Nat := 1198218917321708658430825

theorem tailTrace_7000569 : CollatzResearch.WordTrace tailWord_7000569 prefixEnd_7000569 1198218917321708658430825 := by
  unfold tailWord_7000569
  simp only [CollatzResearch.WordTrace]
  refine ⟨255331727775141589843572761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170221151850094393229048507 255331727775141589843572761)
  ·
    refine ⟨191498795831356192382679571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255331727775141589843572761 191498795831356192382679571)
    ·
      refine ⟨287248193747034288574019357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191498795831356192382679571 287248193747034288574019357)
      ·
        refine ⟨107718072655137858215257259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287248193747034288574019357 107718072655137858215257259)
        ·
          refine ⟨161577108982706787322885889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107718072655137858215257259 161577108982706787322885889)
          ·
            refine ⟨121182831737030090492164417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161577108982706787322885889 121182831737030090492164417)
            ·
              refine ⟨90887123802772567869123313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121182831737030090492164417 90887123802772567869123313)
              ·
                refine ⟨68165342852079425901842485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90887123802772567869123313 68165342852079425901842485)
                ·
                  refine ⟨6390500892382446178297733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68165342852079425901842485 6390500892382446178297733)
                  ·
                    refine ⟨1198218917321708658430825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390500892382446178297733 1198218917321708658430825)
                    ·
                      rfl

theorem cell23_7000569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_7000569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000569 prefixEnd_7000569 := by exact prefixLift 7000569
  have htrace : WordTrace (prefixWord ++ tailWord_7000569) baseStart_7000569 baseEnd_7000569 := by
    simpa [prefixWord, tailWord_7000569, baseEnd_7000569] using wordTrace_append hprefix tailTrace_7000569
  have hstable : (prefixWord ++ tailWord_7000569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000569).length < 2 ^ (prefixWord ++ tailWord_7000569).sum := by decide
  have hdescent : baseEnd_7000569 < baseStart_7000569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000592 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_7000592 : Nat := 118140960795 + 7000592 * 2 ^ 59
def prefixEnd_7000592 : Nat := 4983230072969 + 3 ^ 40 * 7000592 * 2
def baseEnd_7000592 : Nat := 3594668562020179385304869

theorem tailTrace_7000592 : CollatzResearch.WordTrace tailWord_7000592 prefixEnd_7000592 3594668562020179385304869 := by
  unfold tailWord_7000592
  simp only [CollatzResearch.WordTrace]
  refine ⟨127666283327029132385830015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170221711102705509847773353 127666283327029132385830015)
  ·
    refine ⟨191499424990543698578745023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127666283327029132385830015 191499424990543698578745023)
    ·
      refine ⟨287249137485815547868117535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191499424990543698578745023 287249137485815547868117535)
      ·
        refine ⟨430873706228723321802176303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287249137485815547868117535 430873706228723321802176303)
        ·
          refine ⟨646310559343084982703264455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430873706228723321802176303 646310559343084982703264455)
          ·
            refine ⟨969465839014627474054896683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646310559343084982703264455 969465839014627474054896683)
            ·
              refine ⟨1454198758521941211082345025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969465839014627474054896683 1454198758521941211082345025)
              ·
                refine ⟨1090649068891455908311758769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454198758521941211082345025 1090649068891455908311758769)
                ·
                  refine ⟨817986801668591931233819077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1090649068891455908311758769 817986801668591931233819077)
                  ·
                    refine ⟨153372525312860987106341077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 817986801668591931233819077 153372525312860987106341077)
                    ·
                      refine ⟨3594668562020179385304869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153372525312860987106341077 3594668562020179385304869)
                      ·
                        rfl

theorem cell23_7000592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_7000592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000592 prefixEnd_7000592 := by exact prefixLift 7000592
  have htrace : WordTrace (prefixWord ++ tailWord_7000592) baseStart_7000592 baseEnd_7000592 := by
    simpa [prefixWord, tailWord_7000592, baseEnd_7000592] using wordTrace_append hprefix tailTrace_7000592
  have hstable : (prefixWord ++ tailWord_7000592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000592).length < 2 ^ (prefixWord ++ tailWord_7000592).sum := by decide
  have hdescent : baseEnd_7000592 < baseStart_7000592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000637 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_7000637 : Nat := 118140960795 + 7000637 * 2 ^ 59
def prefixEnd_7000637 : Nat := 4983230072969 + 3 ^ 40 * 7000637 * 2
def baseEnd_7000637 : Nat := 1198230556216543903080721

theorem tailTrace_7000637 : CollatzResearch.WordTrace tailWord_7000637 prefixEnd_7000637 1198230556216543903080721 := by
  unfold tailWord_7000637
  simp only [CollatzResearch.WordTrace]
  refine ⟨255334207938895237457048165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170222805292596824971365443 255334207938895237457048165)
  ·
    refine ⟨47875163988542857023196531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255334207938895237457048165 47875163988542857023196531)
    ·
      refine ⟨71812745982814285534794797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47875163988542857023196531 71812745982814285534794797)
      ·
        refine ⟨26929779743555357075548049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71812745982814285534794797 26929779743555357075548049)
        ·
          refine ⟨20197334807666517806661037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26929779743555357075548049 20197334807666517806661037)
          ·
            refine ⟨7574000552874944177497889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20197334807666517806661037 7574000552874944177497889)
            ·
              refine ⟨5680500414656208133123417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574000552874944177497889 5680500414656208133123417)
              ·
                refine ⟨4260375310992156099842563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680500414656208133123417 4260375310992156099842563)
                ·
                  refine ⟨6390562966488234149763845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260375310992156099842563 6390562966488234149763845)
                  ·
                    refine ⟨1198230556216543903080721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390562966488234149763845 1198230556216543903080721)
                    ·
                      rfl

theorem cell23_7000637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_7000637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000637 prefixEnd_7000637 := by exact prefixLift 7000637
  have htrace : WordTrace (prefixWord ++ tailWord_7000637) baseStart_7000637 baseEnd_7000637 := by
    simpa [prefixWord, tailWord_7000637, baseEnd_7000637] using wordTrace_append hprefix tailTrace_7000637
  have hstable : (prefixWord ++ tailWord_7000637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000637).length < 2 ^ (prefixWord ++ tailWord_7000637).sum := by decide
  have hdescent : baseEnd_7000637 < baseStart_7000637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000676 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_7000676 : Nat := 118140960795 + 7000676 * 2 ^ 59
def prefixEnd_7000676 : Nat := 4983230072969 + 3 ^ 40 * 7000676 * 2
def baseEnd_7000676 : Nat := 1198237231465052352218161

theorem tailTrace_7000676 : CollatzResearch.WordTrace tailWord_7000676 prefixEnd_7000676 1198237231465052352218161 := by
  unfold tailWord_7000676
  simp only [CollatzResearch.WordTrace]
  refine ⟨127667815192876973558858941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170223753590502631411811921 127667815192876973558858941)
  ·
    refine ⟨47875430697328865084572103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127667815192876973558858941 47875430697328865084572103)
    ·
      refine ⟨71813146045993297626858155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47875430697328865084572103 71813146045993297626858155)
      ·
        refine ⟨107719719068989946440287233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71813146045993297626858155 107719719068989946440287233)
        ·
          refine ⟨80789789301742459830215425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107719719068989946440287233 80789789301742459830215425)
          ·
            refine ⟨60592341976306844872661569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80789789301742459830215425 60592341976306844872661569)
            ·
              refine ⟨45444256482230133654496177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60592341976306844872661569 45444256482230133654496177)
              ·
                refine ⟨34083192361672600240872133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45444256482230133654496177 34083192361672600240872133)
                ·
                  refine ⟨6390598567813612545163525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34083192361672600240872133 6390598567813612545163525)
                  ·
                    refine ⟨1198237231465052352218161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390598567813612545163525 1198237231465052352218161)
                    ·
                      rfl

theorem cell23_7000676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_7000676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000676 prefixEnd_7000676 := by exact prefixLift 7000676
  have htrace : WordTrace (prefixWord ++ tailWord_7000676) baseStart_7000676 baseEnd_7000676 := by
    simpa [prefixWord, tailWord_7000676, baseEnd_7000676] using wordTrace_append hprefix tailTrace_7000676
  have hstable : (prefixWord ++ tailWord_7000676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000676).length < 2 ^ (prefixWord ++ tailWord_7000676).sum := by decide
  have hdescent : baseEnd_7000676 < baseStart_7000676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000677 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 1, 1, 3]
def baseStart_7000677 : Nat := 118140960795 + 7000677 * 2 ^ 59
def prefixEnd_7000677 : Nat := 4983230072969 + 3 ^ 40 * 7000677 * 2
def baseEnd_7000677 : Nat := 3594712207875811552741979

theorem tailTrace_7000677 : CollatzResearch.WordTrace tailWord_7000677 prefixEnd_7000677 3594712207875811552741979 := by
  unfold tailWord_7000677
  simp only [CollatzResearch.WordTrace]
  refine ⟨255335666858750324288504285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170223777905833549525669523 255335666858750324288504285)
  ·
    refine ⟨95750875072031371608189107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255335666858750324288504285 95750875072031371608189107)
    ·
      refine ⟨143626312608047057412283661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95750875072031371608189107 143626312608047057412283661)
      ·
        refine ⟨53859867228017646529606373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143626312608047057412283661 53859867228017646529606373)
        ·
          refine ⟨10098725105253308724301195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53859867228017646529606373 10098725105253308724301195)
          ·
            refine ⟨15148087657879963086451793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10098725105253308724301195 15148087657879963086451793)
            ·
              refine ⟨11361065743409972314838845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15148087657879963086451793 11361065743409972314838845)
              ·
                refine ⟨4260399653778739618064567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11361065743409972314838845 4260399653778739618064567)
                ·
                  refine ⟨6390599480668109427096851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260399653778739618064567 6390599480668109427096851)
                  ·
                    refine ⟨9585899221002164140645277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390599480668109427096851 9585899221002164140645277)
                    ·
                      refine ⟨3594712207875811552741979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585899221002164140645277 3594712207875811552741979)
                      ·
                        rfl

theorem cell23_7000677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_7000677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000677 prefixEnd_7000677 := by exact prefixLift 7000677
  have htrace : WordTrace (prefixWord ++ tailWord_7000677) baseStart_7000677 baseEnd_7000677 := by
    simpa [prefixWord, tailWord_7000677, baseEnd_7000677] using wordTrace_append hprefix tailTrace_7000677
  have hstable : (prefixWord ++ tailWord_7000677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000677).length < 2 ^ (prefixWord ++ tailWord_7000677).sum := by decide
  have hdescent : baseEnd_7000677 < baseStart_7000677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000679 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_7000679 : Nat := 118140960795 + 7000679 * 2 ^ 59
def prefixEnd_7000679 : Nat := 4983230072969 + 3 ^ 40 * 7000679 * 2
def baseEnd_7000679 : Nat := 3594713234837120544916969

theorem tailTrace_7000679 : CollatzResearch.WordTrace tailWord_7000679 prefixEnd_7000679 3594713234837120544916969 := by
  unfold tailWord_7000679
  simp only [CollatzResearch.WordTrace]
  refine ⟨255335739804743078630077091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170223826536495385753384727 255335739804743078630077091)
  ·
    refine ⟨383003609707114617945115637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255335739804743078630077091 383003609707114617945115637)
    ·
      refine ⟨35906588410041995432354591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383003609707114617945115637 35906588410041995432354591)
      ·
        refine ⟨53859882615062993148531887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35906588410041995432354591 53859882615062993148531887)
        ·
          refine ⟨80789823922594489722797831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53859882615062993148531887 80789823922594489722797831)
          ·
            refine ⟨121184735883891734584196747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80789823922594489722797831 121184735883891734584196747)
            ·
              refine ⟨181777103825837601876295121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121184735883891734584196747 181777103825837601876295121)
              ·
                refine ⟨136332827869378201407221341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181777103825837601876295121 136332827869378201407221341)
                ·
                  refine ⟨51124810451016825527708003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136332827869378201407221341 51124810451016825527708003)
                  ·
                    refine ⟨76687215676525238291562005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51124810451016825527708003 76687215676525238291562005)
                    ·
                      refine ⟨3594713234837120544916969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76687215676525238291562005 3594713234837120544916969)
                      ·
                        rfl

theorem cell23_7000679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_7000679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000679 prefixEnd_7000679 := by exact prefixLift 7000679
  have htrace : WordTrace (prefixWord ++ tailWord_7000679) baseStart_7000679 baseEnd_7000679 := by
    simpa [prefixWord, tailWord_7000679, baseEnd_7000679] using wordTrace_append hprefix tailTrace_7000679
  have hstable : (prefixWord ++ tailWord_7000679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000679).length < 2 ^ (prefixWord ++ tailWord_7000679).sum := by decide
  have hdescent : baseEnd_7000679 < baseStart_7000679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000716 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_7000716 : Nat := 118140960795 + 7000716 * 2 ^ 59
def prefixEnd_7000716 : Nat := 4983230072969 + 3 ^ 40 * 7000716 * 2
def baseEnd_7000716 : Nat := 3594732233621336900154299

theorem tailTrace_7000716 : CollatzResearch.WordTrace tailWord_7000716 prefixEnd_7000716 3594732233621336900154299 := by
  unfold tailWord_7000716
  simp only [CollatzResearch.WordTrace]
  refine ⟨127668544652804516974587001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170224726203739355966116001 127668544652804516974587001)
  ·
    refine ⟨95751408489603387730940251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127668544652804516974587001 95751408489603387730940251)
    ·
      refine ⟨143627112734405081596410377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95751408489603387730940251 143627112734405081596410377)
      ·
        refine ⟨107720334550803811197307783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143627112734405081596410377 107720334550803811197307783)
        ·
          refine ⟨161580501826205716795961675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107720334550803811197307783 161580501826205716795961675)
          ·
            refine ⟨242370752739308575193942513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161580501826205716795961675 242370752739308575193942513)
            ·
              refine ⟨181778064554481431395456885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242370752739308575193942513 181778064554481431395456885)
              ·
                refine ⟨17041693551982634193324083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181778064554481431395456885 17041693551982634193324083)
                ·
                  refine ⟨25562540327973951289986125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17041693551982634193324083 25562540327973951289986125)
                  ·
                    refine ⟨9585952622990231733744797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25562540327973951289986125 9585952622990231733744797)
                    ·
                      refine ⟨3594732233621336900154299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585952622990231733744797 3594732233621336900154299)
                      ·
                        rfl

theorem cell23_7000716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_7000716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000716 prefixEnd_7000716 := by exact prefixLift 7000716
  have htrace : WordTrace (prefixWord ++ tailWord_7000716) baseStart_7000716 baseEnd_7000716 := by
    simpa [prefixWord, tailWord_7000716, baseEnd_7000716] using wordTrace_append hprefix tailTrace_7000716
  have hstable : (prefixWord ++ tailWord_7000716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000716).length < 2 ^ (prefixWord ++ tailWord_7000716).sum := by decide
  have hdescent : baseEnd_7000716 < baseStart_7000716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000729 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_7000729 : Nat := 118140960795 + 7000729 * 2 ^ 59
def prefixEnd_7000729 : Nat := 4983230072969 + 3 ^ 40 * 7000729 * 2
def baseEnd_7000729 : Nat := 3594738908869845349291739

theorem tailTrace_7000729 : CollatzResearch.WordTrace tailWord_7000729 prefixEnd_7000729 3594738908869845349291739 := by
  unfold tailWord_7000729
  simp only [CollatzResearch.WordTrace]
  refine ⟨255337563454561937169397241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170225042303041291446264827 255337563454561937169397241)
  ·
    refine ⟨191503172590921452877047931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255337563454561937169397241 191503172590921452877047931)
    ·
      refine ⟨287254758886382179315571897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191503172590921452877047931 287254758886382179315571897)
      ·
        refine ⟨215441069164786634486678923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287254758886382179315571897 215441069164786634486678923)
        ·
          refine ⟨323161603747179951730018385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215441069164786634486678923 323161603747179951730018385)
          ·
            refine ⟨242371202810384963797513789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323161603747179951730018385 242371202810384963797513789)
            ·
              refine ⟨90889201053894361424067671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242371202810384963797513789 90889201053894361424067671)
              ·
                refine ⟨136333801580841542136101507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90889201053894361424067671 136333801580841542136101507)
                ·
                  refine ⟨204500702371262313204152261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136333801580841542136101507 204500702371262313204152261)
                  ·
                    refine ⟨38343881694611683725778549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204500702371262313204152261 38343881694611683725778549)
                    ·
                      refine ⟨3594738908869845349291739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38343881694611683725778549 3594738908869845349291739)
                      ·
                        rfl

theorem cell23_7000729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_7000729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000729 prefixEnd_7000729 := by exact prefixLift 7000729
  have htrace : WordTrace (prefixWord ++ tailWord_7000729) baseStart_7000729 baseEnd_7000729 := by
    simpa [prefixWord, tailWord_7000729, baseEnd_7000729] using wordTrace_append hprefix tailTrace_7000729
  have hstable : (prefixWord ++ tailWord_7000729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000729).length < 2 ^ (prefixWord ++ tailWord_7000729).sum := by decide
  have hdescent : baseEnd_7000729 < baseStart_7000729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000733 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_7000733 : Nat := 118140960795 + 7000733 * 2 ^ 59
def prefixEnd_7000733 : Nat := 4983230072969 + 3 ^ 40 * 7000733 * 2
def baseEnd_7000733 : Nat := 3594740962792463333641721

theorem tailTrace_7000733 : CollatzResearch.WordTrace tailWord_7000733 prefixEnd_7000733 3594740962792463333641721 := by
  unfold tailWord_7000733
  simp only [CollatzResearch.WordTrace]
  refine ⟨255337709346547445852542853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170225139564364963901695235 255337709346547445852542853)
  ·
    refine ⟨47875820502477646097351785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255337709346547445852542853 47875820502477646097351785)
    ·
      refine ⟨35906865376858234573013839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47875820502477646097351785 35906865376858234573013839)
      ·
        refine ⟨53860298065287351859520759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35906865376858234573013839 53860298065287351859520759)
        ·
          refine ⟨80790447097931027789281139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53860298065287351859520759 80790447097931027789281139)
          ·
            refine ⟨121185670646896541683921709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80790447097931027789281139 121185670646896541683921709)
            ·
              refine ⟨45444626492586203131470641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121185670646896541683921709 45444626492586203131470641)
              ·
                refine ⟨34083469869439652348602981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45444626492586203131470641 34083469869439652348602981)
                ·
                  refine ⟨6390650600519934815363059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34083469869439652348602981 6390650600519934815363059)
                  ·
                    refine ⟨9585975900779902223044589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390650600519934815363059 9585975900779902223044589)
                    ·
                      refine ⟨3594740962792463333641721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9585975900779902223044589 3594740962792463333641721)
                      ·
                        rfl

theorem cell23_7000733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_7000733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000733 prefixEnd_7000733 := by exact prefixLift 7000733
  have htrace : WordTrace (prefixWord ++ tailWord_7000733) baseStart_7000733 baseEnd_7000733 := by
    simpa [prefixWord, tailWord_7000733, baseEnd_7000733] using wordTrace_append hprefix tailTrace_7000733
  have hstable : (prefixWord ++ tailWord_7000733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000733).length < 2 ^ (prefixWord ++ tailWord_7000733).sum := by decide
  have hdescent : baseEnd_7000733 < baseStart_7000733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000766 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7000766 : Nat := 118140960795 + 7000766 * 2 ^ 59
def prefixEnd_7000766 : Nat := 4983230072969 + 3 ^ 40 * 7000766 * 2
def baseEnd_7000766 : Nat := 1198252635884687234843023

theorem tailTrace_7000766 : CollatzResearch.WordTrace tailWord_7000766 prefixEnd_7000766 1198252635884687234843023 := by
  unfold tailWord_7000766
  simp only [CollatzResearch.WordTrace]
  refine ⟨31917364119428486561061769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170225941970285261658996101 31917364119428486561061769)
  ·
    refine ⟨23938023089571364920796327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31917364119428486561061769 23938023089571364920796327)
    ·
      refine ⟨35907034634357047381194491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23938023089571364920796327 35907034634357047381194491)
      ·
        refine ⟨53860551951535571071791737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35907034634357047381194491 53860551951535571071791737)
        ·
          refine ⟨40395413963651678303843803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53860551951535571071791737 40395413963651678303843803)
          ·
            refine ⟨60593120945477517455765705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40395413963651678303843803 60593120945477517455765705)
            ·
              refine ⟨45444840709108138091824279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60593120945477517455765705 45444840709108138091824279)
              ·
                refine ⟨68167261063662207137736419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45444840709108138091824279 68167261063662207137736419)
                ·
                  refine ⟨102250891595493310706604629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68167261063662207137736419 102250891595493310706604629)
                  ·
                    refine ⟨1198252635884687234843023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102250891595493310706604629 1198252635884687234843023)
                    ·
                      rfl

theorem cell23_7000766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7000766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000766 prefixEnd_7000766 := by exact prefixLift 7000766
  have htrace : WordTrace (prefixWord ++ tailWord_7000766) baseStart_7000766 baseEnd_7000766 := by
    simpa [prefixWord, tailWord_7000766, baseEnd_7000766] using wordTrace_append hprefix tailTrace_7000766
  have hstable : (prefixWord ++ tailWord_7000766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000766).length < 2 ^ (prefixWord ++ tailWord_7000766).sum := by decide
  have hdescent : baseEnd_7000766 < baseStart_7000766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000767 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 2, 1, 3]
def baseStart_7000767 : Nat := 118140960795 + 7000767 * 2 ^ 59
def prefixEnd_7000767 : Nat := 4983230072969 + 3 ^ 40 * 7000767 * 2
def baseEnd_7000767 : Nat := 3594758421134716200616565

theorem tailTrace_7000767 : CollatzResearch.WordTrace tailWord_7000767 prefixEnd_7000767 3594758421134716200616565 := by
  unfold tailWord_7000767
  simp only [CollatzResearch.WordTrace]
  refine ⟨255338949428424269659280555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170225966285616179772853703 255338949428424269659280555)
  ·
    refine ⟨383008424142636404488920833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255338949428424269659280555 383008424142636404488920833)
    ·
      refine ⟨287256318106977303366690625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383008424142636404488920833 287256318106977303366690625)
      ·
        refine ⟨215442238580232977525017969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287256318106977303366690625 215442238580232977525017969)
        ·
          refine ⟨161581678935174733143763477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215442238580232977525017969 161581678935174733143763477)
          ·
            refine ⟨7574141200086315616113913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161581678935174733143763477 7574141200086315616113913)
            ·
              refine ⟨5680605900064736712085435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574141200086315616113913 5680605900064736712085435)
              ·
                refine ⟨8520908850097105068128153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680605900064736712085435 8520908850097105068128153)
                ·
                  refine ⟨6390681637572828801096115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8520908850097105068128153 6390681637572828801096115)
                  ·
                    refine ⟨9586022456359243201644173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390681637572828801096115 9586022456359243201644173)
                    ·
                      refine ⟨3594758421134716200616565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9586022456359243201644173 3594758421134716200616565)
                      ·
                        rfl

theorem cell23_7000767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_7000767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000767 prefixEnd_7000767 := by exact prefixLift 7000767
  have htrace : WordTrace (prefixWord ++ tailWord_7000767) baseStart_7000767 baseEnd_7000767 := by
    simpa [prefixWord, tailWord_7000767, baseEnd_7000767] using wordTrace_append hprefix tailTrace_7000767
  have hstable : (prefixWord ++ tailWord_7000767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000767).length < 2 ^ (prefixWord ++ tailWord_7000767).sum := by decide
  have hdescent : baseEnd_7000767 < baseStart_7000767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000776 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_7000776 : Nat := 118140960795 + 7000776 * 2 ^ 59
def prefixEnd_7000776 : Nat := 4983230072969 + 3 ^ 40 * 7000776 * 2
def baseEnd_7000776 : Nat := 3594763042460606665404023

theorem tailTrace_7000776 : CollatzResearch.WordTrace tailWord_7000776 prefixEnd_7000776 3594763042460606665404023 := by
  unfold tailWord_7000776
  simp only [CollatzResearch.WordTrace]
  refine ⟨127669638842695832098179091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170226185123594442797572121 127669638842695832098179091)
  ·
    refine ⟨191504458264043748147268637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127669638842695832098179091 191504458264043748147268637)
    ·
      refine ⟨71814171849016405555225739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191504458264043748147268637 71814171849016405555225739)
      ·
        refine ⟨107721257773524608332838609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71814171849016405555225739 107721257773524608332838609)
        ·
          refine ⟨80790943330143456249628957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107721257773524608332838609 80790943330143456249628957)
          ·
            refine ⟨30296603748803796093610859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80790943330143456249628957 30296603748803796093610859)
            ·
              refine ⟨45444905623205694140416289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30296603748803796093610859 45444905623205694140416289)
              ·
                refine ⟨34083679217404270605312217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45444905623205694140416289 34083679217404270605312217)
                ·
                  refine ⟨25562759413053202953984163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34083679217404270605312217 25562759413053202953984163)
                  ·
                    refine ⟨38344139119579804430976245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25562759413053202953984163 38344139119579804430976245)
                    ·
                      refine ⟨3594763042460606665404023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38344139119579804430976245 3594763042460606665404023)
                      ·
                        rfl

theorem cell23_7000776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_7000776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000776 prefixEnd_7000776 := by exact prefixLift 7000776
  have htrace : WordTrace (prefixWord ++ tailWord_7000776) baseStart_7000776 baseEnd_7000776 := by
    simpa [prefixWord, tailWord_7000776, baseEnd_7000776] using wordTrace_append hprefix tailTrace_7000776
  have hstable : (prefixWord ++ tailWord_7000776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000776).length < 2 ^ (prefixWord ++ tailWord_7000776).sum := by decide
  have hdescent : baseEnd_7000776 < baseStart_7000776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000826 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_7000826 : Nat := 118140960795 + 7000826 * 2 ^ 59
def prefixEnd_7000826 : Nat := 4983230072969 + 3 ^ 40 * 7000826 * 2
def baseEnd_7000826 : Nat := 1198262905497777156592931

theorem tailTrace_7000826 : CollatzResearch.WordTrace tailWord_7000826 prefixEnd_7000826 1198262905497777156592931 := by
  unfold tailWord_7000826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63835275333802630683919583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170227400890140348490452221 63835275333802630683919583)
  ·
    refine ⟨95752913000703946025879375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63835275333802630683919583 95752913000703946025879375)
    ·
      refine ⟨143629369501055919038819063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95752913000703946025879375 143629369501055919038819063)
      ·
        refine ⟨215444054251583878558228595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143629369501055919038819063 215444054251583878558228595)
        ·
          refine ⟨323166081377375817837342893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215444054251583878558228595 323166081377375817837342893)
          ·
            refine ⟨121187280516515931689003585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323166081377375817837342893 121187280516515931689003585)
            ·
              refine ⟨90890460387386948766752689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121187280516515931689003585 90890460387386948766752689)
              ·
                refine ⟨68167845290540211575064517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90890460387386948766752689 68167845290540211575064517)
                ·
                  refine ⟨12781470991976289670324597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68167845290540211575064517 12781470991976289670324597)
                  ·
                    refine ⟨1198262905497777156592931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12781470991976289670324597 1198262905497777156592931)
                    ·
                      rfl

theorem cell23_7000826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_7000826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000826 prefixEnd_7000826 := by exact prefixLift 7000826
  have htrace : WordTrace (prefixWord ++ tailWord_7000826) baseStart_7000826 baseEnd_7000826 := by
    simpa [prefixWord, tailWord_7000826, baseEnd_7000826] using wordTrace_append hprefix tailTrace_7000826
  have hstable : (prefixWord ++ tailWord_7000826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000826).length < 2 ^ (prefixWord ++ tailWord_7000826).sum := by decide
  have hdescent : baseEnd_7000826 < baseStart_7000826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000833 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_7000833 : Nat := 118140960795 + 7000833 * 2 ^ 59
def prefixEnd_7000833 : Nat := 4983230072969 + 3 ^ 40 * 7000833 * 2
def baseEnd_7000833 : Nat := 3594792310857912942391261

theorem tailTrace_7000833 : CollatzResearch.WordTrace tailWord_7000833 prefixEnd_7000833 3594792310857912942391261 := by
  unfold tailWord_7000833
  simp only [CollatzResearch.WordTrace]
  refine ⟨255341356646185162931183153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170227571097456775287455435 255341356646185162931183153)
  ·
    refine ⟨191506017484638872198387365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255341356646185162931183153 191506017484638872198387365)
    ·
      refine ⟨35907378278369788537197631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191506017484638872198387365 35907378278369788537197631)
      ·
        refine ⟨53861067417554682805796447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35907378278369788537197631 53861067417554682805796447)
        ·
          refine ⟨80791601126332024208694671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53861067417554682805796447 80791601126332024208694671)
          ·
            refine ⟨121187401689498036313042007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80791601126332024208694671 121187401689498036313042007)
            ·
              refine ⟨181781102534247054469563011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121187401689498036313042007 181781102534247054469563011)
              ·
                refine ⟨272671653801370581704344517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181781102534247054469563011 272671653801370581704344517)
                ·
                  refine ⟨51125935087756984069564597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272671653801370581704344517 51125935087756984069564597)
                  ·
                    refine ⟨4793056414477217256521681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51125935087756984069564597 4793056414477217256521681)
                    ·
                      refine ⟨3594792310857912942391261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793056414477217256521681 3594792310857912942391261)
                      ·
                        rfl

theorem cell23_7000833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_7000833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000833 prefixEnd_7000833 := by exact prefixLift 7000833
  have htrace : WordTrace (prefixWord ++ tailWord_7000833) baseStart_7000833 baseEnd_7000833 := by
    simpa [prefixWord, tailWord_7000833, baseEnd_7000833] using wordTrace_append hprefix tailTrace_7000833
  have hstable : (prefixWord ++ tailWord_7000833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000833).length < 2 ^ (prefixWord ++ tailWord_7000833).sum := by decide
  have hdescent : baseEnd_7000833 < baseStart_7000833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000876 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_7000876 : Nat := 118140960795 + 7000876 * 2 ^ 59
def prefixEnd_7000876 : Nat := 4983230072969 + 3 ^ 40 * 7000876 * 2
def baseEnd_7000876 : Nat := 3594814390526056274153563

theorem tailTrace_7000876 : CollatzResearch.WordTrace tailWord_7000876 prefixEnd_7000876 3594814390526056274153563 := by
  unfold tailWord_7000876
  simp only [CollatzResearch.WordTrace]
  refine ⟨127671462492514690637499241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170228616656686254183332321 127671462492514690637499241)
  ·
    refine ⟨95753596869386017978124431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127671462492514690637499241 95753596869386017978124431)
    ·
      refine ⟨143630395304079026967186647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95753596869386017978124431 143630395304079026967186647)
      ·
        refine ⟨215445592956118540450779971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143630395304079026967186647 215445592956118540450779971)
        ·
          refine ⟨323168389434177810676169957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215445592956118540450779971 323168389434177810676169957)
          ·
            refine ⟨60594073018908339501781867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323168389434177810676169957 60594073018908339501781867)
            ·
              refine ⟨90891109528362509252672801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60594073018908339501781867 90891109528362509252672801)
              ·
                refine ⟨68168332146271881939504601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90891109528362509252672801 68168332146271881939504601)
                ·
                  refine ⟨51126249109703911454628451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68168332146271881939504601 51126249109703911454628451)
                  ·
                    refine ⟨76689373664555867181942677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51126249109703911454628451 76689373664555867181942677)
                    ·
                      refine ⟨3594814390526056274153563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76689373664555867181942677 3594814390526056274153563)
                      ·
                        rfl

theorem cell23_7000876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_7000876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000876 prefixEnd_7000876 := by exact prefixLift 7000876
  have htrace : WordTrace (prefixWord ++ tailWord_7000876) baseStart_7000876 baseEnd_7000876 := by
    simpa [prefixWord, tailWord_7000876, baseEnd_7000876] using wordTrace_append hprefix tailTrace_7000876
  have hstable : (prefixWord ++ tailWord_7000876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000876).length < 2 ^ (prefixWord ++ tailWord_7000876).sum := by decide
  have hdescent : baseEnd_7000876 < baseStart_7000876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000883 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 3]
def baseStart_7000883 : Nat := 118140960795 + 7000883 * 2 ^ 59
def prefixEnd_7000883 : Nat := 4983230072969 + 3 ^ 40 * 7000883 * 2
def baseEnd_7000883 : Nat := 3594817984890637746766031

theorem tailTrace_7000883 : CollatzResearch.WordTrace tailWord_7000883 prefixEnd_7000883 3594817984890637746766031 := by
  unfold tailWord_7000883
  simp only [CollatzResearch.WordTrace]
  refine ⟨255343180296004021470503303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170228786864002680980335535 255343180296004021470503303)
  ·
    refine ⟨383014770444006032205754955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255343180296004021470503303 383014770444006032205754955)
    ·
      refine ⟨574522155666009048308632433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383014770444006032205754955 574522155666009048308632433)
      ·
        refine ⟨430891616749506786231474325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574522155666009048308632433 430891616749506786231474325)
        ·
          refine ⟨20198044535133130604600359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 430891616749506786231474325 20198044535133130604600359)
          ·
            refine ⟨30297066802699695906900539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20198044535133130604600359 30297066802699695906900539)
            ·
              refine ⟨45445600204049543860350809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30297066802699695906900539 45445600204049543860350809)
              ·
                refine ⟨34084200153037157895263107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45445600204049543860350809 34084200153037157895263107)
                ·
                  refine ⟨51126300229555736842894661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34084200153037157895263107 51126300229555736842894661)
                  ·
                    refine ⟨9586181293041700658042749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51126300229555736842894661 9586181293041700658042749)
                    ·
                      refine ⟨3594817984890637746766031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9586181293041700658042749 3594817984890637746766031)
                      ·
                        rfl

theorem cell23_7000883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_7000883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000883 prefixEnd_7000883 := by exact prefixLift 7000883
  have htrace : WordTrace (prefixWord ++ tailWord_7000883) baseStart_7000883 baseEnd_7000883 := by
    simpa [prefixWord, tailWord_7000883, baseEnd_7000883] using wordTrace_append hprefix tailTrace_7000883
  have hstable : (prefixWord ++ tailWord_7000883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000883).length < 2 ^ (prefixWord ++ tailWord_7000883).sum := by decide
  have hdescent : baseEnd_7000883 < baseStart_7000883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000906 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_7000906 : Nat := 118140960795 + 7000906 * 2 ^ 59
def prefixEnd_7000906 : Nat := 4983230072969 + 3 ^ 40 * 7000906 * 2
def baseEnd_7000906 : Nat := 3594829794945691156778425

theorem tailTrace_7000906 : CollatzResearch.WordTrace tailWord_7000906 prefixEnd_7000906 3594829794945691156778425 := by
  unfold tailWord_7000906
  simp only [CollatzResearch.WordTrace]
  refine ⟨63836004793730174099647643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170229346116613797599060381 63836004793730174099647643)
  ·
    refine ⟨95754007190595261149471465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63836004793730174099647643 95754007190595261149471465)
    ·
      refine ⟨71815505392946445862103599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95754007190595261149471465 71815505392946445862103599)
      ·
        refine ⟨107723258089419668793155399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71815505392946445862103599 107723258089419668793155399)
        ·
          refine ⟨161584887134129503189733099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107723258089419668793155399 161584887134129503189733099)
          ·
            refine ⟨242377330701194254784599649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161584887134129503189733099 242377330701194254784599649)
            ·
              refine ⟨181782998025895691088449737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242377330701194254784599649 181782998025895691088449737)
              ·
                refine ⟨136337248519421768316337303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181782998025895691088449737 136337248519421768316337303)
                ·
                  refine ⟨204505872779132652474505955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136337248519421768316337303 204505872779132652474505955)
                  ·
                    refine ⟨306758809168698978711758933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204505872779132652474505955 306758809168698978711758933)
                    ·
                      refine ⟨3594829794945691156778425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 306758809168698978711758933 3594829794945691156778425)
                      ·
                        rfl

theorem cell23_7000906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_7000906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000906 prefixEnd_7000906 := by exact prefixLift 7000906
  have htrace : WordTrace (prefixWord ++ tailWord_7000906) baseStart_7000906 baseEnd_7000906 := by
    simpa [prefixWord, tailWord_7000906, baseEnd_7000906] using wordTrace_append hprefix tailTrace_7000906
  have hstable : (prefixWord ++ tailWord_7000906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000906).length < 2 ^ (prefixWord ++ tailWord_7000906).sum := by decide
  have hdescent : baseEnd_7000906 < baseStart_7000906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000940 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 4, 3, 2]
def baseStart_7000940 : Nat := 118140960795 + 7000940 * 2 ^ 59
def prefixEnd_7000940 : Nat := 4983230072969 + 3 ^ 40 * 7000940 * 2
def baseEnd_7000940 : Nat := 3594847253287944023753269

theorem tailTrace_7000940 : CollatzResearch.WordTrace tailWord_7000940 prefixEnd_7000940 3594847253287944023753269 := by
  unfold tailWord_7000940
  simp only [CollatzResearch.WordTrace]
  refine ⟨127672629628398760102664137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170230172837865013470218849 127672629628398760102664137)
  ·
    refine ⟨95754472221299070076998103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127672629628398760102664137 95754472221299070076998103)
    ·
      refine ⟨143631708331948605115497155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95754472221299070076998103 143631708331948605115497155)
      ·
        refine ⟨215447562497922907673245733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143631708331948605115497155 215447562497922907673245733)
        ·
          refine ⟨40396417968360545188733575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215447562497922907673245733 40396417968360545188733575)
          ·
            refine ⟨60594626952540817783100363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40396417968360545188733575 60594626952540817783100363)
            ·
              refine ⟨90891940428811226674650545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60594626952540817783100363 90891940428811226674650545)
              ·
                refine ⟨68168955321608420005987909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90891940428811226674650545 68168955321608420005987909)
                ·
                  refine ⟨12781679122801578751122733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68168955321608420005987909 12781679122801578751122733)
                  ·
                    refine ⟨4793129671050592031671025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12781679122801578751122733 4793129671050592031671025)
                    ·
                      refine ⟨3594847253287944023753269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793129671050592031671025 3594847253287944023753269)
                      ·
                        rfl

theorem cell23_7000940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_7000940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000940 prefixEnd_7000940 := by exact prefixLift 7000940
  have htrace : WordTrace (prefixWord ++ tailWord_7000940) baseStart_7000940 baseEnd_7000940 := by
    simpa [prefixWord, tailWord_7000940, baseEnd_7000940] using wordTrace_append hprefix tailTrace_7000940
  have hstable : (prefixWord ++ tailWord_7000940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000940).length < 2 ^ (prefixWord ++ tailWord_7000940).sum := by decide
  have hdescent : baseEnd_7000940 < baseStart_7000940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000963 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 1, 6]
def baseStart_7000963 : Nat := 118140960795 + 7000963 * 2 ^ 59
def prefixEnd_7000963 : Nat := 4983230072969 + 3 ^ 40 * 7000963 * 2
def baseEnd_7000963 : Nat := 1198286354447665811255221

theorem tailTrace_7000963 : CollatzResearch.WordTrace tailWord_7000963 prefixEnd_7000963 1198286354447665811255221 := by
  unfold tailWord_7000963
  simp only [CollatzResearch.WordTrace]
  refine ⟨255346098135714195133415543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170230732090476130088943695 255346098135714195133415543)
  ·
    refine ⟨383019147203571292700123315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255346098135714195133415543 383019147203571292700123315)
    ·
      refine ⟨574528720805356939050184973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383019147203571292700123315 574528720805356939050184973)
      ·
        refine ⟨215448270302008852143819365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574528720805356939050184973 215448270302008852143819365)
        ·
          refine ⟨40396550681626659776966131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215448270302008852143819365 40396550681626659776966131)
          ·
            refine ⟨60594826022439989665449197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40396550681626659776966131 60594826022439989665449197)
            ·
              refine ⟨22723059758414996124543449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60594826022439989665449197 22723059758414996124543449)
              ·
                refine ⟨17042294818811247093407587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22723059758414996124543449 17042294818811247093407587)
                ·
                  refine ⟨25563442228216870640111381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17042294818811247093407587 25563442228216870640111381)
                  ·
                    refine ⟨1198286354447665811255221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25563442228216870640111381 1198286354447665811255221)
                    ·
                      rfl

theorem cell23_7000963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 6].length) (baseStart_7000963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000963 prefixEnd_7000963 := by exact prefixLift 7000963
  have htrace : WordTrace (prefixWord ++ tailWord_7000963) baseStart_7000963 baseEnd_7000963 := by
    simpa [prefixWord, tailWord_7000963, baseEnd_7000963] using wordTrace_append hprefix tailTrace_7000963
  have hstable : (prefixWord ++ tailWord_7000963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000963).length < 2 ^ (prefixWord ++ tailWord_7000963).sum := by decide
  have hdescent : baseEnd_7000963 < baseStart_7000963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000967 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 1, 5]
def baseStart_7000967 : Nat := 118140960795 + 7000967 * 2 ^ 59
def prefixEnd_7000967 : Nat := 4983230072969 + 3 ^ 40 * 7000967 * 2
def baseEnd_7000967 : Nat := 1198287039088538472705215

theorem tailTrace_7000967 : CollatzResearch.WordTrace tailWord_7000967 prefixEnd_7000967 1198287039088538472705215 := by
  unfold tailWord_7000967
  simp only [CollatzResearch.WordTrace]
  refine ⟨255346244027699703816561155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170230829351799802544374103 255346244027699703816561155)
  ·
    refine ⟨383019366041549555724841733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255346244027699703816561155 383019366041549555724841733)
    ·
      refine ⟨71816131132790541698407825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383019366041549555724841733 71816131132790541698407825)
      ·
        refine ⟨53862098349592906273805869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71816131132790541698407825 53862098349592906273805869)
        ·
          refine ⟨20198286881097339852677201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53862098349592906273805869 20198286881097339852677201)
          ·
            refine ⟨15148715160823004889507901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20198286881097339852677201 15148715160823004889507901)
            ·
              refine ⟨5680768185308626833565463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15148715160823004889507901 5680768185308626833565463)
              ·
                refine ⟨8521152277962940250348195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680768185308626833565463 8521152277962940250348195)
                ·
                  refine ⟨12781728416944410375522293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521152277962940250348195 12781728416944410375522293)
                  ·
                    refine ⟨1198287039088538472705215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12781728416944410375522293 1198287039088538472705215)
                    ·
                      rfl

theorem cell23_7000967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_7000967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000967 prefixEnd_7000967 := by exact prefixLift 7000967
  have htrace : WordTrace (prefixWord ++ tailWord_7000967) baseStart_7000967 baseEnd_7000967 := by
    simpa [prefixWord, tailWord_7000967, baseEnd_7000967] using wordTrace_append hprefix tailTrace_7000967
  have hstable : (prefixWord ++ tailWord_7000967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000967).length < 2 ^ (prefixWord ++ tailWord_7000967).sum := by decide
  have hdescent : baseEnd_7000967 < baseStart_7000967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000981 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_7000981 : Nat := 118140960795 + 7000981 * 2 ^ 59
def prefixEnd_7000981 : Nat := 4983230072969 + 3 ^ 40 * 7000981 * 2
def baseEnd_7000981 : Nat := 3594868305994778363340581

theorem tailTrace_7000981 : CollatzResearch.WordTrace tailWord_7000981 prefixEnd_7000981 3594868305994778363340581 := by
  unfold tailWord_7000981
  simp only [CollatzResearch.WordTrace]
  refine ⟨255346754649648984207570797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170231169766432656138380531 255346754649648984207570797)
  ·
    refine ⟨95755032993618369077839049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255346754649648984207570797 95755032993618369077839049)
    ·
      refine ⟨71816274745213776808379287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95755032993618369077839049 71816274745213776808379287)
      ·
        refine ⟨107724412117820665212568931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71816274745213776808379287 107724412117820665212568931)
        ·
          refine ⟨161586618176730997818853397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107724412117820665212568931 161586618176730997818853397)
          ·
            refine ⟨7574372727034265522758753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161586618176730997818853397 7574372727034265522758753)
            ·
              refine ⟨5680779545275699142069065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574372727034265522758753 5680779545275699142069065)
              ·
                refine ⟨4260584658956774356551799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680779545275699142069065 4260584658956774356551799)
                ·
                  refine ⟨6390876988435161534827699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260584658956774356551799 6390876988435161534827699)
                  ·
                    refine ⟨9586315482652742302241549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390876988435161534827699 9586315482652742302241549)
                    ·
                      refine ⟨3594868305994778363340581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9586315482652742302241549 3594868305994778363340581)
                      ·
                        rfl

theorem cell23_7000981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_7000981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000981 prefixEnd_7000981 := by exact prefixLift 7000981
  have htrace : WordTrace (prefixWord ++ tailWord_7000981) baseStart_7000981 baseEnd_7000981 := by
    simpa [prefixWord, tailWord_7000981, baseEnd_7000981] using wordTrace_append hprefix tailTrace_7000981
  have hstable : (prefixWord ++ tailWord_7000981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000981).length < 2 ^ (prefixWord ++ tailWord_7000981).sum := by decide
  have hdescent : baseEnd_7000981 < baseStart_7000981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7000983 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_7000983 : Nat := 118140960795 + 7000983 * 2 ^ 59
def prefixEnd_7000983 : Nat := 4983230072969 + 3 ^ 40 * 7000983 * 2
def baseEnd_7000983 : Nat := 3594869332956087355515571

theorem tailTrace_7000983 : CollatzResearch.WordTrace tailWord_7000983 prefixEnd_7000983 3594869332956087355515571 := by
  unfold tailWord_7000983
  simp only [CollatzResearch.WordTrace]
  refine ⟨255346827595641738549143603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170231218397094492366095735 255346827595641738549143603)
  ·
    refine ⟨383020241393462607823715405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255346827595641738549143603 383020241393462607823715405)
    ·
      refine ⟨143632590522548477933893277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383020241393462607823715405 143632590522548477933893277)
      ·
        refine ⟨53862221445955679225209979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143632590522548477933893277 53862221445955679225209979)
        ·
          refine ⟨80793332168933518837814969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53862221445955679225209979 80793332168933518837814969)
          ·
            refine ⟨60594999126700139128361227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80793332168933518837814969 60594999126700139128361227)
            ·
              refine ⟨90892498690050208692541841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60594999126700139128361227 90892498690050208692541841)
              ·
                refine ⟨68169374017537656519406381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90892498690050208692541841 68169374017537656519406381)
                ·
                  refine ⟨25563515256576621194777393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68169374017537656519406381 25563515256576621194777393)
                  ·
                    refine ⟨19172636442432465896083045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25563515256576621194777393 19172636442432465896083045)
                    ·
                      refine ⟨3594869332956087355515571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19172636442432465896083045 3594869332956087355515571)
                      ·
                        rfl

theorem cell23_7000983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_7000983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7000983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7000983 prefixEnd_7000983 := by exact prefixLift 7000983
  have htrace : WordTrace (prefixWord ++ tailWord_7000983) baseStart_7000983 baseEnd_7000983 := by
    simpa [prefixWord, tailWord_7000983, baseEnd_7000983] using wordTrace_append hprefix tailTrace_7000983
  have hstable : (prefixWord ++ tailWord_7000983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7000983).length < 2 ^ (prefixWord ++ tailWord_7000983).sum := by decide
  have hdescent : baseEnd_7000983 < baseStart_7000983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7000983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 3]
def baseStart_7001003 : Nat := 118140960795 + 7001003 * 2 ^ 59
def prefixEnd_7001003 : Nat := 4983230072969 + 3 ^ 40 * 7001003 * 2
def baseEnd_7001003 : Nat := 3594879602569177277265479

theorem tailTrace_7001003 : CollatzResearch.WordTrace tailWord_7001003 prefixEnd_7001003 3594879602569177277265479 := by
  unfold tailWord_7001003
  simp only [CollatzResearch.WordTrace]
  refine ⟨255347557055569281964871663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170231704703712854643247775 255347557055569281964871663)
  ·
    refine ⟨383021335583353922947307495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255347557055569281964871663 383021335583353922947307495)
    ·
      refine ⟨574532003375030884420961243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383021335583353922947307495 574532003375030884420961243)
      ·
        refine ⟨861798005062546326631441865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574532003375030884420961243 861798005062546326631441865)
        ·
          refine ⟨646348503796909744973581399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861798005062546326631441865 646348503796909744973581399)
          ·
            refine ⟨969522755695364617460372099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646348503796909744973581399 969522755695364617460372099)
            ·
              refine ⟨1454284133543046926190558149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969522755695364617460372099 1454284133543046926190558149)
              ·
                refine ⟨272678275039321298660729653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1454284133543046926190558149 272678275039321298660729653)
                ·
                  refine ⟨25563588284936371749443405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272678275039321298660729653 25563588284936371749443405)
                  ·
                    refine ⟨9586345606851139406041277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25563588284936371749443405 9586345606851139406041277)
                    ·
                      refine ⟨3594879602569177277265479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9586345606851139406041277 3594879602569177277265479)
                      ·
                        rfl

theorem cell23_7001003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 3].length) (baseStart_7001003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001003 prefixEnd_7001003 := by exact prefixLift 7001003
  have htrace : WordTrace (prefixWord ++ tailWord_7001003) baseStart_7001003 baseEnd_7001003 := by
    simpa [prefixWord, tailWord_7001003, baseEnd_7001003] using wordTrace_append hprefix tailTrace_7001003
  have hstable : (prefixWord ++ tailWord_7001003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001003).length < 2 ^ (prefixWord ++ tailWord_7001003).sum := by decide
  have hdescent : baseEnd_7001003 < baseStart_7001003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001021 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_7001021 : Nat := 118140960795 + 7001021 * 2 ^ 59
def prefixEnd_7001021 : Nat := 4983230072969 + 3 ^ 40 * 7001021 * 2
def baseEnd_7001021 : Nat := 3594888845220958206840397

theorem tailTrace_7001021 : CollatzResearch.WordTrace tailWord_7001021 prefixEnd_7001021 3594888845220958206840397 := by
  unfold tailWord_7001021
  simp only [CollatzResearch.WordTrace]
  refine ⟨255348213569504071039026917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170232142379669380692684611 255348213569504071039026917)
  ·
    refine ⟨47877790044282013319817547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255348213569504071039026917 47877790044282013319817547)
    ·
      refine ⟨71816685066423019979726321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47877790044282013319817547 71816685066423019979726321)
      ·
        refine ⟨53862513799817264984794741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71816685066423019979726321 53862513799817264984794741)
        ·
          refine ⟨5049610668732868592324507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53862513799817264984794741 5049610668732868592324507)
          ·
            refine ⟨7574416003099302888486761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049610668732868592324507 7574416003099302888486761)
            ·
              refine ⟨5680812002324477166365071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574416003099302888486761 5680812002324477166365071)
              ·
                refine ⟨8521218003486715749547607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680812002324477166365071 8521218003486715749547607)
                ·
                  refine ⟨12781827005230073624321411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521218003486715749547607 12781827005230073624321411)
                  ·
                    refine ⟨19172740507845110436482117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12781827005230073624321411 19172740507845110436482117)
                    ·
                      refine ⟨3594888845220958206840397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19172740507845110436482117 3594888845220958206840397)
                      ·
                        rfl

theorem cell23_7001021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_7001021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001021 prefixEnd_7001021 := by exact prefixLift 7001021
  have htrace : WordTrace (prefixWord ++ tailWord_7001021) baseStart_7001021 baseEnd_7001021 := by
    simpa [prefixWord, tailWord_7001021, baseEnd_7001021] using wordTrace_append hprefix tailTrace_7001021
  have hstable : (prefixWord ++ tailWord_7001021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001021).length < 2 ^ (prefixWord ++ tailWord_7001021).sum := by decide
  have hdescent : baseEnd_7001021 < baseStart_7001021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001024 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 1, 2, 3]
def baseStart_7001024 : Nat := 118140960795 + 7001024 * 2 ^ 59
def prefixEnd_7001024 : Nat := 4983230072969 + 3 ^ 40 * 7001024 * 2
def baseEnd_7001024 : Nat := 3594890385662921695102883

theorem tailTrace_7001024 : CollatzResearch.WordTrace tailWord_7001024 prefixEnd_7001024 3594890385662921695102883 := by
  unfold tailWord_7001024
  simp only [CollatzResearch.WordTrace]
  refine ⟨127674161494246601275693063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170232215325662135034257417 127674161494246601275693063)
  ·
    refine ⟨191511242241369901913539595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127674161494246601275693063 191511242241369901913539595)
    ·
      refine ⟨287266863362054852870309393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191511242241369901913539595 287266863362054852870309393)
      ·
        refine ⟨215450147521541139652732045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287266863362054852870309393 215450147521541139652732045)
        ·
          refine ⟨80793805320577927369774517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215450147521541139652732045 80793805320577927369774517)
          ·
            refine ⟨7574419248804180690916361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80793805320577927369774517 7574419248804180690916361)
            ·
              refine ⟨5680814436603135518187271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574419248804180690916361 5680814436603135518187271)
              ·
                refine ⟨8521221654904703277280907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680814436603135518187271 8521221654904703277280907)
                ·
                  refine ⟨12781832482357054915921361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521221654904703277280907 12781832482357054915921361)
                  ·
                    refine ⟨9586374361767791186941021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12781832482357054915921361 9586374361767791186941021)
                    ·
                      refine ⟨3594890385662921695102883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9586374361767791186941021 3594890385662921695102883)
                      ·
                        rfl

theorem cell23_7001024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_7001024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001024 prefixEnd_7001024 := by exact prefixLift 7001024
  have htrace : WordTrace (prefixWord ++ tailWord_7001024) baseStart_7001024 baseEnd_7001024 := by
    simpa [prefixWord, tailWord_7001024, baseEnd_7001024] using wordTrace_append hprefix tailTrace_7001024
  have hstable : (prefixWord ++ tailWord_7001024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001024).length < 2 ^ (prefixWord ++ tailWord_7001024).sum := by decide
  have hdescent : baseEnd_7001024 < baseStart_7001024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001093 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_7001093 : Nat := 118140960795 + 7001093 * 2 ^ 59
def prefixEnd_7001093 : Nat := 4983230072969 + 3 ^ 40 * 7001093 * 2
def baseEnd_7001093 : Nat := 3594925815828081925140065

theorem tailTrace_7001093 : CollatzResearch.WordTrace tailWord_7001093 prefixEnd_7001093 3594925815828081925140065 := by
  unfold tailWord_7001093
  simp only [CollatzResearch.WordTrace]
  refine ⟨255350839625243227335647933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170233893083495484890431955 255350839625243227335647933)
  ·
    refine ⟨95756564859466210250867975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255350839625243227335647933 95756564859466210250867975)
    ·
      refine ⟨143634847289199315376301963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95756564859466210250867975 143634847289199315376301963)
      ·
        refine ⟨215452270933798973064452945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143634847289199315376301963 215452270933798973064452945)
        ·
          refine ⟨161589203200349229798339709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215452270933798973064452945 161589203200349229798339709)
          ·
            refine ⟨60595951200130961174377391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161589203200349229798339709 60595951200130961174377391)
            ·
              refine ⟨90893926800196441761566087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60595951200130961174377391 90893926800196441761566087)
              ·
                refine ⟨136340890200294662642349131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90893926800196441761566087 136340890200294662642349131)
                ·
                  refine ⟨204511335300441993963523697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136340890200294662642349131 204511335300441993963523697)
                  ·
                    refine ⟨153383501475331495472642773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204511335300441993963523697 153383501475331495472642773)
                    ·
                      refine ⟨3594925815828081925140065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153383501475331495472642773 3594925815828081925140065)
                      ·
                        rfl

theorem cell23_7001093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_7001093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001093 prefixEnd_7001093 := by exact prefixLift 7001093
  have htrace : WordTrace (prefixWord ++ tailWord_7001093) baseStart_7001093 baseEnd_7001093 := by
    simpa [prefixWord, tailWord_7001093, baseEnd_7001093] using wordTrace_append hprefix tailTrace_7001093
  have hstable : (prefixWord ++ tailWord_7001093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001093).length < 2 ^ (prefixWord ++ tailWord_7001093).sum := by decide
  have hdescent : baseEnd_7001093 < baseStart_7001093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001100 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 7]
def baseStart_7001100 : Nat := 118140960795 + 7001100 * 2 ^ 59
def prefixEnd_7001100 : Nat := 4983230072969 + 3 ^ 40 * 7001100 * 2
def baseEnd_7001100 : Nat := 399436601132518155305837

theorem tailTrace_7001100 : CollatzResearch.WordTrace tailWord_7001100 prefixEnd_7001100 399436601132518155305837 := by
  unfold tailWord_7001100
  simp only [CollatzResearch.WordTrace]
  refine ⟨127675547468108933765576377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170234063290811911687435169 127675547468108933765576377)
  ·
    refine ⟨95756660601081700324182283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127675547468108933765576377 95756660601081700324182283)
    ·
      refine ⟨143634990901622550486273425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95756660601081700324182283 143634990901622550486273425)
      ·
        refine ⟨107726243176216912864705069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143634990901622550486273425 107726243176216912864705069)
        ·
          refine ⟨40397341191081342324264401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107726243176216912864705069 40397341191081342324264401)
          ·
            refine ⟨30298005893311006743198301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40397341191081342324264401 30298005893311006743198301)
            ·
              refine ⟨11361752209991627528699363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30298005893311006743198301 11361752209991627528699363)
              ·
                refine ⟨17042628314987441293049045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11361752209991627528699363 17042628314987441293049045)
                ·
                  refine ⟨399436601132518155305837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17042628314987441293049045 399436601132518155305837)
                  ·
                    rfl

theorem cell23_7001100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_7001100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001100 prefixEnd_7001100 := by exact prefixLift 7001100
  have htrace : WordTrace (prefixWord ++ tailWord_7001100) baseStart_7001100 baseEnd_7001100 := by
    simpa [prefixWord, tailWord_7001100, baseEnd_7001100] using wordTrace_append hprefix tailTrace_7001100
  have hstable : (prefixWord ++ tailWord_7001100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001100).length < 2 ^ (prefixWord ++ tailWord_7001100).sum := by decide
  have hdescent : baseEnd_7001100 < baseStart_7001100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001111 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7001111 : Nat := 118140960795 + 7001111 * 2 ^ 59
def prefixEnd_7001111 : Nat := 4983230072969 + 3 ^ 40 * 7001111 * 2
def baseEnd_7001111 : Nat := 3594935058479862854714983

theorem tailTrace_7001111 : CollatzResearch.WordTrace tailWord_7001111 prefixEnd_7001111 3594935058479862854714983 := by
  unfold tailWord_7001111
  simp only [CollatzResearch.WordTrace]
  refine ⟨255351496139178016409803187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170234330759452010939868791 255351496139178016409803187)
  ·
    refine ⟨383027244208767024614704781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255351496139178016409803187 383027244208767024614704781)
    ·
      refine ⟨143635216578287634230514293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383027244208767024614704781 143635216578287634230514293)
      ·
        refine ⟨13465801554214465709110715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143635216578287634230514293 13465801554214465709110715)
        ·
          refine ⟨20198702331321698563666073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13465801554214465709110715 20198702331321698563666073)
          ·
            refine ⟨15149026748491273922749555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20198702331321698563666073 15149026748491273922749555)
            ·
              refine ⟨22723540122736910884124333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15149026748491273922749555 22723540122736910884124333)
              ·
                refine ⟨8521327546026341581546625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22723540122736910884124333 8521327546026341581546625)
                ·
                  refine ⟨6390995659519756186159969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8521327546026341581546625 6390995659519756186159969)
                  ·
                    refine ⟨4793246744639817139619977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6390995659519756186159969 4793246744639817139619977)
                    ·
                      refine ⟨3594935058479862854714983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793246744639817139619977 3594935058479862854714983)
                      ·
                        rfl

theorem cell23_7001111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7001111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001111 prefixEnd_7001111 := by exact prefixLift 7001111
  have htrace : WordTrace (prefixWord ++ tailWord_7001111) baseStart_7001111 baseEnd_7001111 := by
    simpa [prefixWord, tailWord_7001111, baseEnd_7001111] using wordTrace_append hprefix tailTrace_7001111
  have hstable : (prefixWord ++ tailWord_7001111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001111).length < 2 ^ (prefixWord ++ tailWord_7001111).sum := by decide
  have hdescent : baseEnd_7001111 < baseStart_7001111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001113 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_7001113 : Nat := 118140960795 + 7001113 * 2 ^ 59
def prefixEnd_7001113 : Nat := 4983230072969 + 3 ^ 40 * 7001113 * 2
def baseEnd_7001113 : Nat := 1198312028480390615629991

theorem tailTrace_7001113 : CollatzResearch.WordTrace tailWord_7001113 prefixEnd_7001113 1198312028480390615629991 := by
  unfold tailWord_7001113
  simp only [CollatzResearch.WordTrace]
  refine ⟨255351569085170770751375993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170234379390113847167583995 255351569085170770751375993)
  ·
    refine ⟨191513676813878078063531995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255351569085170770751375993 191513676813878078063531995)
    ·
      refine ⟨287270515220817117095297993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191513676813878078063531995 287270515220817117095297993)
      ·
        refine ⟨215452886415612837821473495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287270515220817117095297993 215452886415612837821473495)
        ·
          refine ⟨323179329623419256732210243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215452886415612837821473495 323179329623419256732210243)
          ·
            refine ⟨484768994435128885098315365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323179329623419256732210243 484768994435128885098315365)
            ·
              refine ⟨90894186456586665955934131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484768994435128885098315365 90894186456586665955934131)
              ·
                refine ⟨136341279684879998933901197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90894186456586665955934131 136341279684879998933901197)
                ·
                  refine ⟨51127979881829999600212949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136341279684879998933901197 51127979881829999600212949)
                  ·
                    refine ⟨1198312028480390615629991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51127979881829999600212949 1198312028480390615629991)
                    ·
                      rfl

theorem cell23_7001113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_7001113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001113 prefixEnd_7001113 := by exact prefixLift 7001113
  have htrace : WordTrace (prefixWord ++ tailWord_7001113) baseStart_7001113 baseEnd_7001113 := by
    simpa [prefixWord, tailWord_7001113, baseEnd_7001113] using wordTrace_append hprefix tailTrace_7001113
  have hstable : (prefixWord ++ tailWord_7001113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001113).length < 2 ^ (prefixWord ++ tailWord_7001113).sum := by decide
  have hdescent : baseEnd_7001113 < baseStart_7001113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001181 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7001181 : Nat := 118140960795 + 7001181 * 2 ^ 59
def prefixEnd_7001181 : Nat := 4983230072969 + 3 ^ 40 * 7001181 * 2
def baseEnd_7001181 : Nat := 1198323667375225860279887

theorem tailTrace_7001181 : CollatzResearch.WordTrace tailWord_7001181 prefixEnd_7001181 1198323667375225860279887 := by
  unfold tailWord_7001181
  simp only [CollatzResearch.WordTrace]
  refine ⟨255354049248924418364851397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170236032832616278909900931 255354049248924418364851397)
  ·
    refine ⟨47878884234173328443409637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255354049248924418364851397 47878884234173328443409637)
    ·
      refine ⟨8977290793907499083139307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47878884234173328443409637 8977290793907499083139307)
      ·
        refine ⟨13465936190861248624708961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8977290793907499083139307 13465936190861248624708961)
        ·
          refine ⟨10099452143145936468531721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13465936190861248624708961 10099452143145936468531721)
          ·
            refine ⟨7574589107359452351398791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10099452143145936468531721 7574589107359452351398791)
            ·
              refine ⟨11361883661039178527098187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7574589107359452351398791 11361883661039178527098187)
              ·
                refine ⟨17042825491558767790647281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11361883661039178527098187 17042825491558767790647281)
                ·
                  refine ⟨12782119118669075842985461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17042825491558767790647281 12782119118669075842985461)
                  ·
                    refine ⟨1198323667375225860279887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12782119118669075842985461 1198323667375225860279887)
                    ·
                      rfl

theorem cell23_7001181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7001181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001181 prefixEnd_7001181 := by exact prefixLift 7001181
  have htrace : WordTrace (prefixWord ++ tailWord_7001181) baseStart_7001181 baseEnd_7001181 := by
    simpa [prefixWord, tailWord_7001181, baseEnd_7001181] using wordTrace_append hprefix tailTrace_7001181
  have hstable : (prefixWord ++ tailWord_7001181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001181).length < 2 ^ (prefixWord ++ tailWord_7001181).sum := by decide
  have hdescent : baseEnd_7001181 < baseStart_7001181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001244 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_7001244 : Nat := 118140960795 + 7001244 * 2 ^ 59
def prefixEnd_7001244 : Nat := 4983230072969 + 3 ^ 40 * 7001244 * 2
def baseEnd_7001244 : Nat := 3595003351406910834351871

theorem tailTrace_7001244 : CollatzResearch.WordTrace tailWord_7001244 prefixEnd_7001244 3595003351406910834351871 := by
  unfold tailWord_7001244
  simp only [CollatzResearch.WordTrace]
  refine ⟨127678173523848090062197393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170237564698464120082929857 127678173523848090062197393)
  ·
    refine ⟨95758630142886067546648045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127678173523848090062197393 95758630142886067546648045)
    ·
      refine ⟨35909486303582275329993017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95758630142886067546648045 35909486303582275329993017)
      ·
        refine ⟨26932114727686706497494763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35909486303582275329993017 26932114727686706497494763)
        ·
          refine ⟨40398172091530059746242145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26932114727686706497494763 40398172091530059746242145)
          ·
            refine ⟨30298629068647544809681609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40398172091530059746242145 30298629068647544809681609)
            ·
              refine ⟨22723971801485658607261207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30298629068647544809681609 22723971801485658607261207)
              ·
                refine ⟨34085957702228487910891811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22723971801485658607261207 34085957702228487910891811)
                ·
                  refine ⟨51128936553342731866337717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34085957702228487910891811 51128936553342731866337717)
                  ·
                    refine ⟨4793337801875881112469161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51128936553342731866337717 4793337801875881112469161)
                    ·
                      refine ⟨3595003351406910834351871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793337801875881112469161 3595003351406910834351871)
                      ·
                        rfl

theorem cell23_7001244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_7001244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001244 prefixEnd_7001244 := by exact prefixLift 7001244
  have htrace : WordTrace (prefixWord ++ tailWord_7001244) baseStart_7001244 baseEnd_7001244 := by
    simpa [prefixWord, tailWord_7001244, baseEnd_7001244] using wordTrace_append hprefix tailTrace_7001244
  have hstable : (prefixWord ++ tailWord_7001244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001244).length < 2 ^ (prefixWord ++ tailWord_7001244).sum := by decide
  have hdescent : baseEnd_7001244 < baseStart_7001244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001267 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 4, 4]
def baseStart_7001267 : Nat := 118140960795 + 7001267 * 2 ^ 59
def prefixEnd_7001267 : Nat := 4983230072969 + 3 ^ 40 * 7001267 * 2
def baseEnd_7001267 : Nat := 1198338387153988081454755

theorem tailTrace_7001267 : CollatzResearch.WordTrace tailWord_7001267 prefixEnd_7001267 1198338387153988081454755 := by
  unfold tailWord_7001267
  simp only [CollatzResearch.WordTrace]
  refine ⟨255357185926612855052482055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170238123951075236701654703 255357185926612855052482055)
  ·
    refine ⟨383035778889919282578723083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255357185926612855052482055 383035778889919282578723083)
    ·
      refine ⟨574553668334878923868084625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383035778889919282578723083 574553668334878923868084625)
      ·
        refine ⟨430915251251159192901063469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574553668334878923868084625 430915251251159192901063469)
        ·
          refine ⟨161593219219184697337898801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430915251251159192901063469 161593219219184697337898801)
          ·
            refine ⟨121194914414388523003424101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161593219219184697337898801 121194914414388523003424101)
            ·
              refine ⟨22724046452697848063142019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121194914414388523003424101 22724046452697848063142019)
              ·
                refine ⟨34086069679046772094713029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22724046452697848063142019 34086069679046772094713029)
                ·
                  refine ⟨6391138064821269767758693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34086069679046772094713029 6391138064821269767758693)
                  ·
                    refine ⟨1198338387153988081454755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391138064821269767758693 1198338387153988081454755)
                    ·
                      rfl

theorem cell23_7001267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 4].length) (baseStart_7001267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001267 prefixEnd_7001267 := by exact prefixLift 7001267
  have htrace : WordTrace (prefixWord ++ tailWord_7001267) baseStart_7001267 baseEnd_7001267 := by
    simpa [prefixWord, tailWord_7001267, baseEnd_7001267] using wordTrace_append hprefix tailTrace_7001267
  have hstable : (prefixWord ++ tailWord_7001267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001267).length < 2 ^ (prefixWord ++ tailWord_7001267).sum := by decide
  have hdescent : baseEnd_7001267 < baseStart_7001267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001277 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_7001277 : Nat := 118140960795 + 7001277 * 2 ^ 59
def prefixEnd_7001277 : Nat := 4983230072969 + 3 ^ 40 * 7001277 * 2
def baseEnd_7001277 : Nat := 3595020296268509205239219

theorem tailTrace_7001277 : CollatzResearch.WordTrace tailWord_7001277 prefixEnd_7001277 3595020296268509205239219 := by
  unfold tailWord_7001277
  simp only [CollatzResearch.WordTrace]
  refine ⟨255357550656576626760346085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170238367104384417840230723 255357550656576626760346085)
  ·
    refine ⟨47879540748108117517564891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255357550656576626760346085 47879540748108117517564891)
    ·
      refine ⟨71819311122162176276347337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47879540748108117517564891 71819311122162176276347337)
      ·
        refine ⟨53864483341621632207260503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71819311122162176276347337 53864483341621632207260503)
        ·
          refine ⟨80796725012432448310890755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53864483341621632207260503 80796725012432448310890755)
          ·
            refine ⟨121195087518648672466336133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80796725012432448310890755 121195087518648672466336133)
            ·
              refine ⟨22724078909746626087438025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121195087518648672466336133 22724078909746626087438025)
              ·
                refine ⟨17043059182309969565578519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22724078909746626087438025 17043059182309969565578519)
                ·
                  refine ⟨25564588773464954348367779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17043059182309969565578519 25564588773464954348367779)
                  ·
                    refine ⟨38346883160197431522551669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25564588773464954348367779 38346883160197431522551669)
                    ·
                      refine ⟨3595020296268509205239219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38346883160197431522551669 3595020296268509205239219)
                      ·
                        rfl

theorem cell23_7001277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_7001277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001277 prefixEnd_7001277 := by exact prefixLift 7001277
  have htrace : WordTrace (prefixWord ++ tailWord_7001277) baseStart_7001277 baseEnd_7001277 := by
    simpa [prefixWord, tailWord_7001277, baseEnd_7001277] using wordTrace_append hprefix tailTrace_7001277
  have hstable : (prefixWord ++ tailWord_7001277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001277).length < 2 ^ (prefixWord ++ tailWord_7001277).sum := by decide
  have hdescent : baseEnd_7001277 < baseStart_7001277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001304 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_7001304 : Nat := 118140960795 + 7001304 * 2 ^ 59
def prefixEnd_7001304 : Nat := 4983230072969 + 3 ^ 40 * 7001304 * 2
def baseEnd_7001304 : Nat := 3595034160246180599601595

theorem tailTrace_7001304 : CollatzResearch.WordTrace tailWord_7001304 prefixEnd_7001304 3595034160246180599601595 := by
  unfold tailWord_7001304
  simp only [CollatzResearch.WordTrace]
  refine ⟨127679267713739405185789483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170239023618319206914385977 127679267713739405185789483)
  ·
    refine ⟨191518901570609107778684225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127679267713739405185789483 191518901570609107778684225)
    ·
      refine ⟨143639176177956830834013169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191518901570609107778684225 143639176177956830834013169)
      ·
        refine ⟨107729382133467623125509877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143639176177956830834013169 107729382133467623125509877)
        ·
          refine ⟨10099629575012589668016551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107729382133467623125509877 10099629575012589668016551)
          ·
            refine ⟨15149444362518884502024827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10099629575012589668016551 15149444362518884502024827)
            ·
              refine ⟨22724166543778326753037241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15149444362518884502024827 22724166543778326753037241)
              ·
                refine ⟨17043124907833745064777931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22724166543778326753037241 17043124907833745064777931)
                ·
                  refine ⟨25564687361750617597166897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17043124907833745064777931 25564687361750617597166897)
                  ·
                    refine ⟨19173515521312963197875173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25564687361750617597166897 19173515521312963197875173)
                    ·
                      refine ⟨3595034160246180599601595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19173515521312963197875173 3595034160246180599601595)
                      ·
                        rfl

theorem cell23_7001304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_7001304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001304 prefixEnd_7001304 := by exact prefixLift 7001304
  have htrace : WordTrace (prefixWord ++ tailWord_7001304) baseStart_7001304 baseEnd_7001304 := by
    simpa [prefixWord, tailWord_7001304, baseEnd_7001304] using wordTrace_append hprefix tailTrace_7001304
  have hstable : (prefixWord ++ tailWord_7001304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001304).length < 2 ^ (prefixWord ++ tailWord_7001304).sum := by decide
  have hdescent : baseEnd_7001304 < baseStart_7001304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001325 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7001325 : Nat := 118140960795 + 7001325 * 2 ^ 59
def prefixEnd_7001325 : Nat := 4983230072969 + 3 ^ 40 * 7001325 * 2
def baseEnd_7001325 : Nat := 3595044943339925017438999

theorem tailTrace_7001325 : CollatzResearch.WordTrace tailWord_7001325 prefixEnd_7001325 3595044943339925017438999 := by
  unfold tailWord_7001325
  simp only [CollatzResearch.WordTrace]
  refine ⟨255359301360402730958093429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170239534240268487305395619 255359301360402730958093429)
  ·
    refine ⟨23939934502537756027321259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255359301360402730958093429 23939934502537756027321259)
    ·
      refine ⟨35909901753806634040981889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23939934502537756027321259 35909901753806634040981889)
      ·
        refine ⟨26932426315354975530736417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35909901753806634040981889 26932426315354975530736417)
        ·
          refine ⟨20199319736516231648052313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26932426315354975530736417 20199319736516231648052313)
          ·
            refine ⟨15149489802387173736039235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20199319736516231648052313 15149489802387173736039235)
            ·
              refine ⟨22724234703580760604058853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15149489802387173736039235 22724234703580760604058853)
              ·
                refine ⟨4260794006921392613261035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22724234703580760604058853 4260794006921392613261035)
                ·
                  refine ⟨6391191010382088919891553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260794006921392613261035 6391191010382088919891553)
                  ·
                    refine ⟨4793393257786566689918665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6391191010382088919891553 4793393257786566689918665)
                    ·
                      refine ⟨3595044943339925017438999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793393257786566689918665 3595044943339925017438999)
                      ·
                        rfl

theorem cell23_7001325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7001325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001325 prefixEnd_7001325 := by exact prefixLift 7001325
  have htrace : WordTrace (prefixWord ++ tailWord_7001325) baseStart_7001325 baseEnd_7001325 := by
    simpa [prefixWord, tailWord_7001325, baseEnd_7001325] using wordTrace_append hprefix tailTrace_7001325
  have hstable : (prefixWord ++ tailWord_7001325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001325).length < 2 ^ (prefixWord ++ tailWord_7001325).sum := by decide
  have hdescent : baseEnd_7001325 < baseStart_7001325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001362 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7001362 : Nat := 118140960795 + 7001362 * 2 ^ 59
def prefixEnd_7001362 : Nat := 4983230072969 + 3 ^ 40 * 7001362 * 2
def baseEnd_7001362 : Nat := 3595063942124141372676329

theorem tailTrace_7001362 : CollatzResearch.WordTrace tailWord_7001362 prefixEnd_7001362 3595063942124141372676329 := by
  unfold tailWord_7001362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63840162715317171569297585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170240433907512457518126893 63840162715317171569297585)
  ·
    refine ⟨47880122036487878676973189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63840162715317171569297585 47880122036487878676973189)
    ·
      refine ⟨8977522881841477251932473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47880122036487878676973189 8977522881841477251932473)
      ·
        refine ⟨6733142161381107938949355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8977522881841477251932473 6733142161381107938949355)
        ·
          refine ⟨10099713242071661908424033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733142161381107938949355 10099713242071661908424033)
          ·
            refine ⟨7574784931553746431318025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10099713242071661908424033 7574784931553746431318025)
            ·
              refine ⟨5681088698665309823488519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574784931553746431318025 5681088698665309823488519)
              ·
                refine ⟨8521633047997964735232779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681088698665309823488519 8521633047997964735232779)
                ·
                  refine ⟨12782449571996947102849169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521633047997964735232779 12782449571996947102849169)
                  ·
                    refine ⟨9586837178997710327136877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12782449571996947102849169 9586837178997710327136877)
                    ·
                      refine ⟨3595063942124141372676329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9586837178997710327136877 3595063942124141372676329)
                      ·
                        rfl

theorem cell23_7001362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7001362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001362 prefixEnd_7001362 := by exact prefixLift 7001362
  have htrace : WordTrace (prefixWord ++ tailWord_7001362) baseStart_7001362 baseEnd_7001362 := by
    simpa [prefixWord, tailWord_7001362, baseEnd_7001362] using wordTrace_append hprefix tailTrace_7001362
  have hstable : (prefixWord ++ tailWord_7001362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001362).length < 2 ^ (prefixWord ++ tailWord_7001362).sum := by decide
  have hdescent : baseEnd_7001362 < baseStart_7001362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001367 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7001367 : Nat := 118140960795 + 7001367 * 2 ^ 59
def prefixEnd_7001367 : Nat := 4983230072969 + 3 ^ 40 * 7001367 * 2
def baseEnd_7001367 : Nat := 3595066509527413853113805

theorem tailTrace_7001367 : CollatzResearch.WordTrace tailWord_7001367 prefixEnd_7001367 3595066509527413853113805 := by
  unfold tailWord_7001367
  simp only [CollatzResearch.WordTrace]
  refine ⟨255360833226250572131122355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170240555484167048087414903 255360833226250572131122355)
  ·
    refine ⟨383041249839375858196683533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255360833226250572131122355 383041249839375858196683533)
    ·
      refine ⟨143640468689765946823756325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383041249839375858196683533 143640468689765946823756325)
      ·
        refine ⟨26932587879331115029454311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143640468689765946823756325 26932587879331115029454311)
        ·
          refine ⟨40398881818996672544181467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26932587879331115029454311 40398881818996672544181467)
          ·
            refine ⟨60598322728495008816272201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40398881818996672544181467 60598322728495008816272201)
            ·
              refine ⟨45448742046371256612204151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60598322728495008816272201 45448742046371256612204151)
              ·
                refine ⟨68173113069556884918306227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45448742046371256612204151 68173113069556884918306227)
                ·
                  refine ⟨102259669604335327377459341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68173113069556884918306227 102259669604335327377459341)
                  ·
                    refine ⟨38347376101625747766547253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102259669604335327377459341 38347376101625747766547253)
                    ·
                      refine ⟨3595066509527413853113805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38347376101625747766547253 3595066509527413853113805)
                      ·
                        rfl

theorem cell23_7001367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7001367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001367 prefixEnd_7001367 := by exact prefixLift 7001367
  have htrace : WordTrace (prefixWord ++ tailWord_7001367) baseStart_7001367 baseEnd_7001367 := by
    simpa [prefixWord, tailWord_7001367, baseEnd_7001367] using wordTrace_append hprefix tailTrace_7001367
  have hstable : (prefixWord ++ tailWord_7001367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001367).length < 2 ^ (prefixWord ++ tailWord_7001367).sum := by decide
  have hdescent : baseEnd_7001367 < baseStart_7001367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001368 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7001368 : Nat := 118140960795 + 7001368 * 2 ^ 59
def prefixEnd_7001368 : Nat := 4983230072969 + 3 ^ 40 * 7001368 * 2
def baseEnd_7001368 : Nat := 3595067023008068349201301

theorem tailTrace_7001368 : CollatzResearch.WordTrace tailWord_7001368 prefixEnd_7001368 3595067023008068349201301 := by
  unfold tailWord_7001368
  simp only [CollatzResearch.WordTrace]
  refine ⟨127680434849623474650954379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170240579799497966201272505 127680434849623474650954379)
  ·
    refine ⟨191520652274435211976431569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127680434849623474650954379 191520652274435211976431569)
    ·
      refine ⟨143640489205826408982323677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191520652274435211976431569 143640489205826408982323677)
      ·
        refine ⟨53865183452184903368371379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143640489205826408982323677 53865183452184903368371379)
        ·
          refine ⟨80797775178277355052557069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53865183452184903368371379 80797775178277355052557069)
          ·
            refine ⟨30299165691854008144708901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80797775178277355052557069 30299165691854008144708901)
            ·
              refine ⟨5681093567222626527132919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30299165691854008144708901 5681093567222626527132919)
              ·
                refine ⟨8521640350833939790699379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681093567222626527132919 8521640350833939790699379)
                ·
                  refine ⟨12782460526250909686049069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521640350833939790699379 12782460526250909686049069)
                  ·
                    refine ⟨4793422697344091132268401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12782460526250909686049069 4793422697344091132268401)
                    ·
                      refine ⟨3595067023008068349201301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793422697344091132268401 3595067023008068349201301)
                      ·
                        rfl

theorem cell23_7001368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7001368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001368 prefixEnd_7001368 := by exact prefixLift 7001368
  have htrace : WordTrace (prefixWord ++ tailWord_7001368) baseStart_7001368 baseEnd_7001368 := by
    simpa [prefixWord, tailWord_7001368, baseEnd_7001368] using wordTrace_append hprefix tailTrace_7001368
  have hstable : (prefixWord ++ tailWord_7001368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001368).length < 2 ^ (prefixWord ++ tailWord_7001368).sum := by decide
  have hdescent : baseEnd_7001368 < baseStart_7001368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001375 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 2, 1, 3]
def baseStart_7001375 : Nat := 118140960795 + 7001375 * 2 ^ 59
def prefixEnd_7001375 : Nat := 4983230072969 + 3 ^ 40 * 7001375 * 2
def baseEnd_7001375 : Nat := 3595070617372649821813769

theorem tailTrace_7001375 : CollatzResearch.WordTrace tailWord_7001375 prefixEnd_7001375 3595070617372649821813769 := by
  unfold tailWord_7001375
  simp only [CollatzResearch.WordTrace]
  refine ⟨255361125010221589497413579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170240750006814392998275719 255361125010221589497413579)
  ·
    refine ⟨383041687515332384246120369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255361125010221589497413579 383041687515332384246120369)
    ·
      refine ⟨287281265636499288184590277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383041687515332384246120369 287281265636499288184590277)
      ·
        refine ⟨53865237306843616534610677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287281265636499288184590277 53865237306843616534610677)
        ·
          refine ⟨5049865997516589050119751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53865237306843616534610677 5049865997516589050119751)
          ·
            refine ⟨7574798996274883575179627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049865997516589050119751 7574798996274883575179627)
            ·
              refine ⟨11362198494412325362769441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7574798996274883575179627 11362198494412325362769441)
              ·
                refine ⟨8521648870809244022077081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11362198494412325362769441 8521648870809244022077081)
                ·
                  refine ⟨6391236653106933016557811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8521648870809244022077081 6391236653106933016557811)
                  ·
                    refine ⟨9586854979660399524836717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391236653106933016557811 9586854979660399524836717)
                    ·
                      refine ⟨3595070617372649821813769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9586854979660399524836717 3595070617372649821813769)
                      ·
                        rfl

theorem cell23_7001375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_7001375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001375 prefixEnd_7001375 := by exact prefixLift 7001375
  have htrace : WordTrace (prefixWord ++ tailWord_7001375) baseStart_7001375 baseEnd_7001375 := by
    simpa [prefixWord, tailWord_7001375, baseEnd_7001375] using wordTrace_append hprefix tailTrace_7001375
  have hstable : (prefixWord ++ tailWord_7001375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001375).length < 2 ^ (prefixWord ++ tailWord_7001375).sum := by decide
  have hdescent : baseEnd_7001375 < baseStart_7001375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001394 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7001394 : Nat := 118140960795 + 7001394 * 2 ^ 59
def prefixEnd_7001394 : Nat := 4983230072969 + 3 ^ 40 * 7001394 * 2
def baseEnd_7001394 : Nat := 3595080373505085247476181

theorem tailTrace_7001394 : CollatzResearch.WordTrace tailWord_7001394 prefixEnd_7001394 3595080373505085247476181 := by
  unfold tailWord_7001394
  simp only [CollatzResearch.WordTrace]
  refine ⟨63840454499288188935588809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170241211998101837161570157 63840454499288188935588809)
  ·
    refine ⟨47880340874466141701691607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63840454499288188935588809 47880340874466141701691607)
    ·
      refine ⟨71820511311699212552537411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47880340874466141701691607 71820511311699212552537411)
      ·
        refine ⟨107730766967548818828806117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71820511311699212552537411 107730766967548818828806117)
        ·
          refine ⟨20199518806415403530401147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107730766967548818828806117 20199518806415403530401147)
          ·
            refine ⟨30299278209623105295601721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20199518806415403530401147 30299278209623105295601721)
            ·
              refine ⟨22724458657217328971701291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30299278209623105295601721 22724458657217328971701291)
              ·
                refine ⟨34086687985825993457551937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22724458657217328971701291 34086687985825993457551937)
                ·
                  refine ⟨25565015989369495093163953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34086687985825993457551937 25565015989369495093163953)
                  ·
                    refine ⟨19173761992027121319872965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25565015989369495093163953 19173761992027121319872965)
                    ·
                      refine ⟨3595080373505085247476181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19173761992027121319872965 3595080373505085247476181)
                      ·
                        rfl

theorem cell23_7001394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7001394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001394 prefixEnd_7001394 := by exact prefixLift 7001394
  have htrace : WordTrace (prefixWord ++ tailWord_7001394) baseStart_7001394 baseEnd_7001394 := by
    simpa [prefixWord, tailWord_7001394, baseEnd_7001394] using wordTrace_append hprefix tailTrace_7001394
  have hstable : (prefixWord ++ tailWord_7001394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001394).length < 2 ^ (prefixWord ++ tailWord_7001394).sum := by decide
  have hdescent : baseEnd_7001394 < baseStart_7001394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001417 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_7001417 : Nat := 118140960795 + 7001417 * 2 ^ 59
def prefixEnd_7001417 : Nat := 4983230072969 + 3 ^ 40 * 7001417 * 2
def baseEnd_7001417 : Nat := 1198364061186712885829525

theorem tailTrace_7001417 : CollatzResearch.WordTrace tailWord_7001417 prefixEnd_7001417 1198364061186712885829525 := by
  unfold tailWord_7001417
  simp only [CollatzResearch.WordTrace]
  refine ⟨255362656876069430670442505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170241771250712953780295003 255362656876069430670442505)
  ·
    refine ⟨191521992657052073002831879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255362656876069430670442505 191521992657052073002831879)
    ·
      refine ⟨287282988985578109504247819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191521992657052073002831879 287282988985578109504247819)
      ·
        refine ⟨430924483478367164256371729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287282988985578109504247819 430924483478367164256371729)
        ·
          refine ⟨323193362608775373192278797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430924483478367164256371729 323193362608775373192278797)
          ·
            refine ⟨121197510978290764947104549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323193362608775373192278797 121197510978290764947104549)
            ·
              refine ⟨22724533308429518427582103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121197510978290764947104549 22724533308429518427582103)
              ·
                refine ⟨34086799962644277641373155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22724533308429518427582103 34086799962644277641373155)
                ·
                  refine ⟨51130199943966416462059733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34086799962644277641373155 51130199943966416462059733)
                  ·
                    refine ⟨1198364061186712885829525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51130199943966416462059733 1198364061186712885829525)
                    ·
                      rfl

theorem cell23_7001417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_7001417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001417 prefixEnd_7001417 := by exact prefixLift 7001417
  have htrace : WordTrace (prefixWord ++ tailWord_7001417) baseStart_7001417 baseEnd_7001417 := by
    simpa [prefixWord, tailWord_7001417, baseEnd_7001417] using wordTrace_append hprefix tailTrace_7001417
  have hstable : (prefixWord ++ tailWord_7001417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001417).length < 2 ^ (prefixWord ++ tailWord_7001417).sum := by decide
  have hdescent : baseEnd_7001417 < baseStart_7001417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001427 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5]
def baseStart_7001427 : Nat := 118140960795 + 7001427 * 2 ^ 59
def prefixEnd_7001427 : Nat := 4983230072969 + 3 ^ 40 * 7001427 * 2
def baseEnd_7001427 : Nat := 3595097318366683618363529

theorem tailTrace_7001427 : CollatzResearch.WordTrace tailWord_7001427 prefixEnd_7001427 3595097318366683618363529 := by
  unfold tailWord_7001427
  simp only [CollatzResearch.WordTrace]
  refine ⟨255363021606033202378306535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170242014404022134918871023 255363021606033202378306535)
  ·
    refine ⟨383044532409049803567459803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255363021606033202378306535 383044532409049803567459803)
    ·
      refine ⟨574566798613574705351189705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383044532409049803567459803 574566798613574705351189705)
      ·
        refine ⟨430925098960181029013392279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574566798613574705351189705 430925098960181029013392279)
        ·
          refine ⟨646387648440271543520088419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430925098960181029013392279 646387648440271543520088419)
          ·
            refine ⟨969581472660407315280132629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646387648440271543520088419 969581472660407315280132629)
            ·
              refine ⟨45449131530956592903756217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 969581472660407315280132629 45449131530956592903756217)
              ·
                refine ⟨34086848648217444677817163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45449131530956592903756217 34086848648217444677817163)
                ·
                  refine ⟨51130272972326167016725745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34086848648217444677817163 51130272972326167016725745)
                  ·
                    refine ⟨38347704729244625262544309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51130272972326167016725745 38347704729244625262544309)
                    ·
                      refine ⟨3595097318366683618363529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38347704729244625262544309 3595097318366683618363529)
                      ·
                        rfl

theorem cell23_7001427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_7001427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001427 prefixEnd_7001427 := by exact prefixLift 7001427
  have htrace : WordTrace (prefixWord ++ tailWord_7001427) baseStart_7001427 baseEnd_7001427 := by
    simpa [prefixWord, tailWord_7001427, baseEnd_7001427] using wordTrace_append hprefix tailTrace_7001427
  have hstable : (prefixWord ++ tailWord_7001427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001427).length < 2 ^ (prefixWord ++ tailWord_7001427).sum := by decide
  have hdescent : baseEnd_7001427 < baseStart_7001427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001444 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_7001444 : Nat := 118140960795 + 7001444 * 2 ^ 59
def prefixEnd_7001444 : Nat := 4983230072969 + 3 ^ 40 * 7001444 * 2
def baseEnd_7001444 : Nat := 3595106047537810051850951

theorem tailTrace_7001444 : CollatzResearch.WordTrace tailWord_7001444 prefixEnd_7001444 3595106047537810051850951 := by
  unfold tailWord_7001444
  simp only [CollatzResearch.WordTrace]
  refine ⟨127681820823485807140837693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170242427764647742854450257 127681820823485807140837693)
  ·
    refine ⟨47880682808807177677814135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127681820823485807140837693 47880682808807177677814135)
    ·
      refine ⟨71821024213210766516721203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47880682808807177677814135 71821024213210766516721203)
      ·
        refine ⟨107731536319816149775081805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71821024213210766516721203 107731536319816149775081805)
        ·
          refine ⟨40399326119931056165655677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107731536319816149775081805 40399326119931056165655677)
          ·
            refine ⟨15149747294974146062120879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40399326119931056165655677 15149747294974146062120879)
            ·
              refine ⟨22724620942461219093181319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15149747294974146062120879 22724620942461219093181319)
              ·
                refine ⟨34086931413691828639771979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22724620942461219093181319 34086931413691828639771979)
                ·
                  refine ⟨51130397120537742959657969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34086931413691828639771979 51130397120537742959657969)
                  ·
                    refine ⟨38347797840403307219743477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51130397120537742959657969 38347797840403307219743477)
                    ·
                      refine ⟨3595106047537810051850951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38347797840403307219743477 3595106047537810051850951)
                      ·
                        rfl

theorem cell23_7001444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_7001444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001444 prefixEnd_7001444 := by exact prefixLift 7001444
  have htrace : WordTrace (prefixWord ++ tailWord_7001444) baseStart_7001444 baseEnd_7001444 := by
    simpa [prefixWord, tailWord_7001444, baseEnd_7001444] using wordTrace_append hprefix tailTrace_7001444
  have hstable : (prefixWord ++ tailWord_7001444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001444).length < 2 ^ (prefixWord ++ tailWord_7001444).sum := by decide
  have hdescent : baseEnd_7001444 < baseStart_7001444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001477 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 10]
def baseStart_7001477 : Nat := 118140960795 + 7001477 * 2 ^ 59
def prefixEnd_7001477 : Nat := 4983230072969 + 3 ^ 40 * 7001477 * 2
def baseEnd_7001477 : Nat := 399458110266600935859811

theorem tailTrace_7001477 : CollatzResearch.WordTrace tailWord_7001477 prefixEnd_7001477 399458110266600935859811 := by
  unfold tailWord_7001477
  simp only [CollatzResearch.WordTrace]
  refine ⟨255364845255852060917626685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170243230170568040611751123 255364845255852060917626685)
  ·
    refine ⟨95761816970944522844110007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255364845255852060917626685 95761816970944522844110007)
    ·
      refine ⟨143642725456416784266165011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95761816970944522844110007 143642725456416784266165011)
      ·
        refine ⟨215464088184625176399247517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143642725456416784266165011 215464088184625176399247517)
        ·
          refine ⟨80799033069234441149717819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215464088184625176399247517 80799033069234441149717819)
          ·
            refine ⟨121198549603851661724576729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80799033069234441149717819 121198549603851661724576729)
            ·
              refine ⟨90898912202888746293432547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121198549603851661724576729 90898912202888746293432547)
              ·
                refine ⟨136348368304333119440148821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90898912202888746293432547 136348368304333119440148821)
                ·
                  refine ⟨399458110266600935859811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136348368304333119440148821 399458110266600935859811)
                  ·
                    rfl

theorem cell23_7001477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_7001477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001477 prefixEnd_7001477 := by exact prefixLift 7001477
  have htrace : WordTrace (prefixWord ++ tailWord_7001477) baseStart_7001477 baseEnd_7001477 := by
    simpa [prefixWord, tailWord_7001477, baseEnd_7001477] using wordTrace_append hprefix tailTrace_7001477
  have hstable : (prefixWord ++ tailWord_7001477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001477).length < 2 ^ (prefixWord ++ tailWord_7001477).sum := by decide
  have hdescent : baseEnd_7001477 < baseStart_7001477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001498 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_7001498 : Nat := 118140960795 + 7001498 * 2 ^ 59
def prefixEnd_7001498 : Nat := 4983230072969 + 3 ^ 40 * 7001498 * 2
def baseEnd_7001498 : Nat := 1198377925164384280191901

theorem tailTrace_7001498 : CollatzResearch.WordTrace tailWord_7001498 prefixEnd_7001498 1198377925164384280191901 := by
  unfold tailWord_7001498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63841402797193995376035287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170243740792517321002760765 63841402797193995376035287)
  ·
    refine ⟨95762104195790993064052931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63841402797193995376035287 95762104195790993064052931)
    ·
      refine ⟨143643156293686489596079397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95762104195790993064052931 143643156293686489596079397)
      ·
        refine ⟨26933091805066216799264887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143643156293686489596079397 26933091805066216799264887)
        ·
          refine ⟨40399637707599325198897331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26933091805066216799264887 40399637707599325198897331)
          ·
            refine ⟨60599456561398987798345997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40399637707599325198897331 60599456561398987798345997)
            ·
              refine ⟨22724796210524620424379749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60599456561398987798345997 22724796210524620424379749)
              ·
                refine ⟨4260899289473366329571203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22724796210524620424379749 4260899289473366329571203)
                ·
                  refine ⟨6391348934210049494356805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260899289473366329571203 6391348934210049494356805)
                  ·
                    refine ⟨1198377925164384280191901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391348934210049494356805 1198377925164384280191901)
                    ·
                      rfl

theorem cell23_7001498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_7001498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001498 prefixEnd_7001498 := by exact prefixLift 7001498
  have htrace : WordTrace (prefixWord ++ tailWord_7001498) baseStart_7001498 baseEnd_7001498 := by
    simpa [prefixWord, tailWord_7001498, baseEnd_7001498] using wordTrace_append hprefix tailTrace_7001498
  have hstable : (prefixWord ++ tailWord_7001498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001498).length < 2 ^ (prefixWord ++ tailWord_7001498).sum := by decide
  have hdescent : baseEnd_7001498 < baseStart_7001498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001534 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7001534 : Nat := 118140960795 + 7001534 * 2 ^ 59
def prefixEnd_7001534 : Nat := 4983230072969 + 3 ^ 40 * 7001534 * 2
def baseEnd_7001534 : Nat := 3595152260796714699725537

theorem tailTrace_7001534 : CollatzResearch.WordTrace tailWord_7001534 prefixEnd_7001534 3595152260796714699725537 := by
  unfold tailWord_7001534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31920865527080694956556457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170244616144430373101634437 31920865527080694956556457)
  ·
    refine ⟨23940649145310521217417343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31920865527080694956556457 23940649145310521217417343)
    ·
      refine ⟨35910973717965781826126015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23940649145310521217417343 35910973717965781826126015)
      ·
        refine ⟨53866460576948672739189023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35910973717965781826126015 53866460576948672739189023)
        ·
          refine ⟨80799690865423009108783535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53866460576948672739189023 80799690865423009108783535)
          ·
            refine ⟨121199536298134513663175303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80799690865423009108783535 121199536298134513663175303)
            ·
              refine ⟨181799304447201770494762955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121199536298134513663175303 181799304447201770494762955)
              ·
                refine ⟨272698956670802655742144433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181799304447201770494762955 272698956670802655742144433)
                ·
                  refine ⟨204524217503101991806608325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272698956670802655742144433 204524217503101991806608325)
                  ·
                    refine ⟨38348290781831623463739061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204524217503101991806608325 38348290781831623463739061)
                    ·
                      refine ⟨3595152260796714699725537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38348290781831623463739061 3595152260796714699725537)
                      ·
                        rfl

theorem cell23_7001534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7001534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001534 prefixEnd_7001534 := by exact prefixLift 7001534
  have htrace : WordTrace (prefixWord ++ tailWord_7001534) baseStart_7001534 baseEnd_7001534 := by
    simpa [prefixWord, tailWord_7001534, baseEnd_7001534] using wordTrace_append hprefix tailTrace_7001534
  have hstable : (prefixWord ++ tailWord_7001534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001534).length < 2 ^ (prefixWord ++ tailWord_7001534).sum := by decide
  have hdescent : baseEnd_7001534 < baseStart_7001534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001571 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 1, 6]
def baseStart_7001571 : Nat := 118140960795 + 7001571 * 2 ^ 59
def prefixEnd_7001571 : Nat := 4983230072969 + 3 ^ 40 * 7001571 * 2
def baseEnd_7001571 : Nat := 1198390419860310351654289

theorem tailTrace_7001571 : CollatzResearch.WordTrace tailWord_7001571 prefixEnd_7001571 1198390419860310351654289 := by
  unfold tailWord_7001571
  simp only [CollatzResearch.WordTrace]
  refine ⟨255368273717511514971548567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170245515811674343314365711 255368273717511514971548567)
  ·
    refine ⟨383052410576267272457322851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255368273717511514971548567 383052410576267272457322851)
    ·
      refine ⟨574578615864400908685984277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383052410576267272457322851 574578615864400908685984277)
      ·
        refine ⟨26933372618643792594655513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 574578615864400908685984277 26933372618643792594655513)
        ·
          refine ⟨20200029463982844445991635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26933372618643792594655513 20200029463982844445991635)
          ·
            refine ⟨30300044195974266668987453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20200029463982844445991635 30300044195974266668987453)
            ·
              refine ⟨11362516573490350000870295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30300044195974266668987453 11362516573490350000870295)
              ·
                refine ⟨17043774860235525001305443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11362516573490350000870295 17043774860235525001305443)
                ·
                  refine ⟨25565662290353287501958165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17043774860235525001305443 25565662290353287501958165)
                  ·
                    refine ⟨1198390419860310351654289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25565662290353287501958165 1198390419860310351654289)
                    ·
                      rfl

theorem cell23_7001571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 6].length) (baseStart_7001571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001571 prefixEnd_7001571 := by exact prefixLift 7001571
  have htrace : WordTrace (prefixWord ++ tailWord_7001571) baseStart_7001571 baseEnd_7001571 := by
    simpa [prefixWord, tailWord_7001571, baseEnd_7001571] using wordTrace_append hprefix tailTrace_7001571
  have hstable : (prefixWord ++ tailWord_7001571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001571).length < 2 ^ (prefixWord ++ tailWord_7001571).sum := by decide
  have hdescent : baseEnd_7001571 < baseStart_7001571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001584 : List Nat := [2, 1, 1, 1, 3, 5, 1, 9]
def baseStart_7001584 : Nat := 118140960795 + 7001584 * 2 ^ 59
def prefixEnd_7001584 : Nat := 4983230072969 + 3 ^ 40 * 7001584 * 2
def baseEnd_7001584 : Nat := 133154738327016277929641

theorem tailTrace_7001584 : CollatzResearch.WordTrace tailWord_7001584 prefixEnd_7001584 133154738327016277929641 := by
  unfold tailWord_7001584
  simp only [CollatzResearch.WordTrace]
  refine ⟨127684373933232209095885903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170245831910976278794514537 127684373933232209095885903)
  ·
    refine ⟨191526560899848313643828855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127684373933232209095885903 191526560899848313643828855)
    ·
      refine ⟨287289841349772470465743283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191526560899848313643828855 287289841349772470465743283)
      ·
        refine ⟨430934762024658705698614925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287289841349772470465743283 430934762024658705698614925)
        ·
          refine ⟨161600535759247014636980597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430934762024658705698614925 161600535759247014636980597)
          ·
            refine ⟨15150050227429407622216931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161600535759247014636980597 15150050227429407622216931)
            ·
              refine ⟨22725075341144111433325397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15150050227429407622216931 22725075341144111433325397)
              ·
                refine ⟨133154738327016277929641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22725075341144111433325397 133154738327016277929641)
                ·
                  rfl

theorem cell23_7001584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 9].length) (baseStart_7001584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001584 prefixEnd_7001584 := by exact prefixLift 7001584
  have htrace : WordTrace (prefixWord ++ tailWord_7001584) baseStart_7001584 baseEnd_7001584 := by
    simpa [prefixWord, tailWord_7001584, baseEnd_7001584] using wordTrace_append hprefix tailTrace_7001584
  have hstable : (prefixWord ++ tailWord_7001584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001584).length < 2 ^ (prefixWord ++ tailWord_7001584).sum := by decide
  have hdescent : baseEnd_7001584 < baseStart_7001584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001589 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7001589 : Nat := 118140960795 + 7001589 * 2 ^ 59
def prefixEnd_7001589 : Nat := 4983230072969 + 3 ^ 40 * 7001589 * 2
def baseEnd_7001589 : Nat := 3595180502232711984537785

theorem tailTrace_7001589 : CollatzResearch.WordTrace tailWord_7001589 prefixEnd_7001589 3595180502232711984537785 := by
  unfold tailWord_7001589
  simp only [CollatzResearch.WordTrace]
  refine ⟨255368930231446304045703821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170245953487630869363802547 255368930231446304045703821)
  ·
    refine ⟨95763348836792364017138933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255368930231446304045703821 95763348836792364017138933)
    ·
      refine ⟨8977813953449284126606775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95763348836792364017138933 8977813953449284126606775)
      ·
        refine ⟨13466720930173926189910163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8977813953449284126606775 13466720930173926189910163)
        ·
          refine ⟨20200081395260889284865245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13466720930173926189910163 20200081395260889284865245)
          ·
            refine ⟨7575030523222833481824467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20200081395260889284865245 7575030523222833481824467)
            ·
              refine ⟨11362545784834250222736701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575030523222833481824467 11362545784834250222736701)
              ·
                refine ⟨4260954669312843833526263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11362545784834250222736701 4260954669312843833526263)
                ·
                  refine ⟨6391432003969265750289395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260954669312843833526263 6391432003969265750289395)
                  ·
                    refine ⟨9587148005953898625434093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391432003969265750289395 9587148005953898625434093)
                    ·
                      refine ⟨3595180502232711984537785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587148005953898625434093 3595180502232711984537785)
                      ·
                        rfl

theorem cell23_7001589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7001589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001589 prefixEnd_7001589 := by exact prefixLift 7001589
  have htrace : WordTrace (prefixWord ++ tailWord_7001589) baseStart_7001589 baseEnd_7001589 := by
    simpa [prefixWord, tailWord_7001589, baseEnd_7001589] using wordTrace_append hprefix tailTrace_7001589
  have hstable : (prefixWord ++ tailWord_7001589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001589).length < 2 ^ (prefixWord ++ tailWord_7001589).sum := by decide
  have hdescent : baseEnd_7001589 < baseStart_7001589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001601 : List Nat := [1, 2, 4, 1, 4, 2, 9]
def baseStart_7001601 : Nat := 118140960795 + 7001601 * 2 ^ 59
def prefixEnd_7001601 : Nat := 4983230072969 + 3 ^ 40 * 7001601 * 2
def baseEnd_7001601 : Nat := 44385020543216863427009

theorem tailTrace_7001601 : CollatzResearch.WordTrace tailWord_7001601 prefixEnd_7001601 44385020543216863427009 := by
  unfold tailWord_7001601
  simp only [CollatzResearch.WordTrace]
  refine ⟨255369367907402830095140657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170246245271601886730093771 255369367907402830095140657)
  ·
    refine ⟨191527025930552122571355493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255369367907402830095140657 191527025930552122571355493)
    ·
      refine ⟨35911317361978522982129155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191527025930552122571355493 35911317361978522982129155)
      ·
        refine ⟨53866976042967784473193733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35911317361978522982129155 53866976042967784473193733)
        ·
          refine ⟨10100058008056459588723825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53866976042967784473193733 10100058008056459588723825)
          ·
            refine ⟨7575043506042344691542869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100058008056459588723825 7575043506042344691542869)
            ·
              refine ⟨44385020543216863427009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7575043506042344691542869 44385020543216863427009)
              ·
                rfl

theorem cell23_7001601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 9].length) (baseStart_7001601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001601 prefixEnd_7001601 := by exact prefixLift 7001601
  have htrace : WordTrace (prefixWord ++ tailWord_7001601) baseStart_7001601 baseEnd_7001601 := by
    simpa [prefixWord, tailWord_7001601, baseEnd_7001601] using wordTrace_append hprefix tailTrace_7001601
  have hstable : (prefixWord ++ tailWord_7001601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001601).length < 2 ^ (prefixWord ++ tailWord_7001601).sum := by decide
  have hdescent : baseEnd_7001601 < baseStart_7001601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001606 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7001606 : Nat := 118140960795 + 7001606 * 2 ^ 59
def prefixEnd_7001606 : Nat := 4983230072969 + 3 ^ 40 * 7001606 * 2
def baseEnd_7001606 : Nat := 3595189231403838418025207

theorem tailTrace_7001606 : CollatzResearch.WordTrace tailWord_7001606 prefixEnd_7001606 3595189231403838418025207 := by
  unfold tailWord_7001606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980298446012022373408521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170246366848256477299381781 7980298446012022373408521)
  ·
    refine ⟨5985223834509016780056391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7980298446012022373408521 5985223834509016780056391)
    ·
      refine ⟨8977835751763525170084587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5985223834509016780056391 8977835751763525170084587)
      ·
        refine ⟨13466753627645287755126881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8977835751763525170084587 13466753627645287755126881)
        ·
          refine ⟨10100065220733965816345161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13466753627645287755126881 10100065220733965816345161)
          ·
            refine ⟨7575048915550474362258871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100065220733965816345161 7575048915550474362258871)
            ·
              refine ⟨11362573373325711543388307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575048915550474362258871 11362573373325711543388307)
              ·
                refine ⟨17043860059988567315082461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11362573373325711543388307 17043860059988567315082461)
                ·
                  refine ⟨6391447522495712743155923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17043860059988567315082461 6391447522495712743155923)
                  ·
                    refine ⟨9587171283743569114733885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391447522495712743155923 9587171283743569114733885)
                    ·
                      refine ⟨3595189231403838418025207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587171283743569114733885 3595189231403838418025207)
                      ·
                        rfl

theorem cell23_7001606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7001606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001606 prefixEnd_7001606 := by exact prefixLift 7001606
  have htrace : WordTrace (prefixWord ++ tailWord_7001606) baseStart_7001606 baseEnd_7001606 := by
    simpa [prefixWord, tailWord_7001606, baseEnd_7001606] using wordTrace_append hprefix tailTrace_7001606
  have hstable : (prefixWord ++ tailWord_7001606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001606).length < 2 ^ (prefixWord ++ tailWord_7001606).sum := by decide
  have hdescent : baseEnd_7001606 < baseStart_7001606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001612 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 3, 2, 2]
def baseStart_7001612 : Nat := 118140960795 + 7001612 * 2 ^ 59
def prefixEnd_7001612 : Nat := 4983230072969 + 3 ^ 40 * 7001612 * 2
def baseEnd_7001612 : Nat := 3595192312287765394550179

theorem tailTrace_7001612 : CollatzResearch.WordTrace tailWord_7001612 prefixEnd_7001612 3595192312287765394550179 := by
  unfold tailWord_7001612
  simp only [CollatzResearch.WordTrace]
  refine ⟨127684884555181489486895545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170246512740241985982527393 127684884555181489486895545)
  ·
    refine ⟨95763663416386117115171659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127684884555181489486895545 95763663416386117115171659)
    ·
      refine ⟨143645495124579175672757489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95763663416386117115171659 143645495124579175672757489)
      ·
        refine ⟨107734121343434381754568117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143645495124579175672757489 107734121343434381754568117)
        ·
          refine ⟨10100073875946973289490761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107734121343434381754568117 10100073875946973289490761)
          ·
            refine ⟨7575055406960229967118071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100073875946973289490761 7575055406960229967118071)
            ·
              refine ⟨11362583110440344950677107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575055406960229967118071 11362583110440344950677107)
              ·
                refine ⟨17043874665660517426015661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11362583110440344950677107 17043874665660517426015661)
                ·
                  refine ⟨6391452999622694034755873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17043874665660517426015661 6391452999622694034755873)
                  ·
                    refine ⟨4793589749717020526066905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6391452999622694034755873 4793589749717020526066905)
                    ·
                      refine ⟨3595192312287765394550179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793589749717020526066905 3595192312287765394550179)
                      ·
                        rfl

theorem cell23_7001612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_7001612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001612 prefixEnd_7001612 := by exact prefixLift 7001612
  have htrace : WordTrace (prefixWord ++ tailWord_7001612) baseStart_7001612 baseEnd_7001612 := by
    simpa [prefixWord, tailWord_7001612, baseEnd_7001612] using wordTrace_append hprefix tailTrace_7001612
  have hstable : (prefixWord ++ tailWord_7001612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001612).length < 2 ^ (prefixWord ++ tailWord_7001612).sum := by decide
  have hdescent : baseEnd_7001612 < baseStart_7001612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001644 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_7001644 : Nat := 118140960795 + 7001644 * 2 ^ 59
def prefixEnd_7001644 : Nat := 4983230072969 + 3 ^ 40 * 7001644 * 2
def baseEnd_7001644 : Nat := 1198402914556236423116677

theorem tailTrace_7001644 : CollatzResearch.WordTrace tailWord_7001644 prefixEnd_7001644 1198402914556236423116677 := by
  unfold tailWord_7001644
  simp only [CollatzResearch.WordTrace]
  refine ⟨127685468123123524219477993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170247290830831365625970657 127685468123123524219477993)
  ·
    refine ⟨95764101092342643164608495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127685468123123524219477993 95764101092342643164608495)
    ·
      refine ⟨143646151638513964746912743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95764101092342643164608495 143646151638513964746912743)
      ·
        refine ⟨215469227457770947120369115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143646151638513964746912743 215469227457770947120369115)
        ·
          refine ⟨323203841186656420680553673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215469227457770947120369115 323203841186656420680553673)
          ·
            refine ⟨242402880889992315510415255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323203841186656420680553673 242402880889992315510415255)
            ·
              refine ⟨363604321334988473265622883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242402880889992315510415255 363604321334988473265622883)
              ·
                refine ⟨545406482002482709898434325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363604321334988473265622883 545406482002482709898434325)
                ·
                  refine ⟨25565928843866377026489109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 545406482002482709898434325 25565928843866377026489109)
                  ·
                    refine ⟨1198402914556236423116677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25565928843866377026489109 1198402914556236423116677)
                    ·
                      rfl

theorem cell23_7001644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_7001644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001644 prefixEnd_7001644 := by exact prefixLift 7001644
  have htrace : WordTrace (prefixWord ++ tailWord_7001644) baseStart_7001644 baseEnd_7001644 := by
    simpa [prefixWord, tailWord_7001644, baseEnd_7001644] using wordTrace_append hprefix tailTrace_7001644
  have hstable : (prefixWord ++ tailWord_7001644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001644).length < 2 ^ (prefixWord ++ tailWord_7001644).sum := by decide
  have hdescent : baseEnd_7001644 < baseStart_7001644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001664 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_7001664 : Nat := 118140960795 + 7001664 * 2 ^ 59
def prefixEnd_7001664 : Nat := 4983230072969 + 3 ^ 40 * 7001664 * 2
def baseEnd_7001664 : Nat := 3595219013281799191099939

theorem tailTrace_7001664 : CollatzResearch.WordTrace tailWord_7001664 prefixEnd_7001664 3595219013281799191099939 := by
  unfold tailWord_7001664
  simp only [CollatzResearch.WordTrace]
  refine ⟨127685832853087295927342023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170247777137449727903122697 127685832853087295927342023)
  ·
    refine ⟨191528749279630943891013035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127685832853087295927342023 191528749279630943891013035)
    ·
      refine ⟨287293123919446415836519553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191528749279630943891013035 287293123919446415836519553)
      ·
        refine ⟨215469842939584811877389665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287293123919446415836519553 215469842939584811877389665)
        ·
          refine ⟨161602382204688608908042249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215469842939584811877389665 161602382204688608908042249)
          ·
            refine ⟨121201786653516456681031687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161602382204688608908042249 121201786653516456681031687)
            ·
              refine ⟨181802679980274685021547531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121201786653516456681031687 181802679980274685021547531)
              ·
                refine ⟨272704019970412027532321297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181802679980274685021547531 272704019970412027532321297)
                ·
                  refine ⟨204528014977809020649240973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272704019970412027532321297 204528014977809020649240973)
                  ·
                    refine ⟨76698005616678382743465365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204528014977809020649240973 76698005616678382743465365)
                    ·
                      refine ⟨3595219013281799191099939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76698005616678382743465365 3595219013281799191099939)
                      ·
                        rfl

theorem cell23_7001664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_7001664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001664 prefixEnd_7001664 := by exact prefixLift 7001664
  have htrace : WordTrace (prefixWord ++ tailWord_7001664) baseStart_7001664 baseEnd_7001664 := by
    simpa [prefixWord, tailWord_7001664, baseEnd_7001664] using wordTrace_append hprefix tailTrace_7001664
  have hstable : (prefixWord ++ tailWord_7001664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001664).length < 2 ^ (prefixWord ++ tailWord_7001664).sum := by decide
  have hdescent : baseEnd_7001664 < baseStart_7001664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001681 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_7001681 : Nat := 118140960795 + 7001681 * 2 ^ 59
def prefixEnd_7001681 : Nat := 4983230072969 + 3 ^ 40 * 7001681 * 2
def baseEnd_7001681 : Nat := 3595227742452925624587361

theorem tailTrace_7001681 : CollatzResearch.WordTrace tailWord_7001681 prefixEnd_7001681 3595227742452925624587361 := by
  unfold tailWord_7001681
  simp only [CollatzResearch.WordTrace]
  refine ⟨255372285747113003758052897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170248190498075335838701931 255372285747113003758052897)
  ·
    refine ⟨191529214310334752818539673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255372285747113003758052897 191529214310334752818539673)
    ·
      refine ⟨143646910732751064613904755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191529214310334752818539673 143646910732751064613904755)
      ·
        refine ⟨215470366099126596920857133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143646910732751064613904755 215470366099126596920857133)
        ·
          refine ⟨80801387287172473845321425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215470366099126596920857133 80801387287172473845321425)
          ·
            refine ⟨60601040465379355383991069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80801387287172473845321425 60601040465379355383991069)
            ·
              refine ⟨22725390174517258268996651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60601040465379355383991069 22725390174517258268996651)
              ·
                refine ⟨34088085261775887403494977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22725390174517258268996651 34088085261775887403494977)
                ·
                  refine ⟨25566063946331915552621233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34088085261775887403494977 25566063946331915552621233)
                  ·
                    refine ⟨19174547959748936664465925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25566063946331915552621233 19174547959748936664465925)
                    ·
                      refine ⟨3595227742452925624587361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19174547959748936664465925 3595227742452925624587361)
                      ·
                        rfl

theorem cell23_7001681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_7001681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001681 prefixEnd_7001681 := by exact prefixLift 7001681
  have htrace : WordTrace (prefixWord ++ tailWord_7001681) baseStart_7001681 baseEnd_7001681 := by
    simpa [prefixWord, tailWord_7001681, baseEnd_7001681] using wordTrace_append hprefix tailTrace_7001681
  have hstable : (prefixWord ++ tailWord_7001681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001681).length < 2 ^ (prefixWord ++ tailWord_7001681).sum := by decide
  have hdescent : baseEnd_7001681 < baseStart_7001681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001721 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_7001721 : Nat := 118140960795 + 7001721 * 2 ^ 59
def prefixEnd_7001721 : Nat := 4983230072969 + 3 ^ 40 * 7001721 * 2
def baseEnd_7001721 : Nat := 1198416093893035156029059

theorem tailTrace_7001721 : CollatzResearch.WordTrace tailWord_7001721 prefixEnd_7001721 1198416093893035156029059 := by
  unfold tailWord_7001721
  simp only [CollatzResearch.WordTrace]
  refine ⟨255373744666968090589509017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170249163111312060393006011 255373744666968090589509017)
  ·
    refine ⟨191530308500226067942131763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255373744666968090589509017 191530308500226067942131763)
    ·
      refine ⟨287295462750339101913197645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191530308500226067942131763 287295462750339101913197645)
      ·
        refine ⟨107735798531377163217449117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287295462750339101913197645 107735798531377163217449117)
        ·
          refine ⟨40400924449266436206543419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107735798531377163217449117 40400924449266436206543419)
          ·
            refine ⟨60601386673899654309815129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40400924449266436206543419 60601386673899654309815129)
            ·
              refine ⟨45451040005424740732361347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60601386673899654309815129 45451040005424740732361347)
              ·
                refine ⟨68176560008137111098542021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45451040005424740732361347 68176560008137111098542021)
                ·
                  refine ⟨12783105001525708330976629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68176560008137111098542021 12783105001525708330976629)
                  ·
                    refine ⟨1198416093893035156029059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12783105001525708330976629 1198416093893035156029059)
                    ·
                      rfl

theorem cell23_7001721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_7001721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001721 prefixEnd_7001721 := by exact prefixLift 7001721
  have htrace : WordTrace (prefixWord ++ tailWord_7001721) baseStart_7001721 baseEnd_7001721 := by
    simpa [prefixWord, tailWord_7001721, baseEnd_7001721] using wordTrace_append hprefix tailTrace_7001721
  have hstable : (prefixWord ++ tailWord_7001721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001721).length < 2 ^ (prefixWord ++ tailWord_7001721).sum := by decide
  have hdescent : baseEnd_7001721 < baseStart_7001721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001736 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7001736 : Nat := 118140960795 + 7001736 * 2 ^ 59
def prefixEnd_7001736 : Nat := 4983230072969 + 3 ^ 40 * 7001736 * 2
def baseEnd_7001736 : Nat := 3595255983888922909399609

theorem tailTrace_7001736 : CollatzResearch.WordTrace tailWord_7001736 prefixEnd_7001736 3595255983888922909399609 := by
  unfold tailWord_7001736
  simp only [CollatzResearch.WordTrace]
  refine ⟨127687145880956874075652531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170249527841275832100870041 127687145880956874075652531)
  ·
    refine ⟨191530718821435311113478797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127687145880956874075652531 191530718821435311113478797)
    ·
      refine ⟨71824019558038241667554549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191530718821435311113478797 71824019558038241667554549)
      ·
        refine ⟨6733501833566085156333239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71824019558038241667554549 6733501833566085156333239)
        ·
          refine ⟨10100252750349127734499859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733501833566085156333239 10100252750349127734499859)
          ·
            refine ⟨15150379125523691601749789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10100252750349127734499859 15150379125523691601749789)
            ·
              refine ⟨5681392172071384350656171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15150379125523691601749789 5681392172071384350656171)
              ·
                refine ⟨8522088258107076525984257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681392172071384350656171 8522088258107076525984257)
                ·
                  refine ⟨6391566193580307394488193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522088258107076525984257 6391566193580307394488193)
                  ·
                    refine ⟨4793674645185230545866145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6391566193580307394488193 4793674645185230545866145)
                    ·
                      refine ⟨3595255983888922909399609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793674645185230545866145 3595255983888922909399609)
                      ·
                        rfl

theorem cell23_7001736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7001736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001736 prefixEnd_7001736 := by exact prefixLift 7001736
  have htrace : WordTrace (prefixWord ++ tailWord_7001736) baseStart_7001736 baseEnd_7001736 := by
    simpa [prefixWord, tailWord_7001736, baseEnd_7001736] using wordTrace_append hprefix tailTrace_7001736
  have hstable : (prefixWord ++ tailWord_7001736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001736).length < 2 ^ (prefixWord ++ tailWord_7001736).sum := by decide
  have hdescent : baseEnd_7001736 < baseStart_7001736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001759 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 5]
def baseStart_7001759 : Nat := 118140960795 + 7001759 * 2 ^ 59
def prefixEnd_7001759 : Nat := 4983230072969 + 3 ^ 40 * 7001759 * 2
def baseEnd_7001759 : Nat := 399474199327108479934667

theorem tailTrace_7001759 : CollatzResearch.WordTrace tailWord_7001759 prefixEnd_7001759 399474199327108479934667 := by
  unfold tailWord_7001759
  simp only [CollatzResearch.WordTrace]
  refine ⟨255375130640830423079392331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170250087093886948719594887 255375130640830423079392331)
  ·
    refine ⟨383062695961245634619088497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255375130640830423079392331 383062695961245634619088497)
    ·
      refine ⟨287297021970934225964316373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383062695961245634619088497 287297021970934225964316373)
      ·
        refine ⟨6733523952443770921038665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 287297021970934225964316373 6733523952443770921038665)
        ·
          refine ⟨5050142964332828190778999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6733523952443770921038665 5050142964332828190778999)
          ·
            refine ⟨7575214446499242286168499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050142964332828190778999 7575214446499242286168499)
            ·
              refine ⟨11362821669748863429252749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575214446499242286168499 11362821669748863429252749)
              ·
                refine ⟨4261058126155823785969781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11362821669748863429252749 4261058126155823785969781)
                ·
                  refine ⟨399474199327108479934667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4261058126155823785969781 399474199327108479934667)
                  ·
                    rfl

theorem cell23_7001759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 5].length) (baseStart_7001759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001759 prefixEnd_7001759 := by exact prefixLift 7001759
  have htrace : WordTrace (prefixWord ++ tailWord_7001759) baseStart_7001759 baseEnd_7001759 := by
    simpa [prefixWord, tailWord_7001759, baseEnd_7001759] using wordTrace_append hprefix tailTrace_7001759
  have hstable : (prefixWord ++ tailWord_7001759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001759).length < 2 ^ (prefixWord ++ tailWord_7001759).sum := by decide
  have hdescent : baseEnd_7001759 < baseStart_7001759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001778 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_7001778 : Nat := 118140960795 + 7001778 * 2 ^ 59
def prefixEnd_7001778 : Nat := 4983230072969 + 3 ^ 40 * 7001778 * 2
def baseEnd_7001778 : Nat := 3595277550076411745074415

theorem tailTrace_7001778 : CollatzResearch.WordTrace tailWord_7001778 prefixEnd_7001778 3595277550076411745074415 := by
  unfold tailWord_7001778
  simp only [CollatzResearch.WordTrace]
  refine ⟨63843955906940397331083497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170250549085174392882889325 63843955906940397331083497)
  ·
    refine ⟨47882966930205297998312623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63843955906940397331083497 47882966930205297998312623)
    ·
      refine ⟨71824450395307946997468935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47882966930205297998312623 71824450395307946997468935)
      ·
        refine ⟨107736675592961920496203403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71824450395307946997468935 107736675592961920496203403)
        ·
          refine ⟨161605013389442880744305105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107736675592961920496203403 161605013389442880744305105)
          ·
            refine ⟨121203760042082160558228829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161605013389442880744305105 121203760042082160558228829)
            ·
              refine ⟨45451410015780810209335811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121203760042082160558228829 45451410015780810209335811)
              ·
                refine ⟨68177115023671215314003717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45451410015780810209335811 68177115023671215314003717)
                ·
                  refine ⟨12783209066938352871375697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68177115023671215314003717 12783209066938352871375697)
                  ·
                    refine ⟨9587406800203764653531773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12783209066938352871375697 9587406800203764653531773)
                    ·
                      refine ⟨3595277550076411745074415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587406800203764653531773 3595277550076411745074415)
                      ·
                        rfl

theorem cell23_7001778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_7001778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001778 prefixEnd_7001778 := by exact prefixLift 7001778
  have htrace : WordTrace (prefixWord ++ tailWord_7001778) baseStart_7001778 baseEnd_7001778 := by
    simpa [prefixWord, tailWord_7001778, baseEnd_7001778] using wordTrace_append hprefix tailTrace_7001778
  have hstable : (prefixWord ++ tailWord_7001778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001778).length < 2 ^ (prefixWord ++ tailWord_7001778).sum := by decide
  have hdescent : baseEnd_7001778 < baseStart_7001778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001785 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 1, 4]
def baseStart_7001785 : Nat := 118140960795 + 7001785 * 2 ^ 59
def prefixEnd_7001785 : Nat := 4983230072969 + 3 ^ 40 * 7001785 * 2
def baseEnd_7001785 : Nat := 1198427048146997739228961

theorem tailTrace_7001785 : CollatzResearch.WordTrace tailWord_7001785 prefixEnd_7001785 1198427048146997739228961 := by
  unfold tailWord_7001785
  simp only [CollatzResearch.WordTrace]
  refine ⟨255376078938736229519838809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170250719292490819679892539 255376078938736229519838809)
  ·
    refine ⟨191532059204052172139879107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255376078938736229519838809 191532059204052172139879107)
    ·
      refine ⟨287298088806078258209818661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191532059204052172139879107 287298088806078258209818661)
      ·
        refine ⟨53868391651139673414340999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287298088806078258209818661 53868391651139673414340999)
        ·
          refine ⟨80802587476709510121511499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53868391651139673414340999 80802587476709510121511499)
          ·
            refine ⟨121203881215064265182267249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80802587476709510121511499 121203881215064265182267249)
            ·
              refine ⟨90902910911298198886700437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121203881215064265182267249 90902910911298198886700437)
              ·
                refine ⟨4261073948967103072814083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90902910911298198886700437 4261073948967103072814083)
                ·
                  refine ⟨6391610923450654609221125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261073948967103072814083 6391610923450654609221125)
                  ·
                    refine ⟨1198427048146997739228961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391610923450654609221125 1198427048146997739228961)
                    ·
                      rfl

theorem cell23_7001785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 4].length) (baseStart_7001785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001785 prefixEnd_7001785 := by exact prefixLift 7001785
  have htrace : WordTrace (prefixWord ++ tailWord_7001785) baseStart_7001785 baseEnd_7001785 := by
    simpa [prefixWord, tailWord_7001785, baseEnd_7001785] using wordTrace_append hprefix tailTrace_7001785
  have hstable : (prefixWord ++ tailWord_7001785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001785).length < 2 ^ (prefixWord ++ tailWord_7001785).sum := by decide
  have hdescent : baseEnd_7001785 < baseStart_7001785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001812 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7001812 : Nat := 118140960795 + 7001812 * 2 ^ 59
def prefixEnd_7001812 : Nat := 4983230072969 + 3 ^ 40 * 7001812 * 2
def baseEnd_7001812 : Nat := 3595295008418664612049259

theorem tailTrace_7001812 : CollatzResearch.WordTrace tailWord_7001812 prefixEnd_7001812 3595295008418664612049259 := by
  unfold tailWord_7001812
  simp only [CollatzResearch.WordTrace]
  refine ⟨127688531854819206565535845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170251375806425608754047793 127688531854819206565535845)
  ·
    refine ⟨23941599722778601231037971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127688531854819206565535845 23941599722778601231037971)
    ·
      refine ⟨35912399584167901846556957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23941599722778601231037971 35912399584167901846556957)
      ·
        refine ⟨13467149844062963192458859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35912399584167901846556957 13467149844062963192458859)
        ·
          refine ⟨20200724766094444788688289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13467149844062963192458859 20200724766094444788688289)
          ·
            refine ⟨15150543574570833591516217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20200724766094444788688289 15150543574570833591516217)
            ·
              refine ⟨11362907680928125193637163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15150543574570833591516217 11362907680928125193637163)
              ·
                refine ⟨17044361521392187790455745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11362907680928125193637163 17044361521392187790455745)
                ·
                  refine ⟨12783271141044140842841809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17044361521392187790455745 12783271141044140842841809)
                  ·
                    refine ⟨9587453355783105632131357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12783271141044140842841809 9587453355783105632131357)
                    ·
                      refine ⟨3595295008418664612049259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587453355783105632131357 3595295008418664612049259)
                      ·
                        rfl

theorem cell23_7001812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7001812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001812 prefixEnd_7001812 := by exact prefixLift 7001812
  have htrace : WordTrace (prefixWord ++ tailWord_7001812) baseStart_7001812 baseEnd_7001812 := by
    simpa [prefixWord, tailWord_7001812, baseEnd_7001812] using wordTrace_append hprefix tailTrace_7001812
  have hstable : (prefixWord ++ tailWord_7001812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001812).length < 2 ^ (prefixWord ++ tailWord_7001812).sum := by decide
  have hdescent : baseEnd_7001812 < baseStart_7001812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001835 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 2, 3, 2]
def baseStart_7001835 : Nat := 118140960795 + 7001835 * 2 ^ 59
def prefixEnd_7001835 : Nat := 4983230072969 + 3 ^ 40 * 7001835 * 2
def baseEnd_7001835 : Nat := 3595306818473718022061653

theorem tailTrace_7001835 : CollatzResearch.WordTrace tailWord_7001835 prefixEnd_7001835 3595306818473718022061653 := by
  unfold tailWord_7001835
  simp only [CollatzResearch.WordTrace]
  refine ⟨255377902588555088059158959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170251935059036725372772639 255377902588555088059158959)
  ·
    refine ⟨383066853882832632088738439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255377902588555088059158959 383066853882832632088738439)
    ·
      refine ⟨574600280824248948133107659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383066853882832632088738439 574600280824248948133107659)
      ·
        refine ⟨861900421236373422199661489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574600280824248948133107659 861900421236373422199661489)
        ·
          refine ⟨646425315927280066649746117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861900421236373422199661489 646425315927280066649746117)
          ·
            refine ⟨121204746736365012496827397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 646425315927280066649746117 121204746736365012496827397)
            ·
              refine ⟨22725890013068439843155137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121204746736365012496827397 22725890013068439843155137)
              ·
                refine ⟨17044417509801329882366353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22725890013068439843155137 17044417509801329882366353)
                ·
                  refine ⟨12783313132350997411774765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17044417509801329882366353 12783313132350997411774765)
                  ·
                    refine ⟨4793742424631624029415537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12783313132350997411774765 4793742424631624029415537)
                    ·
                      refine ⟨3595306818473718022061653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793742424631624029415537 3595306818473718022061653)
                      ·
                        rfl

theorem cell23_7001835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3, 2].length) (baseStart_7001835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001835 prefixEnd_7001835 := by exact prefixLift 7001835
  have htrace : WordTrace (prefixWord ++ tailWord_7001835) baseStart_7001835 baseEnd_7001835 := by
    simpa [prefixWord, tailWord_7001835, baseEnd_7001835] using wordTrace_append hprefix tailTrace_7001835
  have hstable : (prefixWord ++ tailWord_7001835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001835).length < 2 ^ (prefixWord ++ tailWord_7001835).sum := by decide
  have hdescent : baseEnd_7001835 < baseStart_7001835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001881 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_7001881 : Nat := 118140960795 + 7001881 * 2 ^ 59
def prefixEnd_7001881 : Nat := 4983230072969 + 3 ^ 40 * 7001881 * 2
def baseEnd_7001881 : Nat := 3595330438583824842086441

theorem tailTrace_7001881 : CollatzResearch.WordTrace tailWord_7001881 prefixEnd_7001881 3595330438583824842086441 := by
  unfold tailWord_7001881
  simp only [CollatzResearch.WordTrace]
  refine ⟨255379580346388437915333497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170253053564258958610222331 255379580346388437915333497)
  ·
    refine ⟨191534685259791328436500123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255379580346388437915333497 191534685259791328436500123)
    ·
      refine ⟨287302027889686992654750185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191534685259791328436500123 287302027889686992654750185)
      ·
        refine ⟨215476520917265244491062639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287302027889686992654750185 215476520917265244491062639)
        ·
          refine ⟨323214781375897866736593959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215476520917265244491062639 323214781375897866736593959)
          ·
            refine ⟨484822172063846800104890939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323214781375897866736593959 484822172063846800104890939)
            ·
              refine ⟨727233258095770200157336409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484822172063846800104890939 727233258095770200157336409)
              ·
                refine ⟨545424943571827650118002307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727233258095770200157336409 545424943571827650118002307)
                ·
                  refine ⟨818137415357741475177003461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545424943571827650118002307 818137415357741475177003461)
                  ·
                    refine ⟨153400765379576526595688149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818137415357741475177003461 153400765379576526595688149)
                    ·
                      refine ⟨3595330438583824842086441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153400765379576526595688149 3595330438583824842086441)
                      ·
                        rfl

theorem cell23_7001881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_7001881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001881 prefixEnd_7001881 := by exact prefixLift 7001881
  have htrace : WordTrace (prefixWord ++ tailWord_7001881) baseStart_7001881 baseEnd_7001881 := by
    simpa [prefixWord, tailWord_7001881, baseEnd_7001881] using wordTrace_append hprefix tailTrace_7001881
  have hstable : (prefixWord ++ tailWord_7001881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001881).length < 2 ^ (prefixWord ++ tailWord_7001881).sum := by decide
  have hdescent : baseEnd_7001881 < baseStart_7001881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001882 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4]
def baseStart_7001882 : Nat := 118140960795 + 7001882 * 2 ^ 59
def prefixEnd_7001882 : Nat := 4983230072969 + 3 ^ 40 * 7001882 * 2
def baseEnd_7001882 : Nat := 3595330952064479338173937

theorem tailTrace_7001882 : CollatzResearch.WordTrace tailWord_7001882 prefixEnd_7001882 3595330952064479338173937 := by
  unfold tailWord_7001882
  simp only [CollatzResearch.WordTrace]
  refine ⟨63844904204846203771529975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170253077879589876724079933 63844904204846203771529975)
  ·
    refine ⟨95767356307269305657294963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63844904204846203771529975 95767356307269305657294963)
    ·
      refine ⟨143651034460903958485942445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95767356307269305657294963 143651034460903958485942445)
      ·
        refine ⟨53869137922838984432228417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143651034460903958485942445 53869137922838984432228417)
        ·
          refine ⟨40401853442129238324171313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53869137922838984432228417 40401853442129238324171313)
          ·
            refine ⟨30301390081596928743128485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40401853442129238324171313 30301390081596928743128485)
            ·
              refine ⟨5681510640299424139336591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30301390081596928743128485 5681510640299424139336591)
              ·
                refine ⟨8522265960449136209004887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681510640299424139336591 8522265960449136209004887)
                ·
                  refine ⟨12783398940673704313507331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8522265960449136209004887 12783398940673704313507331)
                  ·
                    refine ⟨19175098411010556470260997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12783398940673704313507331 19175098411010556470260997)
                    ·
                      refine ⟨3595330952064479338173937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19175098411010556470260997 3595330952064479338173937)
                      ·
                        rfl

theorem cell23_7001882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_7001882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001882 prefixEnd_7001882 := by exact prefixLift 7001882
  have htrace : WordTrace (prefixWord ++ tailWord_7001882) baseStart_7001882 baseEnd_7001882 := by
    simpa [prefixWord, tailWord_7001882, baseEnd_7001882] using wordTrace_append hprefix tailTrace_7001882
  have hstable : (prefixWord ++ tailWord_7001882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001882).length < 2 ^ (prefixWord ++ tailWord_7001882).sum := by decide
  have hdescent : baseEnd_7001882 < baseStart_7001882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001892 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_7001892 : Nat := 118140960795 + 7001892 * 2 ^ 59
def prefixEnd_7001892 : Nat := 4983230072969 + 3 ^ 40 * 7001892 * 2
def baseEnd_7001892 : Nat := 1198445362290341433016297

theorem tailTrace_7001892 : CollatzResearch.WordTrace tailWord_7001892 prefixEnd_7001892 1198445362290341433016297 := by
  unfold tailWord_7001892
  simp only [CollatzResearch.WordTrace]
  refine ⟨127689990774674293396991965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170253321032899057862655953 127689990774674293396991965)
  ·
    refine ⟨47883746540502860023871987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127689990774674293396991965 47883746540502860023871987)
    ·
      refine ⟨71825619810754290035807981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47883746540502860023871987 71825619810754290035807981)
      ·
        refine ⟨26934607429032858763427993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71825619810754290035807981 26934607429032858763427993)
        ·
          refine ⟨20200955571774644072570995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26934607429032858763427993 20200955571774644072570995)
          ·
            refine ⟨30301433357661966108856493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20200955571774644072570995 30301433357661966108856493)
            ·
              refine ⟨11363037509123237290821185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30301433357661966108856493 11363037509123237290821185)
              ·
                refine ⟨8522278131842427968115889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11363037509123237290821185 8522278131842427968115889)
                ·
                  refine ⟨6391708598881820976086917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522278131842427968115889 6391708598881820976086917)
                  ·
                    refine ⟨1198445362290341433016297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391708598881820976086917 1198445362290341433016297)
                    ·
                      rfl

theorem cell23_7001892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_7001892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001892 prefixEnd_7001892 := by exact prefixLift 7001892
  have htrace : WordTrace (prefixWord ++ tailWord_7001892) baseStart_7001892 baseEnd_7001892 := by
    simpa [prefixWord, tailWord_7001892, baseEnd_7001892] using wordTrace_append hprefix tailTrace_7001892
  have hstable : (prefixWord ++ tailWord_7001892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001892).length < 2 ^ (prefixWord ++ tailWord_7001892).sum := by decide
  have hdescent : baseEnd_7001892 < baseStart_7001892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001902 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7001902 : Nat := 118140960795 + 7001902 * 2 ^ 59
def prefixEnd_7001902 : Nat := 4983230072969 + 3 ^ 40 * 7001902 * 2
def baseEnd_7001902 : Nat := 3595341221677569259923845

theorem tailTrace_7001902 : CollatzResearch.WordTrace tailWord_7001902 prefixEnd_7001902 3595341221677569259923845 := by
  unfold tailWord_7001902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31922543284914044812730995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170253564186208239001231973 31922543284914044812730995)
  ·
    refine ⟨47883814927371067219096493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31922543284914044812730995 47883814927371067219096493)
    ·
      refine ⟨17956430597764150207161185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47883814927371067219096493 17956430597764150207161185)
      ·
        refine ⟨13467322948323112655370889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17956430597764150207161185 13467322948323112655370889)
        ·
          refine ⟨10100492211242334491528167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13467322948323112655370889 10100492211242334491528167)
          ·
            refine ⟨15150738316863501737292251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10100492211242334491528167 15150738316863501737292251)
            ·
              refine ⟨22726107475295252605938377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15150738316863501737292251 22726107475295252605938377)
              ·
                refine ⟨17044580606471439454453783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22726107475295252605938377 17044580606471439454453783)
                ·
                  refine ⟨25566870909707159181680675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17044580606471439454453783 25566870909707159181680675)
                  ·
                    refine ⟨38350306364560738772521013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25566870909707159181680675 38350306364560738772521013)
                    ·
                      refine ⟨3595341221677569259923845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38350306364560738772521013 3595341221677569259923845)
                      ·
                        rfl

theorem cell23_7001902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7001902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001902 prefixEnd_7001902 := by exact prefixLift 7001902
  have htrace : WordTrace (prefixWord ++ tailWord_7001902) baseStart_7001902 baseEnd_7001902 := by
    simpa [prefixWord, tailWord_7001902, baseEnd_7001902] using wordTrace_append hprefix tailTrace_7001902
  have hstable : (prefixWord ++ tailWord_7001902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001902).length < 2 ^ (prefixWord ++ tailWord_7001902).sum := by decide
  have hdescent : baseEnd_7001902 < baseStart_7001902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001909 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_7001909 : Nat := 118140960795 + 7001909 * 2 ^ 59
def prefixEnd_7001909 : Nat := 4983230072969 + 3 ^ 40 * 7001909 * 2
def baseEnd_7001909 : Nat := 1198448272014050244178771

theorem tailTrace_7001909 : CollatzResearch.WordTrace tailWord_7001909 prefixEnd_7001909 1198448272014050244178771 := by
  unfold tailWord_7001909
  simp only [CollatzResearch.WordTrace]
  refine ⟨255380601590286998697352781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170253734393524665798235187 255380601590286998697352781)
  ·
    refine ⟨95767725596357624511507293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255380601590286998697352781 95767725596357624511507293)
    ·
      refine ⟨35912897098634109191815235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95767725596357624511507293 35912897098634109191815235)
      ·
        refine ⟨53869345647951163787722853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35912897098634109191815235 53869345647951163787722853)
        ·
          refine ⟨10100502308990843210198035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53869345647951163787722853 10100502308990843210198035)
          ·
            refine ⟨15150753463486264815297053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10100502308990843210198035 15150753463486264815297053)
            ·
              refine ⟨5681532548807349305736395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15150753463486264815297053 5681532548807349305736395)
              ·
                refine ⟨8522298823211023958604593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681532548807349305736395 8522298823211023958604593)
                ·
                  refine ⟨6391724117408267968953445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522298823211023958604593 6391724117408267968953445)
                  ·
                    refine ⟨1198448272014050244178771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391724117408267968953445 1198448272014050244178771)
                    ·
                      rfl

theorem cell23_7001909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_7001909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001909 prefixEnd_7001909 := by exact prefixLift 7001909
  have htrace : WordTrace (prefixWord ++ tailWord_7001909) baseStart_7001909 baseEnd_7001909 := by
    simpa [prefixWord, tailWord_7001909, baseEnd_7001909] using wordTrace_append hprefix tailTrace_7001909
  have hstable : (prefixWord ++ tailWord_7001909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001909).length < 2 ^ (prefixWord ++ tailWord_7001909).sum := by decide
  have hdescent : baseEnd_7001909 < baseStart_7001909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001928 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_7001928 : Nat := 118140960795 + 7001928 * 2 ^ 59
def prefixEnd_7001928 : Nat := 4983230072969 + 3 ^ 40 * 7001928 * 2
def baseEnd_7001928 : Nat := 3595354572174586158198725

theorem tailTrace_7001928 : CollatzResearch.WordTrace tailWord_7001928 prefixEnd_7001928 3595354572174586158198725 := by
  unfold tailWord_7001928
  simp only [CollatzResearch.WordTrace]
  refine ⟨127690647288609082471147219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170254196384812109961529625 127690647288609082471147219)
  ·
    refine ⟨191535970932913623706720829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127690647288609082471147219 191535970932913623706720829)
    ·
      refine ⟨71825989099842608890020311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191535970932913623706720829 71825989099842608890020311)
      ·
        refine ⟨107738983649763913335030467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71825989099842608890020311 107738983649763913335030467)
        ·
          refine ⟨161608475474645870002545701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107738983649763913335030467 161608475474645870002545701)
          ·
            refine ⟨30301589151496100625477319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161608475474645870002545701 30301589151496100625477319)
            ·
              refine ⟨45452383727244150938215979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30301589151496100625477319 45452383727244150938215979)
              ·
                refine ⟨68178575590866226407323969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45452383727244150938215979 68178575590866226407323969)
                ·
                  refine ⟨51133931693149669805492977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68178575590866226407323969 51133931693149669805492977)
                  ·
                    refine ⟨38350448769862252354119733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51133931693149669805492977 38350448769862252354119733)
                    ·
                      refine ⟨3595354572174586158198725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38350448769862252354119733 3595354572174586158198725)
                      ·
                        rfl

theorem cell23_7001928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_7001928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001928 prefixEnd_7001928 := by exact prefixLift 7001928
  have htrace : WordTrace (prefixWord ++ tailWord_7001928) baseStart_7001928 baseEnd_7001928 := by
    simpa [prefixWord, tailWord_7001928, baseEnd_7001928] using wordTrace_append hprefix tailTrace_7001928
  have hstable : (prefixWord ++ tailWord_7001928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001928).length < 2 ^ (prefixWord ++ tailWord_7001928).sum := by decide
  have hdescent : baseEnd_7001928 < baseStart_7001928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001933 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7001933 : Nat := 118140960795 + 7001933 * 2 ^ 59
def prefixEnd_7001933 : Nat := 4983230072969 + 3 ^ 40 * 7001933 * 2
def baseEnd_7001933 : Nat := 3595357139577858638636203

theorem tailTrace_7001933 : CollatzResearch.WordTrace tailWord_7001933 prefixEnd_7001933 3595357139577858638636203 := by
  unfold tailWord_7001933
  simp only [CollatzResearch.WordTrace]
  refine ⟨255381476942200050796226453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170254317961466700530817635 255381476942200050796226453)
  ·
    refine ⟨11971006731665627381073115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255381476942200050796226453 11971006731665627381073115)
    ·
      refine ⟨17956510097498441071609673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11971006731665627381073115 17956510097498441071609673)
      ·
        refine ⟨13467382573123830803707255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17956510097498441071609673 13467382573123830803707255)
        ·
          refine ⟨20201073859685746205560883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13467382573123830803707255 20201073859685746205560883)
          ·
            refine ⟨30301610789528619308341325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20201073859685746205560883 30301610789528619308341325)
            ·
              refine ⟨11363104046073232240627997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30301610789528619308341325 11363104046073232240627997)
              ·
                refine ⟨4261164017277462090235499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11363104046073232240627997 4261164017277462090235499)
                ·
                  refine ⟨6391746025916193135353249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261164017277462090235499 6391746025916193135353249)
                  ·
                    refine ⟨4793809519437144851514937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6391746025916193135353249 4793809519437144851514937)
                    ·
                      refine ⟨3595357139577858638636203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793809519437144851514937 3595357139577858638636203)
                      ·
                        rfl

theorem cell23_7001933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7001933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001933 prefixEnd_7001933 := by exact prefixLift 7001933
  have htrace : WordTrace (prefixWord ++ tailWord_7001933) baseStart_7001933 baseEnd_7001933 := by
    simpa [prefixWord, tailWord_7001933, baseEnd_7001933] using wordTrace_append hprefix tailTrace_7001933
  have hstable : (prefixWord ++ tailWord_7001933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001933).length < 2 ^ (prefixWord ++ tailWord_7001933).sum := by decide
  have hdescent : baseEnd_7001933 < baseStart_7001933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001966 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7001966 : Nat := 118140960795 + 7001966 * 2 ^ 59
def prefixEnd_7001966 : Nat := 4983230072969 + 3 ^ 40 * 7001966 * 2
def baseEnd_7001966 : Nat := 3595374084439457009523551

theorem tailTrace_7001966 : CollatzResearch.WordTrace tailWord_7001966 prefixEnd_7001966 3595374084439457009523551 := by
  unfold tailWord_7001966
  simp only [CollatzResearch.WordTrace]
  refine ⟨31922835068885062179022219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170255120367386998288118501 31922835068885062179022219)
  ·
    refine ⟨47884252603327593268533329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31922835068885062179022219 47884252603327593268533329)
    ·
      refine ⟨35913189452495694951399997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47884252603327593268533329 35913189452495694951399997)
      ·
        refine ⟨13467446044685885606774999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35913189452495694951399997 13467446044685885606774999)
        ·
          refine ⟨20201169067028828410162499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13467446044685885606774999 20201169067028828410162499)
          ·
            refine ⟨30301753600543242615243749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20201169067028828410162499 30301753600543242615243749)
            ·
              refine ⟨5681578800101857990358203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30301753600543242615243749 5681578800101857990358203)
              ·
                refine ⟨8522368200152786985537305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681578800101857990358203 8522368200152786985537305)
                ·
                  refine ⟨6391776150114590239152979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522368200152786985537305 6391776150114590239152979)
                  ·
                    refine ⟨9587664225171885358729469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391776150114590239152979 9587664225171885358729469)
                    ·
                      refine ⟨3595374084439457009523551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587664225171885358729469 3595374084439457009523551)
                      ·
                        rfl

theorem cell23_7001966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7001966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001966 prefixEnd_7001966 := by exact prefixLift 7001966
  have htrace : WordTrace (prefixWord ++ tailWord_7001966) baseStart_7001966 baseEnd_7001966 := by
    simpa [prefixWord, tailWord_7001966, baseEnd_7001966] using wordTrace_append hprefix tailTrace_7001966
  have hstable : (prefixWord ++ tailWord_7001966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001966).length < 2 ^ (prefixWord ++ tailWord_7001966).sum := by decide
  have hdescent : baseEnd_7001966 < baseStart_7001966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001968 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_7001968 : Nat := 118140960795 + 7001968 * 2 ^ 59
def prefixEnd_7001968 : Nat := 4983230072969 + 3 ^ 40 * 7001968 * 2
def baseEnd_7001968 : Nat := 3595375111400766001698541

theorem tailTrace_7001968 : CollatzResearch.WordTrace tailWord_7001968 prefixEnd_7001968 3595375111400766001698541 := by
  unfold tailWord_7001968
  simp only [CollatzResearch.WordTrace]
  refine ⟨127691376748536625886875279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170255168998048834515833705 127691376748536625886875279)
  ·
    refine ⟨191537065122804938830312919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127691376748536625886875279 191537065122804938830312919)
    ·
      refine ⟨287305597684207408245469379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191537065122804938830312919 287305597684207408245469379)
      ·
        refine ⟨430958396526311112368204069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287305597684207408245469379 430958396526311112368204069)
        ·
          refine ⟨80804699348683333569038263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430958396526311112368204069 80804699348683333569038263)
          ·
            refine ⟨121207049023025000353557395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80804699348683333569038263 121207049023025000353557395)
            ·
              refine ⟨181810573534537500530336093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121207049023025000353557395 181810573534537500530336093)
              ·
                refine ⟨68178965075451562698876035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181810573534537500530336093 68178965075451562698876035)
                ·
                  refine ⟨102268447613177344048314053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68178965075451562698876035 102268447613177344048314053)
                  ·
                    refine ⟨19175333927470752009058885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102268447613177344048314053 19175333927470752009058885)
                    ·
                      refine ⟨3595375111400766001698541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19175333927470752009058885 3595375111400766001698541)
                      ·
                        rfl

theorem cell23_7001968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_7001968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001968 prefixEnd_7001968 := by exact prefixLift 7001968
  have htrace : WordTrace (prefixWord ++ tailWord_7001968) baseStart_7001968 baseEnd_7001968 := by
    simpa [prefixWord, tailWord_7001968, baseEnd_7001968] using wordTrace_append hprefix tailTrace_7001968
  have hstable : (prefixWord ++ tailWord_7001968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001968).length < 2 ^ (prefixWord ++ tailWord_7001968).sum := by decide
  have hdescent : baseEnd_7001968 < baseStart_7001968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001978 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_7001978 : Nat := 118140960795 + 7001978 * 2 ^ 59
def prefixEnd_7001978 : Nat := 4983230072969 + 3 ^ 40 * 7001978 * 2
def baseEnd_7001978 : Nat := 399486694023034551397055

theorem tailTrace_7001978 : CollatzResearch.WordTrace tailWord_7001978 prefixEnd_7001978 399486694023034551397055 := by
  unfold tailWord_7001978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63845779556759255870403647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170255412151358015654409725 63845779556759255870403647)
  ·
    refine ⟨95768669335138883805605471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63845779556759255870403647 95768669335138883805605471)
    ·
      refine ⟨143653004002708325708408207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95768669335138883805605471 143653004002708325708408207)
      ·
        refine ⟨215479506004062488562612311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143653004002708325708408207 215479506004062488562612311)
        ·
          refine ⟨323219259006093732843918467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215479506004062488562612311 323219259006093732843918467)
          ·
            refine ⟨484828888509140599265877701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323219259006093732843918467 484828888509140599265877701)
            ·
              refine ⟨90905416595463862362352069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484828888509140599265877701 90905416595463862362352069)
              ·
                refine ⟨17044765611649474192941013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90905416595463862362352069 17044765611649474192941013)
                ·
                  refine ⟨399486694023034551397055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17044765611649474192941013 399486694023034551397055)
                  ·
                    rfl

theorem cell23_7001978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_7001978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001978 prefixEnd_7001978 := by exact prefixLift 7001978
  have htrace : WordTrace (prefixWord ++ tailWord_7001978) baseStart_7001978 baseEnd_7001978 := by
    simpa [prefixWord, tailWord_7001978, baseEnd_7001978] using wordTrace_append hprefix tailTrace_7001978
  have hstable : (prefixWord ++ tailWord_7001978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001978).length < 2 ^ (prefixWord ++ tailWord_7001978).sum := by decide
  have hdescent : baseEnd_7001978 < baseStart_7001978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7001995 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 5]
def baseStart_7001995 : Nat := 118140960795 + 7001995 * 2 ^ 59
def prefixEnd_7001995 : Nat := 4983230072969 + 3 ^ 40 * 7001995 * 2
def baseEnd_7001995 : Nat := 399487663930937488451213

theorem tailTrace_7001995 : CollatzResearch.WordTrace tailWord_7001995 prefixEnd_7001995 399487663930937488451213 := by
  unfold tailWord_7001995
  simp only [CollatzResearch.WordTrace]
  refine ⟨255383738267975435384983439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170255825511983623589988959 255383738267975435384983439)
  ·
    refine ⟨383075607401963153077475159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255383738267975435384983439 383075607401963153077475159)
    ·
      refine ⟨574613411102944729616212739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383075607401963153077475159 574613411102944729616212739)
      ·
        refine ⟨861920116654417094424319109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574613411102944729616212739 861920116654417094424319109)
        ·
          refine ⟨161610021872703205204559833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 861920116654417094424319109 161610021872703205204559833)
          ·
            refine ⟨121207516404527403903419875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161610021872703205204559833 121207516404527403903419875)
            ·
              refine ⟨181811274606791105855129813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121207516404527403903419875 181811274606791105855129813)
              ·
                refine ⟨4261201748596666543479605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181811274606791105855129813 4261201748596666543479605)
                ·
                  refine ⟨399487663930937488451213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4261201748596666543479605 399487663930937488451213)
                  ·
                    rfl

theorem cell23_7001995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 5].length) (baseStart_7001995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7001995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7001995 prefixEnd_7001995 := by exact prefixLift 7001995
  have htrace : WordTrace (prefixWord ++ tailWord_7001995) baseStart_7001995 baseEnd_7001995 := by
    simpa [prefixWord, tailWord_7001995, baseEnd_7001995] using wordTrace_append hprefix tailTrace_7001995
  have hstable : (prefixWord ++ tailWord_7001995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7001995).length < 2 ^ (prefixWord ++ tailWord_7001995).sum := by decide
  have hdescent : baseEnd_7001995 < baseStart_7001995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7001995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002005 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_7002005 : Nat := 118140960795 + 7002005 * 2 ^ 59
def prefixEnd_7002005 : Nat := 4983230072969 + 3 ^ 40 * 7002005 * 2
def baseEnd_7002005 : Nat := 3595394110184982356935871

theorem tailTrace_7002005 : CollatzResearch.WordTrace tailWord_7002005 prefixEnd_7002005 3595394110184982356935871 := by
  unfold tailWord_7002005
  simp only [CollatzResearch.WordTrace]
  refine ⟨255384102997939207092847469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170256068665292804728564979 255384102997939207092847469)
  ·
    refine ⟨95769038624227202659817801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255384102997939207092847469 95769038624227202659817801)
    ·
      refine ⟨71826778968170401994863351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95769038624227202659817801 71826778968170401994863351)
      ·
        refine ⟨107740168452255602992295027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71826778968170401994863351 107740168452255602992295027)
        ·
          refine ⟨161610252678383404488442541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107740168452255602992295027 161610252678383404488442541)
          ·
            refine ⟨60603844754393776683165953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161610252678383404488442541 60603844754393776683165953)
            ·
              refine ⟨45452883565795332512374465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60603844754393776683165953 45452883565795332512374465)
              ·
                refine ⟨34089662674346499384280849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45452883565795332512374465 34089662674346499384280849)
                ·
                  refine ⟨25567247005759874538210637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34089662674346499384280849 25567247005759874538210637)
                  ·
                    refine ⟨9587717627159952951828989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25567247005759874538210637 9587717627159952951828989)
                    ·
                      refine ⟨3595394110184982356935871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587717627159952951828989 3595394110184982356935871)
                      ·
                        rfl

theorem cell23_7002005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_7002005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002005 prefixEnd_7002005 := by exact prefixLift 7002005
  have htrace : WordTrace (prefixWord ++ tailWord_7002005) baseStart_7002005 baseEnd_7002005 := by
    simpa [prefixWord, tailWord_7002005, baseEnd_7002005] using wordTrace_append hprefix tailTrace_7002005
  have hstable : (prefixWord ++ tailWord_7002005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002005).length < 2 ^ (prefixWord ++ tailWord_7002005).sum := by decide
  have hdescent : baseEnd_7002005 < baseStart_7002005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002055 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 7, 4]
def baseStart_7002055 : Nat := 118140960795 + 7002055 * 2 ^ 59
def prefixEnd_7002055 : Nat := 4983230072969 + 3 ^ 40 * 7002055 * 2
def baseEnd_7002055 : Nat := 1198473261405902387103547

theorem tailTrace_7002055 : CollatzResearch.WordTrace tailWord_7002055 prefixEnd_7002055 1198473261405902387103547 := by
  unfold tailWord_7002055
  simp only [CollatzResearch.WordTrace]
  refine ⟨255385926647758065632167619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170257284431838710421445079 255385926647758065632167619)
  ·
    refine ⟨383078889971637098448251429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255385926647758065632167619 383078889971637098448251429)
    ·
      refine ⟨71827291869681955959047143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383078889971637098448251429 71827291869681955959047143)
      ·
        refine ⟨107740937804522933938570715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71827291869681955959047143 107740937804522933938570715)
        ·
          refine ⟨161611406706784400907856073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107740937804522933938570715 161611406706784400907856073)
          ·
            refine ⟨121208555030088300680892055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161611406706784400907856073 121208555030088300680892055)
            ·
              refine ⟨181812832545132451021338083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121208555030088300680892055 181812832545132451021338083)
              ·
                refine ⟨272719248817698676532007125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181812832545132451021338083 272719248817698676532007125)
                ·
                  refine ⟨6391857394164812731218917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 272719248817698676532007125 6391857394164812731218917)
                  ·
                    refine ⟨1198473261405902387103547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391857394164812731218917 1198473261405902387103547)
                    ·
                      rfl

theorem cell23_7002055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_7002055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002055 prefixEnd_7002055 := by exact prefixLift 7002055
  have htrace : WordTrace (prefixWord ++ tailWord_7002055) baseStart_7002055 baseEnd_7002055 := by
    simpa [prefixWord, tailWord_7002055, baseEnd_7002055] using wordTrace_append hprefix tailTrace_7002055
  have hstable : (prefixWord ++ tailWord_7002055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002055).length < 2 ^ (prefixWord ++ tailWord_7002055).sum := by decide
  have hdescent : baseEnd_7002055 < baseStart_7002055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002062 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_7002062 : Nat := 118140960795 + 7002062 * 2 ^ 59
def prefixEnd_7002062 : Nat := 4983230072969 + 3 ^ 40 * 7002062 * 2
def baseEnd_7002062 : Nat := 3595423378582288633923109

theorem tailTrace_7002062 : CollatzResearch.WordTrace tailWord_7002062 prefixEnd_7002062 3595423378582288633923109 := by
  unfold tailWord_7002062
  simp only [CollatzResearch.WordTrace]
  refine ⟨31923272744841588228459055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170257454639155137218448293 31923272744841588228459055)
  ·
    refine ⟨47884909117262382342688583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31923272744841588228459055 47884909117262382342688583)
    ·
      refine ⟨71827363675893573514032875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47884909117262382342688583 71827363675893573514032875)
      ·
        refine ⟨107741045513840360271049313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71827363675893573514032875 107741045513840360271049313)
        ·
          refine ⟨80805784135380270203286985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107741045513840360271049313 80805784135380270203286985)
          ·
            refine ⟨60604338101535202652465239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80805784135380270203286985 60604338101535202652465239)
            ·
              refine ⟨90906507152302803978697859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60604338101535202652465239 90906507152302803978697859)
              ·
                refine ⟨136359760728454205968046789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90906507152302803978697859 136359760728454205968046789)
                ·
                  refine ⟨25567455136585163619008773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136359760728454205968046789 25567455136585163619008773)
                  ·
                    refine ⟨4793897838109718178564145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25567455136585163619008773 4793897838109718178564145)
                    ·
                      refine ⟨3595423378582288633923109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4793897838109718178564145 3595423378582288633923109)
                      ·
                        rfl

theorem cell23_7002062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_7002062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002062 prefixEnd_7002062 := by exact prefixLift 7002062
  have htrace : WordTrace (prefixWord ++ tailWord_7002062) baseStart_7002062 baseEnd_7002062 := by
    simpa [prefixWord, tailWord_7002062, baseEnd_7002062] using wordTrace_append hprefix tailTrace_7002062
  have hstable : (prefixWord ++ tailWord_7002062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002062).length < 2 ^ (prefixWord ++ tailWord_7002062).sum := by decide
  have hdescent : baseEnd_7002062 < baseStart_7002062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002072 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 3, 4]
def baseStart_7002072 : Nat := 118140960795 + 7002072 * 2 ^ 59
def prefixEnd_7002072 : Nat := 4983230072969 + 3 ^ 40 * 7002072 * 2
def baseEnd_7002072 : Nat := 1198476171129611198266021

theorem tailTrace_7002072 : CollatzResearch.WordTrace tailWord_7002072 prefixEnd_7002072 1198476171129611198266021 := by
  unfold tailWord_7002072
  simp only [CollatzResearch.WordTrace]
  refine ⟨127693273344348238767768235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170257697792464318357024313 127693273344348238767768235)
  ·
    refine ⟨191539910016522358151652353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127693273344348238767768235 191539910016522358151652353)
    ·
      refine ⟨143654932512391768613739265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191539910016522358151652353 143654932512391768613739265)
      ·
        refine ⟨107741199384293826460304449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143654932512391768613739265 107741199384293826460304449)
        ·
          refine ⟨80805899538220369845228337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107741199384293826460304449 80805899538220369845228337)
          ·
            refine ⟨60604424653665277383921253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80805899538220369845228337 60604424653665277383921253)
            ·
              refine ⟨11363329622562239509485235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60604424653665277383921253 11363329622562239509485235)
              ·
                refine ⟨17044994433843359264227853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11363329622562239509485235 17044994433843359264227853)
                ·
                  refine ⟨6391872912691259724085445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17044994433843359264227853 6391872912691259724085445)
                  ·
                    refine ⟨1198476171129611198266021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391872912691259724085445 1198476171129611198266021)
                    ·
                      rfl

theorem cell23_7002072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_7002072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002072 prefixEnd_7002072 := by exact prefixLift 7002072
  have htrace : WordTrace (prefixWord ++ tailWord_7002072) baseStart_7002072 baseEnd_7002072 := by
    simpa [prefixWord, tailWord_7002072, baseEnd_7002072] using wordTrace_append hprefix tailTrace_7002072
  have hstable : (prefixWord ++ tailWord_7002072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002072).length < 2 ^ (prefixWord ++ tailWord_7002072).sum := by decide
  have hdescent : baseEnd_7002072 < baseStart_7002072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002095 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_7002095 : Nat := 118140960795 + 7002095 * 2 ^ 59
def prefixEnd_7002095 : Nat := 4983230072969 + 3 ^ 40 * 7002095 * 2
def baseEnd_7002095 : Nat := 3595440323443887004810457

theorem tailTrace_7002095 : CollatzResearch.WordTrace tailWord_7002095 prefixEnd_7002095 3595440323443887004810457 := by
  unfold tailWord_7002095
  simp only [CollatzResearch.WordTrace]
  refine ⟨255387385567613152463623739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170258257045075434975749159 255387385567613152463623739)
  ·
    refine ⟨383081078351419728695435609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255387385567613152463623739 383081078351419728695435609)
    ·
      refine ⟨287310808763564796521576707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383081078351419728695435609 287310808763564796521576707)
      ·
        refine ⟨430966213145347194782365061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287310808763564796521576707 430966213145347194782365061)
        ·
          refine ⟨80806164964752599021693449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430966213145347194782365061 80806164964752599021693449)
          ·
            refine ⟨60604623723564449266270087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80806164964752599021693449 60604623723564449266270087)
            ·
              refine ⟨90906935585346673899405131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60604623723564449266270087 90906935585346673899405131)
              ·
                refine ⟨136360403378020010849107697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90906935585346673899405131 136360403378020010849107697)
                ·
                  refine ⟨102270302533515008136830773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136360403378020010849107697 102270302533515008136830773)
                  ·
                    refine ⟨9587840862517032012827885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102270302533515008136830773 9587840862517032012827885)
                    ·
                      refine ⟨3595440323443887004810457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587840862517032012827885 3595440323443887004810457)
                      ·
                        rfl

theorem cell23_7002095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_7002095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002095 prefixEnd_7002095 := by exact prefixLift 7002095
  have htrace : WordTrace (prefixWord ++ tailWord_7002095) baseStart_7002095 baseEnd_7002095 := by
    simpa [prefixWord, tailWord_7002095, baseEnd_7002095] using wordTrace_append hprefix tailTrace_7002095
  have hstable : (prefixWord ++ tailWord_7002095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002095).length < 2 ^ (prefixWord ++ tailWord_7002095).sum := by decide
  have hdescent : baseEnd_7002095 < baseStart_7002095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002116 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7002116 : Nat := 118140960795 + 7002116 * 2 ^ 59
def prefixEnd_7002116 : Nat := 4983230072969 + 3 ^ 40 * 7002116 * 2
def baseEnd_7002116 : Nat := 3595451106537631422647861

theorem tailTrace_7002116 : CollatzResearch.WordTrace tailWord_7002116 prefixEnd_7002116 3595451106537631422647861 := by
  unfold tailWord_7002116
  simp only [CollatzResearch.WordTrace]
  refine ⟨127694075750268536525069101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170258767667024715366758801 127694075750268536525069101)
  ·
    refine ⟨47885278406350701196900913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127694075750268536525069101 47885278406350701196900913)
    ·
      refine ⟨35913958804763025897675685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47885278406350701196900913 35913958804763025897675685)
      ·
        refine ⟨6733867275893067355814191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35913958804763025897675685 6733867275893067355814191)
        ·
          refine ⟨10100800913839601033721287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733867275893067355814191 10100800913839601033721287)
          ·
            refine ⟨15151201370759401550581931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10100800913839601033721287 15151201370759401550581931)
            ·
              refine ⟨22726802056139102325872897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15151201370759401550581931 22726802056139102325872897)
              ·
                refine ⟨17045101542104326744404673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22726802056139102325872897 17045101542104326744404673)
                ·
                  refine ⟨12783826156578245058303505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17045101542104326744404673 12783826156578245058303505)
                  ·
                    refine ⟨9587869617433683793727629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12783826156578245058303505 9587869617433683793727629)
                    ·
                      refine ⟨3595451106537631422647861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587869617433683793727629 3595451106537631422647861)
                      ·
                        rfl

theorem cell23_7002116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7002116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002116 prefixEnd_7002116 := by exact prefixLift 7002116
  have htrace : WordTrace (prefixWord ++ tailWord_7002116) baseStart_7002116 baseEnd_7002116 := by
    simpa [prefixWord, tailWord_7002116, baseEnd_7002116] using wordTrace_append hprefix tailTrace_7002116
  have hstable : (prefixWord ++ tailWord_7002116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002116).length < 2 ^ (prefixWord ++ tailWord_7002116).sum := by decide
  have hdescent : baseEnd_7002116 < baseStart_7002116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002149 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_7002149 : Nat := 118140960795 + 7002149 * 2 ^ 59
def prefixEnd_7002149 : Nat := 4983230072969 + 3 ^ 40 * 7002149 * 2
def baseEnd_7002149 : Nat := 1198489350466409931178403

theorem tailTrace_7002149 : CollatzResearch.WordTrace tailWord_7002149 prefixEnd_7002149 1198489350466409931178403 := by
  unfold tailWord_7002149
  simp only [CollatzResearch.WordTrace]
  refine ⟨255389355109417519686089501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170259570072945013124059667 255389355109417519686089501)
  ·
    refine ⟨95771008166031569882283563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255389355109417519686089501 95771008166031569882283563)
    ·
      refine ⟨143656512249047354823425345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95771008166031569882283563 143656512249047354823425345)
      ·
        refine ⟨107742384186785516117569009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143656512249047354823425345 107742384186785516117569009)
        ·
          refine ⟨80806788140089137088176757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107742384186785516117569009 80806788140089137088176757)
          ·
            refine ⟨7575636388133356602016571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80806788140089137088176757 7575636388133356602016571)
            ·
              refine ⟨11363454582200034903024857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575636388133356602016571 11363454582200034903024857)
              ·
                refine ⟨8522590936650026177268643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11363454582200034903024857 8522590936650026177268643)
                ·
                  refine ⟨12783886404975039265902965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8522590936650026177268643 12783886404975039265902965)
                  ·
                    refine ⟨1198489350466409931178403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12783886404975039265902965 1198489350466409931178403)
                    ·
                      rfl

theorem cell23_7002149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_7002149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002149 prefixEnd_7002149 := by exact prefixLift 7002149
  have htrace : WordTrace (prefixWord ++ tailWord_7002149) baseStart_7002149 baseEnd_7002149 := by
    simpa [prefixWord, tailWord_7002149, baseEnd_7002149] using wordTrace_append hprefix tailTrace_7002149
  have hstable : (prefixWord ++ tailWord_7002149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002149).length < 2 ^ (prefixWord ++ tailWord_7002149).sum := by decide
  have hdescent : baseEnd_7002149 < baseStart_7002149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002162 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_7002162 : Nat := 118140960795 + 7002162 * 2 ^ 59
def prefixEnd_7002162 : Nat := 4983230072969 + 3 ^ 40 * 7002162 * 2
def baseEnd_7002162 : Nat := 1198491575549246080890883

theorem tailTrace_7002162 : CollatzResearch.WordTrace tailWord_7002162 prefixEnd_7002162 1198491575549246080890883 := by
  unfold tailWord_7002162
  simp only [CollatzResearch.WordTrace]
  refine ⟨63847457314592605726578185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170259886172246948604208493 63847457314592605726578185)
  ·
    refine ⟨47885592985944454294933639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63847457314592605726578185 47885592985944454294933639)
    ·
      refine ⟨71828389478916681442400459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47885592985944454294933639 71828389478916681442400459)
      ·
        refine ⟨107742584218375022163600689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71828389478916681442400459 107742584218375022163600689)
        ·
          refine ⟨80806938163781266622700517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107742584218375022163600689 80806938163781266622700517)
          ·
            refine ⟨15151300905708987491756347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80806938163781266622700517 15151300905708987491756347)
            ·
              refine ⟨22726951358563481237634521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15151300905708987491756347 22726951358563481237634521)
              ·
                refine ⟨17045213518922610928225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22726951358563481237634521 17045213518922610928225891)
                ·
                  refine ⟨25567820278383916392338837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17045213518922610928225891 25567820278383916392338837)
                  ·
                    refine ⟨1198491575549246080890883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25567820278383916392338837 1198491575549246080890883)
                    ·
                      rfl

theorem cell23_7002162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_7002162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002162 prefixEnd_7002162 := by exact prefixLift 7002162
  have htrace : WordTrace (prefixWord ++ tailWord_7002162) baseStart_7002162 baseEnd_7002162 := by
    simpa [prefixWord, tailWord_7002162, baseEnd_7002162] using wordTrace_append hprefix tailTrace_7002162
  have hstable : (prefixWord ++ tailWord_7002162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002162).length < 2 ^ (prefixWord ++ tailWord_7002162).sum := by decide
  have hdescent : baseEnd_7002162 < baseStart_7002162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002166 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_7002166 : Nat := 118140960795 + 7002166 * 2 ^ 59
def prefixEnd_7002166 : Nat := 4983230072969 + 3 ^ 40 * 7002166 * 2
def baseEnd_7002166 : Nat := 1198492260190118742340877

theorem tailTrace_7002166 : CollatzResearch.WordTrace tailWord_7002166 prefixEnd_7002166 1198492260190118742340877 := by
  unfold tailWord_7002166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15961873446897245724341147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170259983433570621059638901 15961873446897245724341147)
  ·
    refine ⟨23942810170345868586511721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15961873446897245724341147 23942810170345868586511721)
    ·
      refine ⟨17957107627759401439883791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23942810170345868586511721 17957107627759401439883791)
      ·
        refine ⟨26935661441639102159825687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17957107627759401439883791 26935661441639102159825687)
        ·
          refine ⟨40403492162458653239738531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26935661441639102159825687 40403492162458653239738531)
          ·
            refine ⟨60605238243687979859607797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40403492162458653239738531 60605238243687979859607797)
            ·
              refine ⟨5681741085345748111838231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60605238243687979859607797 5681741085345748111838231)
              ·
                refine ⟨8522611628018622167757347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681741085345748111838231 8522611628018622167757347)
                ·
                  refine ⟨12783917442027933251636021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8522611628018622167757347 12783917442027933251636021)
                  ·
                    refine ⟨1198492260190118742340877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12783917442027933251636021 1198492260190118742340877)
                    ·
                      rfl

theorem cell23_7002166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_7002166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002166 prefixEnd_7002166 := by exact prefixLift 7002166
  have htrace : WordTrace (prefixWord ++ tailWord_7002166) baseStart_7002166 baseEnd_7002166 := by
    simpa [prefixWord, tailWord_7002166, baseEnd_7002166] using wordTrace_append hprefix tailTrace_7002166
  have hstable : (prefixWord ++ tailWord_7002166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002166).length < 2 ^ (prefixWord ++ tailWord_7002166).sum := by decide
  have hdescent : baseEnd_7002166 < baseStart_7002166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002189 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7002189 : Nat := 118140960795 + 7002189 * 2 ^ 59
def prefixEnd_7002189 : Nat := 4983230072969 + 3 ^ 40 * 7002189 * 2
def baseEnd_7002189 : Nat := 3595488590625409637035025

theorem tailTrace_7002189 : CollatzResearch.WordTrace tailWord_7002189 prefixEnd_7002189 3595488590625409637035025 := by
  unfold tailWord_7002189
  simp only [CollatzResearch.WordTrace]
  refine ⟨255390814029272606517545621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170260542686181737678363747 255390814029272606517545621)
  ·
    refine ⟨11971444407622153430509951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255390814029272606517545621 11971444407622153430509951)
    ·
      refine ⟨17957166611433230145764927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11971444407622153430509951 17957166611433230145764927)
      ·
        refine ⟨26935749917149845218647391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17957166611433230145764927 26935749917149845218647391)
        ·
          refine ⟨40403624875724767827971087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26935749917149845218647391 40403624875724767827971087)
          ·
            refine ⟨60605437313587151741956631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40403624875724767827971087 60605437313587151741956631)
            ·
              refine ⟨90908155970380727612934947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60605437313587151741956631 90908155970380727612934947)
              ·
                refine ⟨136362233955571091419402421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90908155970380727612934947 136362233955571091419402421)
                ·
                  refine ⟨12783959433334789820568977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136362233955571091419402421 12783959433334789820568977)
                  ·
                    refine ⟨9587969575001092365426733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12783959433334789820568977 9587969575001092365426733)
                    ·
                      refine ⟨3595488590625409637035025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9587969575001092365426733 3595488590625409637035025)
                      ·
                        rfl

theorem cell23_7002189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7002189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002189 prefixEnd_7002189 := by exact prefixLift 7002189
  have htrace : WordTrace (prefixWord ++ tailWord_7002189) baseStart_7002189 baseEnd_7002189 := by
    simpa [prefixWord, tailWord_7002189, baseEnd_7002189] using wordTrace_append hprefix tailTrace_7002189
  have hstable : (prefixWord ++ tailWord_7002189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002189).length < 2 ^ (prefixWord ++ tailWord_7002189).sum := by decide
  have hdescent : baseEnd_7002189 < baseStart_7002189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002236 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_7002236 : Nat := 118140960795 + 7002236 * 2 ^ 59
def prefixEnd_7002236 : Nat := 4983230072969 + 3 ^ 40 * 7002236 * 2
def baseEnd_7002236 : Nat := 3595512724216170953147309

theorem tailTrace_7002236 : CollatzResearch.WordTrace tailWord_7002236 prefixEnd_7002236 3595512724216170953147309 := by
  unfold tailWord_7002236
  simp only [CollatzResearch.WordTrace]
  refine ⟨127696264130051166772253281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170261685506734889029671041 127696264130051166772253281)
  ·
    refine ⟨95772198097538375079189961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127696264130051166772253281 95772198097538375079189961)
    ·
      refine ⟨71829148573153781309392471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95772198097538375079189961 71829148573153781309392471)
      ·
        refine ⟨107743722859730671964088707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71829148573153781309392471 107743722859730671964088707)
        ·
          refine ⟨161615584289596007946133061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107743722859730671964088707 161615584289596007946133061)
          ·
            refine ⟨30302922054299251489899949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161615584289596007946133061 30302922054299251489899949)
            ·
              refine ⟨11363595770362219308712481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30302922054299251489899949 11363595770362219308712481)
              ·
                refine ⟨8522696827771664481534361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11363595770362219308712481 8522696827771664481534361)
                ·
                  refine ⟨6392022620828748361150771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522696827771664481534361 6392022620828748361150771)
                  ·
                    refine ⟨9588033931243122541726157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6392022620828748361150771 9588033931243122541726157)
                    ·
                      refine ⟨3595512724216170953147309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588033931243122541726157 3595512724216170953147309)
                      ·
                        rfl

theorem cell23_7002236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_7002236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002236 prefixEnd_7002236 := by exact prefixLift 7002236
  have htrace : WordTrace (prefixWord ++ tailWord_7002236) baseStart_7002236 baseEnd_7002236 := by
    simpa [prefixWord, tailWord_7002236, baseEnd_7002236] using wordTrace_append hprefix tailTrace_7002236
  have hstable : (prefixWord ++ tailWord_7002236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002236).length < 2 ^ (prefixWord ++ tailWord_7002236).sum := by decide
  have hdescent : baseEnd_7002236 < baseStart_7002236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002263 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 1, 3, 2]
def baseStart_7002263 : Nat := 118140960795 + 7002263 * 2 ^ 59
def prefixEnd_7002263 : Nat := 4983230072969 + 3 ^ 40 * 7002263 * 2
def baseEnd_7002263 : Nat := 3595526588193842347509685

theorem tailTrace_7002263 : CollatzResearch.WordTrace tailWord_7002263 prefixEnd_7002263 3595526588193842347509685 := by
  unfold tailWord_7002263
  simp only [CollatzResearch.WordTrace]
  refine ⟨255393513031004517155739443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170262342020669678103826295 255393513031004517155739443)
  ·
    refine ⟨383090269546506775733609165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255393513031004517155739443 383090269546506775733609165)
    ·
      refine ⟨143658851079940040900103437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383090269546506775733609165 143658851079940040900103437)
      ·
        refine ⟨53872069154977515337538789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143658851079940040900103437 53872069154977515337538789)
        ·
          refine ⟨10101012966558284125788523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53872069154977515337538789 10101012966558284125788523)
          ·
            refine ⟨15151519449837426188682785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101012966558284125788523 15151519449837426188682785)
            ·
              refine ⟨11363639587378069641512089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15151519449837426188682785 11363639587378069641512089)
              ·
                refine ⟨8522729690533552231134067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11363639587378069641512089 8522729690533552231134067)
                ·
                  refine ⟨12784094535800328346701101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8522729690533552231134067 12784094535800328346701101)
                  ·
                    refine ⟨4794035450925123130012913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12784094535800328346701101 4794035450925123130012913)
                    ·
                      refine ⟨3595526588193842347509685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794035450925123130012913 3595526588193842347509685)
                      ·
                        rfl

theorem cell23_7002263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_7002263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002263 prefixEnd_7002263 := by exact prefixLift 7002263
  have htrace : WordTrace (prefixWord ++ tailWord_7002263) baseStart_7002263 baseEnd_7002263 := by
    simpa [prefixWord, tailWord_7002263, baseEnd_7002263] using wordTrace_append hprefix tailTrace_7002263
  have hstable : (prefixWord ++ tailWord_7002263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002263).length < 2 ^ (prefixWord ++ tailWord_7002263).sum := by decide
  have hdescent : baseEnd_7002263 < baseStart_7002263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002312 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_7002312 : Nat := 118140960795 + 7002312 * 2 ^ 59
def prefixEnd_7002312 : Nat := 4983230072969 + 3 ^ 40 * 7002312 * 2
def baseEnd_7002312 : Nat := 1198517249581970885265653

theorem tailTrace_7002312 : CollatzResearch.WordTrace tailWord_7002312 prefixEnd_7002312 1198517249581970885265653 := by
  unfold tailWord_7002312
  simp only [CollatzResearch.WordTrace]
  refine ⟨127697650103913499262136595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170263533471884665682848793 127697650103913499262136595)
  ·
    refine ⟨191546475155870248893204893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127697650103913499262136595 191546475155870248893204893)
    ·
      refine ⟨71829928183451343334951835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191546475155870248893204893 71829928183451343334951835)
      ·
        refine ⟨107744892275177015002427753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71829928183451343334951835 107744892275177015002427753)
        ·
          refine ⟨80808669206382761251820815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107744892275177015002427753 80808669206382761251820815)
          ·
            refine ⟨121213003809574141877731223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80808669206382761251820815 121213003809574141877731223)
            ·
              refine ⟨181819505714361212816596835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121213003809574141877731223 181819505714361212816596835)
              ·
                refine ⟨272729258571541819224895253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181819505714361212816596835 272729258571541819224895253)
                ·
                  refine ⟨12784183995541022776166965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 272729258571541819224895253 12784183995541022776166965)
                  ·
                    refine ⟨1198517249581970885265653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12784183995541022776166965 1198517249581970885265653)
                    ·
                      rfl

theorem cell23_7002312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_7002312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002312 prefixEnd_7002312 := by exact prefixLift 7002312
  have htrace : WordTrace (prefixWord ++ tailWord_7002312) baseStart_7002312 baseEnd_7002312 := by
    simpa [prefixWord, tailWord_7002312, baseEnd_7002312] using wordTrace_append hprefix tailTrace_7002312
  have hstable : (prefixWord ++ tailWord_7002312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002312).length < 2 ^ (prefixWord ++ tailWord_7002312).sum := by decide
  have hdescent : baseEnd_7002312 < baseStart_7002312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002369 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_7002369 : Nat := 118140960795 + 7002369 * 2 ^ 59
def prefixEnd_7002369 : Nat := 4983230072969 + 3 ^ 40 * 7002369 * 2
def baseEnd_7002369 : Nat := 3595581017143218932784197

theorem tailTrace_7002369 : CollatzResearch.WordTrace tailWord_7002369 prefixEnd_7002369 3595581017143218932784197 := by
  unfold tailWord_7002369
  simp only [CollatzResearch.WordTrace]
  refine ⟨255397379168620497259098161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170264919445746998172732107 255397379168620497259098161)
  ·
    refine ⟨191548034376465372944323621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255397379168620497259098161 191548034376465372944323621)
    ·
      refine ⟨35915256445587257427060679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191548034376465372944323621 35915256445587257427060679)
      ·
        refine ⟨53872884668380886140591019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35915256445587257427060679 53872884668380886140591019)
        ·
          refine ⟨80809327002571329210886529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53872884668380886140591019 80809327002571329210886529)
          ·
            refine ⟨60606995251928496908164897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80809327002571329210886529 60606995251928496908164897)
            ·
              refine ⟨45455246438946372681123673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60606995251928496908164897 45455246438946372681123673)
              ·
                refine ⟨34091434829209779510842755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45455246438946372681123673 34091434829209779510842755)
                ·
                  refine ⟨51137152243814669266264133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34091434829209779510842755 51137152243814669266264133)
                  ·
                    refine ⟨9588216045715250487424525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51137152243814669266264133 9588216045715250487424525)
                    ·
                      refine ⟨3595581017143218932784197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588216045715250487424525 3595581017143218932784197)
                      ·
                        rfl

theorem cell23_7002369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_7002369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002369 prefixEnd_7002369 := by exact prefixLift 7002369
  have htrace : WordTrace (prefixWord ++ tailWord_7002369) baseStart_7002369 baseEnd_7002369 := by
    simpa [prefixWord, tailWord_7002369, baseEnd_7002369] using wordTrace_append hprefix tailTrace_7002369
  have hstable : (prefixWord ++ tailWord_7002369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002369).length < 2 ^ (prefixWord ++ tailWord_7002369).sum := by decide
  have hdescent : baseEnd_7002369 < baseStart_7002369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002376 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 3, 4]
def baseStart_7002376 : Nat := 118140960795 + 7002376 * 2 ^ 59
def prefixEnd_7002376 : Nat := 4983230072969 + 3 ^ 40 * 7002376 * 2
def baseEnd_7002376 : Nat := 1198528203835933468465555

theorem tailTrace_7002376 : CollatzResearch.WordTrace tailWord_7002376 prefixEnd_7002376 1198528203835933468465555 := by
  unfold tailWord_7002376
  simp only [CollatzResearch.WordTrace]
  refine ⟨127698817239797568727301491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170265089653063424969735321 127698817239797568727301491)
  ·
    refine ⟨191548225859696353090952237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127698817239797568727301491 191548225859696353090952237)
    ·
      refine ⟨71830584697386132409107089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191548225859696353090952237 71830584697386132409107089)
      ·
        refine ⟨53872938523039599306830317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71830584697386132409107089 53872938523039599306830317)
        ·
          refine ⟨20202351946139849740061369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53872938523039599306830317 20202351946139849740061369)
          ·
            refine ⟨15151763959604887305046027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20202351946139849740061369 15151763959604887305046027)
            ·
              refine ⟨22727645939407330957569041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15151763959604887305046027 22727645939407330957569041)
              ·
                refine ⟨17045734454555498218176781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22727645939407330957569041 17045734454555498218176781)
                ·
                  refine ⟨6392150420458311831816293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17045734454555498218176781 6392150420458311831816293)
                  ·
                    refine ⟨1198528203835933468465555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392150420458311831816293 1198528203835933468465555)
                    ·
                      rfl

theorem cell23_7002376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_7002376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002376 prefixEnd_7002376 := by exact prefixLift 7002376
  have htrace : WordTrace (prefixWord ++ tailWord_7002376) baseStart_7002376 baseEnd_7002376 := by
    simpa [prefixWord, tailWord_7002376, baseEnd_7002376] using wordTrace_append hprefix tailTrace_7002376
  have hstable : (prefixWord ++ tailWord_7002376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002376).length < 2 ^ (prefixWord ++ tailWord_7002376).sum := by decide
  have hdescent : baseEnd_7002376 < baseStart_7002376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002426 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2]
def baseStart_7002426 : Nat := 118140960795 + 7002426 * 2 ^ 59
def prefixEnd_7002426 : Nat := 4983230072969 + 3 ^ 40 * 7002426 * 2
def baseEnd_7002426 : Nat := 3595610285540525209771435

theorem tailTrace_7002426 : CollatzResearch.WordTrace tailWord_7002426 prefixEnd_7002426 3595610285540525209771435 := by
  unfold tailWord_7002426
  simp only [CollatzResearch.WordTrace]
  refine ⟨63849864532353498998480783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170266305419609330662615421 63849864532353498998480783)
  ·
    refine ⟨95774796798530248497721175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63849864532353498998480783 95774796798530248497721175)
    ·
      refine ⟨143662195197795372746581763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95774796798530248497721175 143662195197795372746581763)
      ·
        refine ⟨215493292796693059119872645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143662195197795372746581763 215493292796693059119872645)
        ·
          refine ⟨40404992399379948584976121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215493292796693059119872645 40404992399379948584976121)
          ·
            refine ⟨30303744299534961438732091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40404992399379948584976121 30303744299534961438732091)
            ·
              refine ⟨45455616449302442158098137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30303744299534961438732091 45455616449302442158098137)
              ·
                refine ⟨34091712336976831618573603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45455616449302442158098137 34091712336976831618573603)
                ·
                  refine ⟨51137568505465247427860405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34091712336976831618573603 51137568505465247427860405)
                  ·
                    refine ⟨4794147047387366946361913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51137568505465247427860405 4794147047387366946361913)
                    ·
                      refine ⟨3595610285540525209771435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794147047387366946361913 3595610285540525209771435)
                      ·
                        rfl

theorem cell23_7002426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_7002426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002426 prefixEnd_7002426 := by exact prefixLift 7002426
  have htrace : WordTrace (prefixWord ++ tailWord_7002426) baseStart_7002426 baseEnd_7002426 := by
    simpa [prefixWord, tailWord_7002426, baseEnd_7002426] using wordTrace_append hprefix tailTrace_7002426
  have hstable : (prefixWord ++ tailWord_7002426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002426).length < 2 ^ (prefixWord ++ tailWord_7002426).sum := by decide
  have hdescent : baseEnd_7002426 < baseStart_7002426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002450 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_7002450 : Nat := 118140960795 + 7002450 * 2 ^ 59
def prefixEnd_7002450 : Nat := 4983230072969 + 3 ^ 40 * 7002450 * 2
def baseEnd_7002450 : Nat := 3595622609076233115871325

theorem tailTrace_7002450 : CollatzResearch.WordTrace tailWord_7002450 prefixEnd_7002450 3595622609076233115871325 := by
  unfold tailWord_7002450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63850083370331762023199201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170266888987551365395197869 63850083370331762023199201)
  ·
    refine ⟨47887562527748821517399401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63850083370331762023199201 47887562527748821517399401)
    ·
      refine ⟨35915671895811616138049551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47887562527748821517399401 35915671895811616138049551)
      ·
        refine ⟨53873507843717424207074327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35915671895811616138049551 53873507843717424207074327)
        ·
          refine ⟨80810261765576136310611491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53873507843717424207074327 80810261765576136310611491)
          ·
            refine ⟨121215392648364204465917237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80810261765576136310611491 121215392648364204465917237)
            ·
              refine ⟨11363943060784144168679741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121215392648364204465917237 11363943060784144168679741)
              ·
                refine ⟨4261478647794054063254903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11363943060784144168679741 4261478647794054063254903)
                ·
                  refine ⟨6392217971691081094882355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261478647794054063254903 6392217971691081094882355)
                  ·
                    refine ⟨9588326957536621642323533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6392217971691081094882355 9588326957536621642323533)
                    ·
                      refine ⟨3595622609076233115871325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588326957536621642323533 3595622609076233115871325)
                      ·
                        rfl

theorem cell23_7002450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_7002450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002450 prefixEnd_7002450 := by exact prefixLift 7002450
  have htrace : WordTrace (prefixWord ++ tailWord_7002450) baseStart_7002450 baseEnd_7002450 := by
    simpa [prefixWord, tailWord_7002450, baseEnd_7002450] using wordTrace_append hprefix tailTrace_7002450
  have hstable : (prefixWord ++ tailWord_7002450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002450).length < 2 ^ (prefixWord ++ tailWord_7002450).sum := by decide
  have hdescent : baseEnd_7002450 < baseStart_7002450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002469 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7002469 : Nat := 118140960795 + 7002469 * 2 ^ 59
def prefixEnd_7002469 : Nat := 4983230072969 + 3 ^ 40 * 7002469 * 2
def baseEnd_7002469 : Nat := 3595632365208668541533737

theorem tailTrace_7002469 : CollatzResearch.WordTrace tailWord_7002469 prefixEnd_7002469 3595632365208668541533737 := by
  unfold tailWord_7002469
  simp only [CollatzResearch.WordTrace]
  refine ⟨255401026468258214337738461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170267350978838809558492307 255401026468258214337738461)
  ·
    refine ⟨95775384925596830376651923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255401026468258214337738461 95775384925596830376651923)
    ·
      refine ⟨143663077388395245564977885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95775384925596830376651923 143663077388395245564977885)
      ·
        refine ⟨53873654020648217086866707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143663077388395245564977885 53873654020648217086866707)
        ·
          refine ⟨80810481030972325630300061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53873654020648217086866707 80810481030972325630300061)
          ·
            refine ⟨30303930386614622111362523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80810481030972325630300061 30303930386614622111362523)
            ·
              refine ⟨45455895579921933167043785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30303930386614622111362523 45455895579921933167043785)
              ·
                refine ⟨34091921684941449875282839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45455895579921933167043785 34091921684941449875282839)
                ·
                  refine ⟨51137882527412174812924259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34091921684941449875282839 51137882527412174812924259)
                  ·
                    refine ⟨76706823791118262219386389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51137882527412174812924259 76706823791118262219386389)
                    ·
                      refine ⟨3595632365208668541533737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76706823791118262219386389 3595632365208668541533737)
                      ·
                        rfl

theorem cell23_7002469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7002469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002469 prefixEnd_7002469 := by exact prefixLift 7002469
  have htrace : WordTrace (prefixWord ++ tailWord_7002469) baseStart_7002469 baseEnd_7002469 := by
    simpa [prefixWord, tailWord_7002469, baseEnd_7002469] using wordTrace_append hprefix tailTrace_7002469
  have hstable : (prefixWord ++ tailWord_7002469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002469).length < 2 ^ (prefixWord ++ tailWord_7002469).sum := by decide
  have hdescent : baseEnd_7002469 < baseStart_7002469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002493 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_7002493 : Nat := 118140960795 + 7002493 * 2 ^ 59
def prefixEnd_7002493 : Nat := 4983230072969 + 3 ^ 40 * 7002493 * 2
def baseEnd_7002493 : Nat := 3595644688744376447633627

theorem tailTrace_7002493 : CollatzResearch.WordTrace tailWord_7002493 prefixEnd_7002493 3595644688744376447633627 := by
  unfold tailWord_7002493
  simp only [CollatzResearch.WordTrace]
  refine ⟨255401901820171266436612133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170267934546780844291074755 255401901820171266436612133)
  ·
    refine ⟨47887856591282112456864775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255401901820171266436612133 47887856591282112456864775)
    ·
      refine ⟨71831784886923168685297163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47887856591282112456864775 71831784886923168685297163)
      ·
        refine ⟨107747677330384753027945745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71831784886923168685297163 107747677330384753027945745)
        ·
          refine ⟨80810757997788564770959309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107747677330384753027945745 80810757997788564770959309)
          ·
            refine ⟨30304034249170711789109741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80810757997788564770959309 30304034249170711789109741)
            ·
              refine ⟨11364012843439016920916153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30304034249170711789109741 11364012843439016920916153)
              ·
                refine ⟨8523009632579262690687115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364012843439016920916153 8523009632579262690687115)
                ·
                  refine ⟨12784514448868894036030673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523009632579262690687115 12784514448868894036030673)
                  ·
                    refine ⟨9588385836651670527023005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12784514448868894036030673 9588385836651670527023005)
                    ·
                      refine ⟨3595644688744376447633627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588385836651670527023005 3595644688744376447633627)
                      ·
                        rfl

theorem cell23_7002493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_7002493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002493 prefixEnd_7002493 := by exact prefixLift 7002493
  have htrace : WordTrace (prefixWord ++ tailWord_7002493) baseStart_7002493 baseEnd_7002493 := by
    simpa [prefixWord, tailWord_7002493, baseEnd_7002493] using wordTrace_append hprefix tailTrace_7002493
  have hstable : (prefixWord ++ tailWord_7002493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002493).length < 2 ^ (prefixWord ++ tailWord_7002493).sum := by decide
  have hdescent : baseEnd_7002493 < baseStart_7002493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002519 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_7002519 : Nat := 118140960795 + 7002519 * 2 ^ 59
def prefixEnd_7002519 : Nat := 4983230072969 + 3 ^ 40 * 7002519 * 2
def baseEnd_7002519 : Nat := 3595658039241393345908507

theorem tailTrace_7002519 : CollatzResearch.WordTrace tailWord_7002519 prefixEnd_7002519 3595658039241393345908507 := by
  unfold tailWord_7002519
  simp only [CollatzResearch.WordTrace]
  refine ⟨255402850118077072877058611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170268566745384715251372407 255402850118077072877058611)
  ·
    refine ⟨383104275177115609315587917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255402850118077072877058611 383104275177115609315587917)
    ·
      refine ⟨143664103191418353493345469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383104275177115609315587917 143664103191418353493345469)
      ·
        refine ⟨53874038696781882560004551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143664103191418353493345469 53874038696781882560004551)
        ·
          refine ⟨80811058045172823840006827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53874038696781882560004551 80811058045172823840006827)
          ·
            refine ⟨121216587067759235760010241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80811058045172823840006827 121216587067759235760010241)
            ·
              refine ⟨90912440300819426820007681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121216587067759235760010241 90912440300819426820007681)
              ·
                refine ⟨68184330225614570115005761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90912440300819426820007681 68184330225614570115005761)
                ·
                  refine ⟨51138247669210927586254321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68184330225614570115005761 51138247669210927586254321)
                  ·
                    refine ⟨38353685751908195689690741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51138247669210927586254321 38353685751908195689690741)
                    ·
                      refine ⟨3595658039241393345908507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38353685751908195689690741 3595658039241393345908507)
                      ·
                        rfl

theorem cell23_7002519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_7002519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002519 prefixEnd_7002519 := by exact prefixLift 7002519
  have htrace : WordTrace (prefixWord ++ tailWord_7002519) baseStart_7002519 baseEnd_7002519 := by
    simpa [prefixWord, tailWord_7002519, baseEnd_7002519] using wordTrace_append hprefix tailTrace_7002519
  have hstable : (prefixWord ++ tailWord_7002519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002519).length < 2 ^ (prefixWord ++ tailWord_7002519).sum := by decide
  have hdescent : baseEnd_7002519 < baseStart_7002519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002561 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7002561 : Nat := 118140960795 + 7002561 * 2 ^ 59
def prefixEnd_7002561 : Nat := 4983230072969 + 3 ^ 40 * 7002561 * 2
def baseEnd_7002561 : Nat := 3595679605428882181583315

theorem tailTrace_7002561 : CollatzResearch.WordTrace tailWord_7002561 prefixEnd_7002561 3595679605428882181583315 := by
  unfold tailWord_7002561
  simp only [CollatzResearch.WordTrace]
  refine ⟨255404381983924914050087537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170269587989283276033391691 255404381983924914050087537)
  ·
    refine ⟨191553286487943685537565653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255404381983924914050087537 191553286487943685537565653)
    ·
      refine ⟨4489530152061180129786695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 191553286487943685537565653 4489530152061180129786695)
      ·
        refine ⟨6734295228091770194680043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489530152061180129786695 6734295228091770194680043)
        ·
          refine ⟨10101442842137655292020065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734295228091770194680043 10101442842137655292020065)
          ·
            refine ⟨7576082131603241469015049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10101442842137655292020065 7576082131603241469015049)
            ·
              refine ⟨5682061598702431101761287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576082131603241469015049 5682061598702431101761287)
              ·
                refine ⟨8523092398053646652641931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682061598702431101761287 8523092398053646652641931)
                ·
                  refine ⟨12784638597080469978962897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523092398053646652641931 12784638597080469978962897)
                  ·
                    refine ⟨9588478947810352484222173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12784638597080469978962897 9588478947810352484222173)
                    ·
                      refine ⟨3595679605428882181583315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588478947810352484222173 3595679605428882181583315)
                      ·
                        rfl

theorem cell23_7002561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7002561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002561 prefixEnd_7002561 := by exact prefixLift 7002561
  have htrace : WordTrace (prefixWord ++ tailWord_7002561) baseStart_7002561 baseEnd_7002561 := by
    simpa [prefixWord, tailWord_7002561, baseEnd_7002561] using wordTrace_append hprefix tailTrace_7002561
  have hstable : (prefixWord ++ tailWord_7002561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002561).length < 2 ^ (prefixWord ++ tailWord_7002561).sum := by decide
  have hdescent : baseEnd_7002561 < baseStart_7002561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002563 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 4, 2, 2]
def baseStart_7002563 : Nat := 118140960795 + 7002563 * 2 ^ 59
def prefixEnd_7002563 : Nat := 4983230072969 + 3 ^ 40 * 7002563 * 2
def baseEnd_7002563 : Nat := 3595680632390191173758305

theorem tailTrace_7002563 : CollatzResearch.WordTrace tailWord_7002563 prefixEnd_7002563 3595680632390191173758305 := by
  unfold tailWord_7002563
  simp only [CollatzResearch.WordTrace]
  refine ⟨255404454929917668391660343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170269636619945112261106895 255404454929917668391660343)
  ·
    refine ⟨383106682394876502587490515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255404454929917668391660343 383106682394876502587490515)
    ·
      refine ⟨574660023592314753881235773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383106682394876502587490515 574660023592314753881235773)
      ·
        refine ⟨215497508847118032705463415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574660023592314753881235773 215497508847118032705463415)
        ·
          refine ⟨323246263270677049058195123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215497508847118032705463415 323246263270677049058195123)
          ·
            refine ⟨484869394906015573587292685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323246263270677049058195123 484869394906015573587292685)
            ·
              refine ⟨181826023089755840095234757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484869394906015573587292685 181826023089755840095234757)
              ·
                refine ⟨34092379329329220017856517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181826023089755840095234757 34092379329329220017856517)
                ·
                  refine ⟨6392321124249228753348097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34092379329329220017856517 6392321124249228753348097)
                  ·
                    refine ⟨4794240843186921565011073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6392321124249228753348097 4794240843186921565011073)
                    ·
                      refine ⟨3595680632390191173758305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794240843186921565011073 3595680632390191173758305)
                      ·
                        rfl

theorem cell23_7002563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_7002563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002563 prefixEnd_7002563 := by exact prefixLift 7002563
  have htrace : WordTrace (prefixWord ++ tailWord_7002563) baseStart_7002563 baseEnd_7002563 := by
    simpa [prefixWord, tailWord_7002563, baseEnd_7002563] using wordTrace_append hprefix tailTrace_7002563
  have hstable : (prefixWord ++ tailWord_7002563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002563).length < 2 ^ (prefixWord ++ tailWord_7002563).sum := by decide
  have hdescent : baseEnd_7002563 < baseStart_7002563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002567 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_7002567 : Nat := 118140960795 + 7002567 * 2 ^ 59
def prefixEnd_7002567 : Nat := 4983230072969 + 3 ^ 40 * 7002567 * 2
def baseEnd_7002567 : Nat := 3595682686312809158108287

theorem tailTrace_7002567 : CollatzResearch.WordTrace tailWord_7002567 prefixEnd_7002567 3595682686312809158108287 := by
  unfold tailWord_7002567
  simp only [CollatzResearch.WordTrace]
  refine ⟨255404600821903177074805955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170269733881268784716537303 255404600821903177074805955)
  ·
    refine ⟨383106901232854765612208933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255404600821903177074805955 383106901232854765612208933)
    ·
      refine ⟨71832543981160268552289175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383106901232854765612208933 71832543981160268552289175)
      ·
        refine ⟨107748815971740402828433763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71832543981160268552289175 107748815971740402828433763)
        ·
          refine ⟨161623223957610604242650645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107748815971740402828433763 161623223957610604242650645)
          ·
            refine ⟨7576088623012997073874249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161623223957610604242650645 7576088623012997073874249)
            ·
              refine ⟨5682066467259747805405687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576088623012997073874249 5682066467259747805405687)
              ·
                refine ⟨8523099700889621708108531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682066467259747805405687 8523099700889621708108531)
                ·
                  refine ⟨12784649551334432562162797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523099700889621708108531 12784649551334432562162797)
                  ·
                    refine ⟨4794243581750412210811049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12784649551334432562162797 4794243581750412210811049)
                    ·
                      refine ⟨3595682686312809158108287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794243581750412210811049 3595682686312809158108287)
                      ·
                        rfl

theorem cell23_7002567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_7002567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002567 prefixEnd_7002567 := by exact prefixLift 7002567
  have htrace : WordTrace (prefixWord ++ tailWord_7002567) baseStart_7002567 baseEnd_7002567 := by
    simpa [prefixWord, tailWord_7002567, baseEnd_7002567] using wordTrace_append hprefix tailTrace_7002567
  have hstable : (prefixWord ++ tailWord_7002567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002567).length < 2 ^ (prefixWord ++ tailWord_7002567).sum := by decide
  have hdescent : baseEnd_7002567 < baseStart_7002567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002586 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_7002586 : Nat := 118140960795 + 7002586 * 2 ^ 59
def prefixEnd_7002586 : Nat := 4983230072969 + 3 ^ 40 * 7002586 * 2
def baseEnd_7002586 : Nat := 399521382493916064863411

theorem tailTrace_7002586 : CollatzResearch.WordTrace tailWord_7002586 prefixEnd_7002586 399521382493916064863411 := by
  unfold tailWord_7002586
  simp only [CollatzResearch.WordTrace]
  refine ⟨63851323452208585829936903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170270195872556228879831741 63851323452208585829936903)
  ·
    refine ⟨95776985178312878744905355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63851323452208585829936903 95776985178312878744905355)
    ·
      refine ⟨143665477767469318117358033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95776985178312878744905355 143665477767469318117358033)
      ·
        refine ⟨107749108325601988588018525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143665477767469318117358033 107749108325601988588018525)
        ·
          refine ⟨40405915622100745720506947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107749108325601988588018525 40405915622100745720506947)
          ·
            refine ⟨60608873433151118580760421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40405915622100745720506947 60608873433151118580760421)
            ·
              refine ⟨11364163768715834733892579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60608873433151118580760421 11364163768715834733892579)
              ·
                refine ⟨17046245653073752100838869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11364163768715834733892579 17046245653073752100838869)
                ·
                  refine ⟨399521382493916064863411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17046245653073752100838869 399521382493916064863411)
                  ·
                    rfl

theorem cell23_7002586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_7002586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002586 prefixEnd_7002586 := by exact prefixLift 7002586
  have htrace : WordTrace (prefixWord ++ tailWord_7002586) baseStart_7002586 baseEnd_7002586 := by
    simpa [prefixWord, tailWord_7002586, baseEnd_7002586] using wordTrace_append hprefix tailTrace_7002586
  have hstable : (prefixWord ++ tailWord_7002586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002586).length < 2 ^ (prefixWord ++ tailWord_7002586).sum := by decide
  have hdescent : baseEnd_7002586 < baseStart_7002586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002597 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7002597 : Nat := 118140960795 + 7002597 * 2 ^ 59
def prefixEnd_7002597 : Nat := 4983230072969 + 3 ^ 40 * 7002597 * 2
def baseEnd_7002597 : Nat := 3595698090732444040733149

theorem tailTrace_7002597 : CollatzResearch.WordTrace tailWord_7002597 prefixEnd_7002597 3595698090732444040733149 := by
  unfold tailWord_7002597
  simp only [CollatzResearch.WordTrace]
  refine ⟨255405695011794492198398045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170270463341196328132265363 255405695011794492198398045)
  ·
    refine ⟨95777135629422934574399267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255405695011794492198398045 95777135629422934574399267)
    ·
      refine ⟨143665703444134401861598901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95777135629422934574399267 143665703444134401861598901)
      ·
        refine ⟨13468659697887600174524897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143665703444134401861598901 13468659697887600174524897)
        ·
          refine ⟨10101494773415700130893673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13468659697887600174524897 10101494773415700130893673)
          ·
            refine ⟨7576121080061775098170255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10101494773415700130893673 7576121080061775098170255)
            ·
              refine ⟨11364181620092662647255383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576121080061775098170255 11364181620092662647255383)
              ·
                refine ⟨17046272430138993970883075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11364181620092662647255383 17046272430138993970883075)
                ·
                  refine ⟨25569408645208490956324613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17046272430138993970883075 25569408645208490956324613)
                  ·
                    refine ⟨4794264120976592054310865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25569408645208490956324613 4794264120976592054310865)
                    ·
                      refine ⟨3595698090732444040733149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794264120976592054310865 3595698090732444040733149)
                      ·
                        rfl

theorem cell23_7002597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7002597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002597 prefixEnd_7002597 := by exact prefixLift 7002597
  have htrace : WordTrace (prefixWord ++ tailWord_7002597) baseStart_7002597 baseEnd_7002597 := by
    simpa [prefixWord, tailWord_7002597, baseEnd_7002597] using wordTrace_append hprefix tailTrace_7002597
  have hstable : (prefixWord ++ tailWord_7002597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002597).length < 2 ^ (prefixWord ++ tailWord_7002597).sum := by decide
  have hdescent : baseEnd_7002597 < baseStart_7002597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002616 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_7002616 : Nat := 118140960795 + 7002616 * 2 ^ 59
def prefixEnd_7002616 : Nat := 4983230072969 + 3 ^ 40 * 7002616 * 2
def baseEnd_7002616 : Nat := 1198569282288293155465187

theorem tailTrace_7002616 : CollatzResearch.WordTrace tailWord_7002616 prefixEnd_7002616 1198569282288293155465187 := by
  unfold tailWord_7002616
  simp only [CollatzResearch.WordTrace]
  refine ⟨127703193999362829221669851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170270925332483772295559801 127703193999362829221669851)
  ·
    refine ⟨191554790999044243832504777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127703193999362829221669851 191554790999044243832504777)
    ·
      refine ⟨143666093249283182874378583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191554790999044243832504777 143666093249283182874378583)
      ·
        refine ⟨215499139873924774311567875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143666093249283182874378583 215499139873924774311567875)
        ·
          refine ⟨323248709810887161467351813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215499139873924774311567875 323248709810887161467351813)
          ·
            refine ⟨60609133089541342775128465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323248709810887161467351813 60609133089541342775128465)
            ·
              refine ⟨45456849817156007081346349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60609133089541342775128465 45456849817156007081346349)
              ·
                refine ⟨17046318681433502655504881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45456849817156007081346349 17046318681433502655504881)
                ·
                  refine ⟨12784739011075126991628661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17046318681433502655504881 12784739011075126991628661)
                  ·
                    refine ⟨1198569282288293155465187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12784739011075126991628661 1198569282288293155465187)
                    ·
                      rfl

theorem cell23_7002616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_7002616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002616 prefixEnd_7002616 := by exact prefixLift 7002616
  have htrace : WordTrace (prefixWord ++ tailWord_7002616) baseStart_7002616 baseEnd_7002616 := by
    simpa [prefixWord, tailWord_7002616, baseEnd_7002616] using wordTrace_append hprefix tailTrace_7002616
  have hstable : (prefixWord ++ tailWord_7002616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002616).length < 2 ^ (prefixWord ++ tailWord_7002616).sum := by decide
  have hdescent : baseEnd_7002616 < baseStart_7002616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002637 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7002637 : Nat := 118140960795 + 7002637 * 2 ^ 59
def prefixEnd_7002637 : Nat := 4983230072969 + 3 ^ 40 * 7002637 * 2
def baseEnd_7002637 : Nat := 399524292217624876025885

theorem tailTrace_7002637 : CollatzResearch.WordTrace tailWord_7002637 prefixEnd_7002637 399524292217624876025885 := by
  unfold tailWord_7002637
  simp only [CollatzResearch.WordTrace]
  refine ⟨255407153931649579029854165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170271435954433052686569443 255407153931649579029854165)
  ·
    refine ⟨5986105170273037008512207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 255407153931649579029854165 5986105170273037008512207)
    ·
      refine ⟨8979157755409555512768311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986105170273037008512207 8979157755409555512768311)
      ·
        refine ⟨13468736633114333269152467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8979157755409555512768311 13468736633114333269152467)
        ·
          refine ⟨20203104949671499903728701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13468736633114333269152467 20203104949671499903728701)
          ·
            refine ⟨7576164356126812463898263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20203104949671499903728701 7576164356126812463898263)
            ·
              refine ⟨11364246534190218695847395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576164356126812463898263 11364246534190218695847395)
              ·
                refine ⟨17046369801285328043771093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11364246534190218695847395 17046369801285328043771093)
                ·
                  refine ⟨399524292217624876025885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17046369801285328043771093 399524292217624876025885)
                  ·
                    rfl

theorem cell23_7002637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7002637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002637 prefixEnd_7002637 := by exact prefixLift 7002637
  have htrace : WordTrace (prefixWord ++ tailWord_7002637) baseStart_7002637 baseEnd_7002637 := by
    simpa [prefixWord, tailWord_7002637, baseEnd_7002637] using wordTrace_append hprefix tailTrace_7002637
  have hstable : (prefixWord ++ tailWord_7002637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002637).length < 2 ^ (prefixWord ++ tailWord_7002637).sum := by decide
  have hdescent : baseEnd_7002637 < baseStart_7002637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002673 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_7002673 : Nat := 118140960795 + 7002673 * 2 ^ 59
def prefixEnd_7002673 : Nat := 4983230072969 + 3 ^ 40 * 7002673 * 2
def baseEnd_7002673 : Nat := 3595737115262185743382799

theorem tailTrace_7002673 : CollatzResearch.WordTrace tailWord_7002673 prefixEnd_7002673 3595737115262185743382799 := by
  unfold tailWord_7002673
  simp only [CollatzResearch.WordTrace]
  refine ⟨255408466959519157178164673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170272311306346104785443115 255408466959519157178164673)
  ·
    refine ⟨191556350219639367883623505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255408466959519157178164673 191556350219639367883623505)
    ·
      refine ⟨143667262664729525912717629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191556350219639367883623505 143667262664729525912717629)
      ·
        refine ⟨53875223499273572217269111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143667262664729525912717629 53875223499273572217269111)
        ·
          refine ⟨80812835248910358325903667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53875223499273572217269111 80812835248910358325903667)
          ·
            refine ⟨121219252873365537488855501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80812835248910358325903667 121219252873365537488855501)
            ·
              refine ⟨45457219827512076558320813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121219252873365537488855501 45457219827512076558320813)
              ·
                refine ⟨17046457435317028709370305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45457219827512076558320813 17046457435317028709370305)
                ·
                  refine ⟨12784843076487771532027729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17046457435317028709370305 12784843076487771532027729)
                  ·
                    refine ⟨9588632307365828649020797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12784843076487771532027729 9588632307365828649020797)
                    ·
                      refine ⟨3595737115262185743382799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588632307365828649020797 3595737115262185743382799)
                      ·
                        rfl

theorem cell23_7002673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_7002673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002673 prefixEnd_7002673 := by exact prefixLift 7002673
  have htrace : WordTrace (prefixWord ++ tailWord_7002673) baseStart_7002673 baseEnd_7002673 := by
    simpa [prefixWord, tailWord_7002673, baseEnd_7002673] using wordTrace_append hprefix tailTrace_7002673
  have hstable : (prefixWord ++ tailWord_7002673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002673).length < 2 ^ (prefixWord ++ tailWord_7002673).sum := by decide
  have hdescent : baseEnd_7002673 < baseStart_7002673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002680 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 1, 4]
def baseStart_7002680 : Nat := 118140960795 + 7002680 * 2 ^ 59
def prefixEnd_7002680 : Nat := 4983230072969 + 3 ^ 40 * 7002680 * 2
def baseEnd_7002680 : Nat := 1198580236542255738665089

theorem tailTrace_7002680 : CollatzResearch.WordTrace tailWord_7002680 prefixEnd_7002680 1198580236542255738665089 := by
  unfold tailWord_7002680
  simp only [CollatzResearch.WordTrace]
  refine ⟨127704361135246898686834747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170272481513662531582446329 127704361135246898686834747)
  ·
    refine ⟨191556541702870348030252121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127704361135246898686834747 191556541702870348030252121)
    ·
      refine ⟨143667406277152761022689091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191556541702870348030252121 143667406277152761022689091)
      ·
        refine ⟨215501109415729141534033637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143667406277152761022689091 215501109415729141534033637)
        ·
          refine ⟨40406458015449214037631307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215501109415729141534033637 40406458015449214037631307)
          ·
            refine ⟨60609687023173821056446961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40406458015449214037631307 60609687023173821056446961)
            ·
              refine ⟨45457265267380365792335221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60609687023173821056446961 45457265267380365792335221)
              ·
                refine ⟨4261618618816909293031427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45457265267380365792335221 4261618618816909293031427)
                ·
                  refine ⟨6392427928225363939547141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261618618816909293031427 6392427928225363939547141)
                  ·
                    refine ⟨1198580236542255738665089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392427928225363939547141 1198580236542255738665089)
                    ·
                      rfl

theorem cell23_7002680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_7002680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002680 prefixEnd_7002680 := by exact prefixLift 7002680
  have htrace : WordTrace (prefixWord ++ tailWord_7002680) baseStart_7002680 baseEnd_7002680 := by
    simpa [prefixWord, tailWord_7002680, baseEnd_7002680] using wordTrace_append hprefix tailTrace_7002680
  have hstable : (prefixWord ++ tailWord_7002680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002680).length < 2 ^ (prefixWord ++ tailWord_7002680).sum := by decide
  have hdescent : baseEnd_7002680 < baseStart_7002680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002693 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 6]
def baseStart_7002693 : Nat := 118140960795 + 7002693 * 2 ^ 59
def prefixEnd_7002693 : Nat := 4983230072969 + 3 ^ 40 * 7002693 * 2
def baseEnd_7002693 : Nat := 399527487208363962792523

theorem tailTrace_7002693 : CollatzResearch.WordTrace tailWord_7002693 prefixEnd_7002693 399527487208363962792523 := by
  unfold tailWord_7002693
  simp only [CollatzResearch.WordTrace]
  refine ⟨255409196419446700593892733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170272797612964467062595155 255409196419446700593892733)
  ·
    refine ⟨95778448657292512722709775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255409196419446700593892733 95778448657292512722709775)
    ·
      refine ⟨143667672985938769084064663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95778448657292512722709775 143667672985938769084064663)
      ·
        refine ⟨215501509478908153626096995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143667672985938769084064663 215501509478908153626096995)
        ·
          refine ⟨323252264218362230439145493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215501509478908153626096995 323252264218362230439145493)
          ·
            refine ⟨15152449885235729551834945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 323252264218362230439145493 15152449885235729551834945)
            ·
              refine ⟨11364337413926797163876209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15152449885235729551834945 11364337413926797163876209)
              ·
                refine ⟨8523253060445097872907157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364337413926797163876209 8523253060445097872907157)
                ·
                  refine ⟨399527487208363962792523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8523253060445097872907157 399527487208363962792523)
                  ·
                    rfl

theorem cell23_7002693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_7002693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002693 prefixEnd_7002693 := by exact prefixLift 7002693
  have htrace : WordTrace (prefixWord ++ tailWord_7002693) baseStart_7002693 baseEnd_7002693 := by
    simpa [prefixWord, tailWord_7002693, baseEnd_7002693] using wordTrace_append hprefix tailTrace_7002693
  have hstable : (prefixWord ++ tailWord_7002693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002693).length < 2 ^ (prefixWord ++ tailWord_7002693).sum := by decide
  have hdescent : baseEnd_7002693 < baseStart_7002693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002723 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 1, 5]
def baseStart_7002723 : Nat := 118140960795 + 7002723 * 2 ^ 59
def prefixEnd_7002723 : Nat := 4983230072969 + 3 ^ 40 * 7002723 * 2
def baseEnd_7002723 : Nat := 1198587596431636849252523

theorem tailTrace_7002723 : CollatzResearch.WordTrace tailWord_7002723 prefixEnd_7002723 1198587596431636849252523 := by
  unfold tailWord_7002723
  simp only [CollatzResearch.WordTrace]
  refine ⟨255410290609338015717484823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170273527072892010478323215 255410290609338015717484823)
  ·
    refine ⟨383115435914007023576227235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255410290609338015717484823 383115435914007023576227235)
    ·
      refine ⟨574673153871010535364340853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383115435914007023576227235 574673153871010535364340853)
      ·
        refine ⟨53875608175407237690406955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 574673153871010535364340853 53875608175407237690406955)
        ·
          refine ⟨80813412263110856535610433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53875608175407237690406955 80813412263110856535610433)
          ·
            refine ⟨60610059197333142401707825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80813412263110856535610433 60610059197333142401707825)
            ·
              refine ⟨45457544397999856801280869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60610059197333142401707825 45457544397999856801280869)
              ·
                refine ⟨8523289574624973150240163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45457544397999856801280869 8523289574624973150240163)
                ·
                  refine ⟨12784934361937459725360245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523289574624973150240163 12784934361937459725360245)
                  ·
                    refine ⟨1198587596431636849252523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12784934361937459725360245 1198587596431636849252523)
                    ·
                      rfl

theorem cell23_7002723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 5].length) (baseStart_7002723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002723 prefixEnd_7002723 := by exact prefixLift 7002723
  have htrace : WordTrace (prefixWord ++ tailWord_7002723) baseStart_7002723 baseEnd_7002723 := by
    simpa [prefixWord, tailWord_7002723, baseEnd_7002723] using wordTrace_append hprefix tailTrace_7002723
  have hstable : (prefixWord ++ tailWord_7002723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002723).length < 2 ^ (prefixWord ++ tailWord_7002723).sum := by decide
  have hdescent : baseEnd_7002723 < baseStart_7002723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002730 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_7002730 : Nat := 118140960795 + 7002730 * 2 ^ 59
def prefixEnd_7002730 : Nat := 4983230072969 + 3 ^ 40 * 7002730 * 2
def baseEnd_7002730 : Nat := 3595766383659492020370037

theorem tailTrace_7002730 : CollatzResearch.WordTrace tailWord_7002730 prefixEnd_7002730 3595766383659492020370037 := by
  unfold tailWord_7002730
  simp only [CollatzResearch.WordTrace]
  refine ⟨63852636480078163978247411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170273697280208437275326429 63852636480078163978247411)
  ·
    refine ⟨95778954720117245967371117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63852636480078163978247411 95778954720117245967371117)
    ·
      refine ⟨35917108020043967237764169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95778954720117245967371117 35917108020043967237764169)
      ·
        refine ⟨26937831015032975428323127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35917108020043967237764169 26937831015032975428323127)
        ·
          refine ⟨40406746522549463142484691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26937831015032975428323127 40406746522549463142484691)
          ·
            refine ⟨60610119783824194713727037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40406746522549463142484691 60610119783824194713727037)
            ·
              refine ⟨22728794918934073017647639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60610119783824194713727037 22728794918934073017647639)
              ·
                refine ⟨34093192378401109526471459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22728794918934073017647639 34093192378401109526471459)
                ·
                  refine ⟨51139788567601664289707189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34093192378401109526471459 51139788567601664289707189)
                  ·
                    refine ⟨4794355178212656027160049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51139788567601664289707189 4794355178212656027160049)
                    ·
                      refine ⟨3595766383659492020370037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794355178212656027160049 3595766383659492020370037)
                      ·
                        rfl

theorem cell23_7002730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_7002730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002730 prefixEnd_7002730 := by exact prefixLift 7002730
  have htrace : WordTrace (prefixWord ++ tailWord_7002730) baseStart_7002730 baseEnd_7002730 := by
    simpa [prefixWord, tailWord_7002730, baseEnd_7002730] using wordTrace_append hprefix tailTrace_7002730
  have hstable : (prefixWord ++ tailWord_7002730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002730).length < 2 ^ (prefixWord ++ tailWord_7002730).sum := by decide
  have hdescent : baseEnd_7002730 < baseStart_7002730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002763 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 3]
def baseStart_7002763 : Nat := 118140960795 + 7002763 * 2 ^ 59
def prefixEnd_7002763 : Nat := 4983230072969 + 3 ^ 40 * 7002763 * 2
def baseEnd_7002763 : Nat := 3595783328521090391257385

theorem tailTrace_7002763 : CollatzResearch.WordTrace tailWord_7002763 prefixEnd_7002763 3595783328521090391257385 := by
  unfold tailWord_7002763
  simp only [CollatzResearch.WordTrace]
  refine ⟨255411749529193102548940943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170274499686128735032627295 255411749529193102548940943)
  ·
    refine ⟨383117624293789653823411415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255411749529193102548940943 383117624293789653823411415)
    ·
      refine ⟨574676436440684480735117123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383117624293789653823411415 574676436440684480735117123)
      ·
        refine ⟨862014654661026721102675685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574676436440684480735117123 862014654661026721102675685)
        ·
          refine ⟨161627747748942510206751691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862014654661026721102675685 161627747748942510206751691)
          ·
            refine ⟨242441621623413765310127537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161627747748942510206751691 242441621623413765310127537)
            ·
              refine ⟨181831216217560323982595653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242441621623413765310127537 181831216217560323982595653)
              ·
                refine ⟨34093353040792560746736685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181831216217560323982595653 34093353040792560746736685)
                ·
                  refine ⟨12785007390297210280026257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34093353040792560746736685 12785007390297210280026257)
                  ·
                    refine ⟨9588755542722907710019693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12785007390297210280026257 9588755542722907710019693)
                    ·
                      refine ⟨3595783328521090391257385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588755542722907710019693 3595783328521090391257385)
                      ·
                        rfl

theorem cell23_7002763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 3].length) (baseStart_7002763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002763 prefixEnd_7002763 := by exact prefixLift 7002763
  have htrace : WordTrace (prefixWord ++ tailWord_7002763) baseStart_7002763 baseEnd_7002763 := by
    simpa [prefixWord, tailWord_7002763, baseEnd_7002763] using wordTrace_append hprefix tailTrace_7002763
  have hstable : (prefixWord ++ tailWord_7002763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002763).length < 2 ^ (prefixWord ++ tailWord_7002763).sum := by decide
  have hdescent : baseEnd_7002763 < baseStart_7002763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002770 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7002770 : Nat := 118140960795 + 7002770 * 2 ^ 59
def prefixEnd_7002770 : Nat := 4983230072969 + 3 ^ 40 * 7002770 * 2
def baseEnd_7002770 : Nat := 1198595640961890621289951

theorem tailTrace_7002770 : CollatzResearch.WordTrace tailWord_7002770 prefixEnd_7002770 1198595640961890621289951 := by
  unfold tailWord_7002770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63853001210041935686111441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170274669893445161829630509 63853001210041935686111441)
  ·
    refine ⟨47889750907531451764583581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63853001210041935686111441 47889750907531451764583581)
    ·
      refine ⟨17958656590324294411718843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47889750907531451764583581 17958656590324294411718843)
      ·
        refine ⟨26937984885486441617578265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17958656590324294411718843 26937984885486441617578265)
        ·
          refine ⟨20203488664114831213183699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26937984885486441617578265 20203488664114831213183699)
          ·
            refine ⟨30305232996172246819775549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20203488664114831213183699 30305232996172246819775549)
            ·
              refine ⟨11364462373564592557415831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30305232996172246819775549 11364462373564592557415831)
              ·
                refine ⟨17046693560346888836123747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11364462373564592557415831 17046693560346888836123747)
                ·
                  refine ⟨25570040340520333254185621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17046693560346888836123747 25570040340520333254185621)
                  ·
                    refine ⟨1198595640961890621289951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25570040340520333254185621 1198595640961890621289951)
                    ·
                      rfl

theorem cell23_7002770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7002770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002770 prefixEnd_7002770 := by exact prefixLift 7002770
  have htrace : WordTrace (prefixWord ++ tailWord_7002770) baseStart_7002770 baseEnd_7002770 := by
    simpa [prefixWord, tailWord_7002770, baseEnd_7002770] using wordTrace_append hprefix tailTrace_7002770
  have hstable : (prefixWord ++ tailWord_7002770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002770).length < 2 ^ (prefixWord ++ tailWord_7002770).sum := by decide
  have hdescent : baseEnd_7002770 < baseStart_7002770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002797 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7002797 : Nat := 118140960795 + 7002797 * 2 ^ 59
def prefixEnd_7002797 : Nat := 4983230072969 + 3 ^ 40 * 7002797 * 2
def baseEnd_7002797 : Nat := 3595800786863343258232229

theorem tailTrace_7002797 : CollatzResearch.WordTrace tailWord_7002797 prefixEnd_7002797 3595800786863343258232229 := by
  unfold tailWord_7002797
  simp only [CollatzResearch.WordTrace]
  refine ⟨255412989611069926355678645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170275326407379950903785763 255412989611069926355678645)
  ·
    refine ⟨23944967776037805595844873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255412989611069926355678645 23944967776037805595844873)
    ·
      refine ⟨17958725832028354196883655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23944967776037805595844873 17958725832028354196883655)
      ·
        refine ⟨26938088748042531295325483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17958725832028354196883655 26938088748042531295325483)
        ·
          refine ⟨40407133122063796942988225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26938088748042531295325483 40407133122063796942988225)
          ·
            refine ⟨30305349841547847707241169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40407133122063796942988225 30305349841547847707241169)
            ·
              refine ⟨22729012381160885780430877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30305349841547847707241169 22729012381160885780430877)
              ·
                refine ⟨8523379642935332167661579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22729012381160885780430877 8523379642935332167661579)
                ·
                  refine ⟨12785069464402998251492369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523379642935332167661579 12785069464402998251492369)
                  ·
                    refine ⟨9588802098302248688619277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12785069464402998251492369 9588802098302248688619277)
                    ·
                      refine ⟨3595800786863343258232229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588802098302248688619277 3595800786863343258232229)
                      ·
                        rfl

theorem cell23_7002797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7002797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002797 prefixEnd_7002797 := by exact prefixLift 7002797
  have htrace : WordTrace (prefixWord ++ tailWord_7002797) baseStart_7002797 baseEnd_7002797 := by
    simpa [prefixWord, tailWord_7002797, baseEnd_7002797] using wordTrace_append hprefix tailTrace_7002797
  have hstable : (prefixWord ++ tailWord_7002797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002797).length < 2 ^ (prefixWord ++ tailWord_7002797).sum := by decide
  have hdescent : baseEnd_7002797 < baseStart_7002797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002810 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_7002810 : Nat := 118140960795 + 7002810 * 2 ^ 59
def prefixEnd_7002810 : Nat := 4983230072969 + 3 ^ 40 * 7002810 * 2
def baseEnd_7002810 : Nat := 3595807462111851707369669

theorem tailTrace_7002810 : CollatzResearch.WordTrace tailWord_7002810 prefixEnd_7002810 3595807462111851707369669 := by
  unfold tailWord_7002810
  simp only [CollatzResearch.WordTrace]
  refine ⟨63853365940005707393975471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170275642506681886383934589 63853365940005707393975471)
  ·
    refine ⟨95780048910008561090963207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63853365940005707393975471 95780048910008561090963207)
    ·
      refine ⟨143670073365012841636444811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95780048910008561090963207 143670073365012841636444811)
      ·
        refine ⟨215505110047519262454667217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143670073365012841636444811 215505110047519262454667217)
        ·
          refine ⟨161628832535639446841000413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215505110047519262454667217 161628832535639446841000413)
          ·
            refine ⟨60610812200864792565375155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161628832535639446841000413 60610812200864792565375155)
            ·
              refine ⟨90916218301297188848062733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60610812200864792565375155 90916218301297188848062733)
              ·
                refine ⟨34093581862986445818023525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90916218301297188848062733 34093581862986445818023525)
                ·
                  refine ⟨6392546599309958590879411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34093581862986445818023525 6392546599309958590879411)
                  ·
                    refine ⟨9588819898964937886319117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6392546599309958590879411 9588819898964937886319117)
                    ·
                      refine ⟨3595807462111851707369669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588819898964937886319117 3595807462111851707369669)
                      ·
                        rfl

theorem cell23_7002810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_7002810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002810 prefixEnd_7002810 := by exact prefixLift 7002810
  have htrace : WordTrace (prefixWord ++ tailWord_7002810) baseStart_7002810 baseEnd_7002810 := by
    simpa [prefixWord, tailWord_7002810, baseEnd_7002810] using wordTrace_append hprefix tailTrace_7002810
  have hstable : (prefixWord ++ tailWord_7002810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002810).length < 2 ^ (prefixWord ++ tailWord_7002810).sum := by decide
  have hdescent : baseEnd_7002810 < baseStart_7002810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002817 : List Nat := [1, 2, 6, 2, 1, 1, 2, 8]
def baseStart_7002817 : Nat := 118140960795 + 7002817 * 2 ^ 59
def prefixEnd_7002817 : Nat := 4983230072969 + 3 ^ 40 * 7002817 * 2
def baseEnd_7002817 : Nat := 133178187276904932591931

theorem tailTrace_7002817 : CollatzResearch.WordTrace tailWord_7002817 prefixEnd_7002817 133178187276904932591931 := by
  unfold tailWord_7002817
  simp only [CollatzResearch.WordTrace]
  refine ⟨255413719070997469771406705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170275812713998313180937803 255413719070997469771406705)
  ·
    refine ⟨191560289303248102328555029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255413719070997469771406705 191560289303248102328555029)
    ·
      refine ⟨8979388561089754796651017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 191560289303248102328555029 8979388561089754796651017)
      ·
        refine ⟨6734541420817316097488263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8979388561089754796651017 6734541420817316097488263)
        ·
          refine ⟨10101812131225974146232395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734541420817316097488263 10101812131225974146232395)
          ·
            refine ⟨15152718196838961219348593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101812131225974146232395 15152718196838961219348593)
            ·
              refine ⟨11364538647629220914511445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15152718196838961219348593 11364538647629220914511445)
              ·
                refine ⟨133178187276904932591931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11364538647629220914511445 133178187276904932591931)
                ·
                  rfl

theorem cell23_7002817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 8].length) (baseStart_7002817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002817 prefixEnd_7002817 := by exact prefixLift 7002817
  have htrace : WordTrace (prefixWord ++ tailWord_7002817) baseStart_7002817 baseEnd_7002817 := by
    simpa [prefixWord, tailWord_7002817, baseEnd_7002817] using wordTrace_append hprefix tailTrace_7002817
  have hstable : (prefixWord ++ tailWord_7002817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002817).length < 2 ^ (prefixWord ++ tailWord_7002817).sum := by decide
  have hdescent : baseEnd_7002817 < baseStart_7002817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002870 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_7002870 : Nat := 118140960795 + 7002870 * 2 ^ 59
def prefixEnd_7002870 : Nat := 4983230072969 + 3 ^ 40 * 7002870 * 2
def baseEnd_7002870 : Nat := 3595838270951121472619393

theorem tailTrace_7002870 : CollatzResearch.WordTrace tailWord_7002870 prefixEnd_7002870 3595838270951121472619393 := by
  unfold tailWord_7002870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963478258737841238942879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170277101426536973215390709 15963478258737841238942879)
  ·
    refine ⟨23945217388106761858414319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15963478258737841238942879 23945217388106761858414319)
    ·
      refine ⟨35917826082160142787621479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23945217388106761858414319 35917826082160142787621479)
      ·
        refine ⟨53876739123240214181432219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35917826082160142787621479 53876739123240214181432219)
        ·
          refine ⟨80815108684860321272148329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53876739123240214181432219 80815108684860321272148329)
          ·
            refine ⟨60611331513645240954111247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80815108684860321272148329 60611331513645240954111247)
            ·
              refine ⟨90916997270467861431166871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60611331513645240954111247 90916997270467861431166871)
              ·
                refine ⟨136375495905701792146750307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90916997270467861431166871 136375495905701792146750307)
                ·
                  refine ⟨204563243858552688220125461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136375495905701792146750307 204563243858552688220125461)
                  ·
                    refine ⟨9588902055869657260318381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 204563243858552688220125461 9588902055869657260318381)
                    ·
                      refine ⟨3595838270951121472619393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9588902055869657260318381 3595838270951121472619393)
                      ·
                        rfl

theorem cell23_7002870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_7002870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002870 prefixEnd_7002870 := by exact prefixLift 7002870
  have htrace : WordTrace (prefixWord ++ tailWord_7002870) baseStart_7002870 baseEnd_7002870 := by
    simpa [prefixWord, tailWord_7002870, baseEnd_7002870] using wordTrace_append hprefix tailTrace_7002870
  have hstable : (prefixWord ++ tailWord_7002870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002870).length < 2 ^ (prefixWord ++ tailWord_7002870).sum := by decide
  have hdescent : baseEnd_7002870 < baseStart_7002870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002884 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_7002884 : Nat := 118140960795 + 7002884 * 2 ^ 59
def prefixEnd_7002884 : Nat := 4983230072969 + 3 ^ 40 * 7002884 * 2
def baseEnd_7002884 : Nat := 3595845459680284417844329

theorem tailTrace_7002884 : CollatzResearch.WordTrace tailWord_7002884 prefixEnd_7002884 3595845459680284417844329 := by
  unfold tailWord_7002884
  simp only [CollatzResearch.WordTrace]
  refine ⟨127708081380877370107047853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170277441841169826809397137 127708081380877370107047853)
  ·
    refine ⟨47890530517829013790142945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127708081380877370107047853 47890530517829013790142945)
    ·
      refine ⟨35917897888371760342607209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47890530517829013790142945 35917897888371760342607209)
      ·
        refine ⟨26938423416278820256955407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35917897888371760342607209 26938423416278820256955407)
        ·
          refine ⟨40407635124418230385433111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26938423416278820256955407 40407635124418230385433111)
          ·
            refine ⟨60611452686627345578149667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40407635124418230385433111 60611452686627345578149667)
            ·
              refine ⟨90917179029941018367224501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60611452686627345578149667 90917179029941018367224501)
              ·
                refine ⟨8523485534056970471927297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90917179029941018367224501 8523485534056970471927297)
                ·
                  refine ⟨6392614150542727853945473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8523485534056970471927297 6392614150542727853945473)
                  ·
                    refine ⟨4794460612907045890459105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6392614150542727853945473 4794460612907045890459105)
                    ·
                      refine ⟨3595845459680284417844329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794460612907045890459105 3595845459680284417844329)
                      ·
                        rfl

theorem cell23_7002884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_7002884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002884 prefixEnd_7002884 := by exact prefixLift 7002884
  have htrace : WordTrace (prefixWord ++ tailWord_7002884) baseStart_7002884 baseEnd_7002884 := by
    simpa [prefixWord, tailWord_7002884, baseEnd_7002884] using wordTrace_append hprefix tailTrace_7002884
  have hstable : (prefixWord ++ tailWord_7002884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002884).length < 2 ^ (prefixWord ++ tailWord_7002884).sum := by decide
  have hdescent : baseEnd_7002884 < baseStart_7002884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002920 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7002920 : Nat := 118140960795 + 7002920 * 2 ^ 59
def prefixEnd_7002920 : Nat := 4983230072969 + 3 ^ 40 * 7002920 * 2
def baseEnd_7002920 : Nat := 1198621314994615425664721

theorem tailTrace_7002920 : CollatzResearch.WordTrace tailWord_7002920 prefixEnd_7002920 1198621314994615425664721 := by
  unfold tailWord_7002920
  simp only [CollatzResearch.WordTrace]
  refine ⟨127708737894812159181203107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170278317193082878908270809 127708737894812159181203107)
  ·
    refine ⟨191563106842218238771804661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127708737894812159181203107 191563106842218238771804661)
    ·
      refine ⟨17959041266457959884856687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191563106842218238771804661 17959041266457959884856687)
      ·
        refine ⟨26938561899686939827285031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17959041266457959884856687 26938561899686939827285031)
        ·
          refine ⟨40407842849530409740927547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26938561899686939827285031 40407842849530409740927547)
          ·
            refine ⟨60611764274295614611391321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40407842849530409740927547 60611764274295614611391321)
            ·
              refine ⟨45458823205721710958543491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60611764274295614611391321 45458823205721710958543491)
              ·
                refine ⟨68188234808582566437815237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45458823205721710958543491 68188234808582566437815237)
                ·
                  refine ⟨12785294026609231207090357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68188234808582566437815237 12785294026609231207090357)
                  ·
                    refine ⟨1198621314994615425664721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12785294026609231207090357 1198621314994615425664721)
                    ·
                      rfl

theorem cell23_7002920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7002920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002920 prefixEnd_7002920 := by exact prefixLift 7002920
  have htrace : WordTrace (prefixWord ++ tailWord_7002920) baseStart_7002920 baseEnd_7002920 := by
    simpa [prefixWord, tailWord_7002920, baseEnd_7002920] using wordTrace_append hprefix tailTrace_7002920
  have hstable : (prefixWord ++ tailWord_7002920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002920).length < 2 ^ (prefixWord ++ tailWord_7002920).sum := by decide
  have hdescent : baseEnd_7002920 < baseStart_7002920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002923 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4]
def baseStart_7002923 : Nat := 118140960795 + 7002923 * 2 ^ 59
def prefixEnd_7002923 : Nat := 4983230072969 + 3 ^ 40 * 7002923 * 2
def baseEnd_7002923 : Nat := 3595865485425809765256649

theorem tailTrace_7002923 : CollatzResearch.WordTrace tailWord_7002923 prefixEnd_7002923 3595865485425809765256649 := by
  unfold tailWord_7002923
  simp only [CollatzResearch.WordTrace]
  refine ⟨255417585208613449874765423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170278390139075633249843615 255417585208613449874765423)
  ·
    refine ⟨383126377812920174812148135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255417585208613449874765423 383126377812920174812148135)
    ·
      refine ⟨574689566719380262218222203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383126377812920174812148135 574689566719380262218222203)
      ·
        refine ⟨862034350079070393327333305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574689566719380262218222203 862034350079070393327333305)
        ·
          refine ⟨646525762559302794995499979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862034350079070393327333305 646525762559302794995499979)
          ·
            refine ⟨969788643838954192493249969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646525762559302794995499979 969788643838954192493249969)
            ·
              refine ⟨727341482879215644369937477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969788643838954192493249969 727341482879215644369937477)
              ·
                refine ⟨136376528039852933319363277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727341482879215644369937477 136376528039852933319363277)
                ·
                  refine ⟨51141198014944849994761229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136376528039852933319363277 51141198014944849994761229)
                  ·
                    refine ⟨19177949255604318748035461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51141198014944849994761229 19177949255604318748035461)
                    ·
                      refine ⟨3595865485425809765256649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19177949255604318748035461 3595865485425809765256649)
                      ·
                        rfl

theorem cell23_7002923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_7002923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002923 prefixEnd_7002923 := by exact prefixLift 7002923
  have htrace : WordTrace (prefixWord ++ tailWord_7002923) baseStart_7002923 baseEnd_7002923 := by
    simpa [prefixWord, tailWord_7002923, baseEnd_7002923] using wordTrace_append hprefix tailTrace_7002923
  have hstable : (prefixWord ++ tailWord_7002923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002923).length < 2 ^ (prefixWord ++ tailWord_7002923).sum := by decide
  have hdescent : baseEnd_7002923 < baseStart_7002923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002960 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_7002960 : Nat := 118140960795 + 7002960 * 2 ^ 59
def prefixEnd_7002960 : Nat := 4983230072969 + 3 ^ 40 * 7002960 * 2
def baseEnd_7002960 : Nat := 3595884484210026120493979

theorem tailTrace_7002960 : CollatzResearch.WordTrace tailWord_7002960 prefixEnd_7002960 3595884484210026120493979 := by
  unfold tailWord_7002960
  simp only [CollatzResearch.WordTrace]
  refine ⟨127709467354739702596931167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170279289806319603462574889 127709467354739702596931167)
  ·
    refine ⟨191564201032109553895396751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127709467354739702596931167 191564201032109553895396751)
    ·
      refine ⟨287346301548164330843095127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191564201032109553895396751 287346301548164330843095127)
      ·
        refine ⟨431019452322246496264642691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287346301548164330843095127 431019452322246496264642691)
        ·
          refine ⟨646529178483369744396964037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431019452322246496264642691 646529178483369744396964037)
          ·
            refine ⟨121224220965631827074430757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 646529178483369744396964037 121224220965631827074430757)
            ·
              refine ⟨22729541431055967576455767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121224220965631827074430757 22729541431055967576455767)
              ·
                refine ⟨34094312146583951364683651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22729541431055967576455767 34094312146583951364683651)
                ·
                  refine ⟨51141468219875927047025477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34094312146583951364683651 51141468219875927047025477)
                  ·
                    refine ⟨9589025291226736321317277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51141468219875927047025477 9589025291226736321317277)
                    ·
                      refine ⟨3595884484210026120493979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589025291226736321317277 3595884484210026120493979)
                      ·
                        rfl

theorem cell23_7002960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_7002960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002960 prefixEnd_7002960 := by exact prefixLift 7002960
  have htrace : WordTrace (prefixWord ++ tailWord_7002960) baseStart_7002960 baseEnd_7002960 := by
    simpa [prefixWord, tailWord_7002960, baseEnd_7002960] using wordTrace_append hprefix tailTrace_7002960
  have hstable : (prefixWord ++ tailWord_7002960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002960).length < 2 ^ (prefixWord ++ tailWord_7002960).sum := by decide
  have hdescent : baseEnd_7002960 < baseStart_7002960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002980 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 8]
def baseStart_7002980 : Nat := 118140960795 + 7002980 * 2 ^ 59
def prefixEnd_7002980 : Nat := 4983230072969 + 3 ^ 40 * 7002980 * 2
def baseEnd_7002980 : Nat := 399543861535901782471543

theorem tailTrace_7002980 : CollatzResearch.WordTrace tailWord_7002980 prefixEnd_7002980 399543861535901782471543 := by
  unfold tailWord_7002980
  simp only [CollatzResearch.WordTrace]
  refine ⟨127709832084703474304795197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170279776112937965739726929 127709832084703474304795197)
  ·
    refine ⟨47891187031763802864298199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127709832084703474304795197 47891187031763802864298199)
    ·
      refine ⟨71836780547645704296447299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47891187031763802864298199 71836780547645704296447299)
      ·
        refine ⟨107755170821468556444670949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71836780547645704296447299 107755170821468556444670949)
        ·
          refine ⟨20204094529025354333375803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107755170821468556444670949 20204094529025354333375803)
          ·
            refine ⟨30306141793538031500063705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20204094529025354333375803 30306141793538031500063705)
            ·
              refine ⟨22729606345153523625047779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30306141793538031500063705 22729606345153523625047779)
              ·
                refine ⟨34094409517730285437571669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22729606345153523625047779 34094409517730285437571669)
                ·
                  refine ⟨399543861535901782471543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34094409517730285437571669 399543861535901782471543)
                  ·
                    rfl

theorem cell23_7002980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_7002980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002980 prefixEnd_7002980 := by exact prefixLift 7002980
  have htrace : WordTrace (prefixWord ++ tailWord_7002980) baseStart_7002980 baseEnd_7002980 := by
    simpa [prefixWord, tailWord_7002980, baseEnd_7002980] using wordTrace_append hprefix tailTrace_7002980
  have hstable : (prefixWord ++ tailWord_7002980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002980).length < 2 ^ (prefixWord ++ tailWord_7002980).sum := by decide
  have hdescent : baseEnd_7002980 < baseStart_7002980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002984 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 3, 4]
def baseStart_7002984 : Nat := 118140960795 + 7002984 * 2 ^ 59
def prefixEnd_7002984 : Nat := 4983230072969 + 3 ^ 40 * 7002984 * 2
def baseEnd_7002984 : Nat := 1198632269248578008864623

theorem tailTrace_7002984 : CollatzResearch.WordTrace tailWord_7002984 prefixEnd_7002984 1198632269248578008864623 := by
  unfold tailWord_7002984
  simp only [CollatzResearch.WordTrace]
  refine ⟨127709905030696228646368003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170279873374261638195157337 127709905030696228646368003)
  ·
    refine ⟨191564857546044342969552005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127709905030696228646368003 191564857546044342969552005)
    ·
      refine ⟨35918410789883314306791001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191564857546044342969552005 35918410789883314306791001)
      ·
        refine ⟨26938808092412485730093251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35918410789883314306791001 26938808092412485730093251)
        ·
          refine ⟨40408212138618728595139877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26938808092412485730093251 40408212138618728595139877)
          ·
            refine ⟨7576539775991011611588727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40408212138618728595139877 7576539775991011611588727)
            ·
              refine ⟨11364809663986517417383091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576539775991011611588727 11364809663986517417383091)
              ·
                refine ⟨17047214495979776126074637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11364809663986517417383091 17047214495979776126074637)
                ·
                  refine ⟨6392705435992416047277989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17047214495979776126074637 6392705435992416047277989)
                  ·
                    refine ⟨1198632269248578008864623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392705435992416047277989 1198632269248578008864623)
                    ·
                      rfl

theorem cell23_7002984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_7002984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002984 prefixEnd_7002984 := by exact prefixLift 7002984
  have htrace : WordTrace (prefixWord ++ tailWord_7002984) baseStart_7002984 baseEnd_7002984 := by
    simpa [prefixWord, tailWord_7002984, baseEnd_7002984] using wordTrace_append hprefix tailTrace_7002984
  have hstable : (prefixWord ++ tailWord_7002984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002984).length < 2 ^ (prefixWord ++ tailWord_7002984).sum := by decide
  have hdescent : baseEnd_7002984 < baseStart_7002984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7002997 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 6]
def baseStart_7002997 : Nat := 118140960795 + 7002997 * 2 ^ 59
def prefixEnd_7002997 : Nat := 4983230072969 + 3 ^ 40 * 7002997 * 2
def baseEnd_7002997 : Nat := 399544831443804719525701

theorem tailTrace_7002997 : CollatzResearch.WordTrace tailWord_7002997 prefixEnd_7002997 399544831443804719525701 := by
  unfold tailWord_7002997
  simp only [CollatzResearch.WordTrace]
  refine ⟨255420284210345360512959245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170280189473563573675306163 255420284210345360512959245)
  ·
    refine ⟨95782606578879510192359717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255420284210345360512959245 95782606578879510192359717)
    ·
      refine ⟨17959238733539908161067447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95782606578879510192359717 17959238733539908161067447)
      ·
        refine ⟨26938858100309862241601171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17959238733539908161067447 26938858100309862241601171)
        ·
          refine ⟨40408287150464793362401757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26938858100309862241601171 40408287150464793362401757)
          ·
            refine ⟨15153107681424297510900659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40408287150464793362401757 15153107681424297510900659)
            ·
              refine ⟨22729661522136446266350989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15153107681424297510900659 22729661522136446266350989)
              ·
                refine ⟨8523623070801167349881621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22729661522136446266350989 8523623070801167349881621)
                ·
                  refine ⟨399544831443804719525701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8523623070801167349881621 399544831443804719525701)
                  ·
                    rfl

theorem cell23_7002997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_7002997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7002997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7002997 prefixEnd_7002997 := by exact prefixLift 7002997
  have htrace : WordTrace (prefixWord ++ tailWord_7002997) baseStart_7002997 baseEnd_7002997 := by
    simpa [prefixWord, tailWord_7002997, baseEnd_7002997] using wordTrace_append hprefix tailTrace_7002997
  have hstable : (prefixWord ++ tailWord_7002997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7002997).length < 2 ^ (prefixWord ++ tailWord_7002997).sum := by decide
  have hdescent : baseEnd_7002997 < baseStart_7002997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7002997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003007 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 3]
def baseStart_7003007 : Nat := 118140960795 + 7003007 * 2 ^ 59
def prefixEnd_7003007 : Nat := 4983230072969 + 3 ^ 40 * 7003007 * 2
def baseEnd_7003007 : Nat := 3595908617800787436606263

theorem tailTrace_7003007 : CollatzResearch.WordTrace tailWord_7003007 prefixEnd_7003007 3595908617800787436606263 := by
  unfold tailWord_7003007
  simp only [CollatzResearch.WordTrace]
  refine ⟨255420648940309132220823275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170280432626872754813882183 255420648940309132220823275)
  ·
    refine ⟨383130973410463698331234913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255420648940309132220823275 383130973410463698331234913)
    ·
      refine ⟨287348230057847773748426185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383130973410463698331234913 287348230057847773748426185)
      ·
        refine ⟨215511172543385830311319639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287348230057847773748426185 215511172543385830311319639)
        ·
          refine ⟨323266758815078745466979459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215511172543385830311319639 323266758815078745466979459)
          ·
            refine ⟨484900138222618118200469189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323266758815078745466979459 484900138222618118200469189)
            ·
              refine ⟨90918775916740897162587973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484900138222618118200469189 90918775916740897162587973)
              ·
                refine ⟨17047270484388918217985245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90918775916740897162587973 17047270484388918217985245)
                ·
                  refine ⟨6392726431645844331744467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17047270484388918217985245 6392726431645844331744467)
                  ·
                    refine ⟨9589089647468766497616701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6392726431645844331744467 9589089647468766497616701)
                    ·
                      refine ⟨3595908617800787436606263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589089647468766497616701 3595908617800787436606263)
                      ·
                        rfl

theorem cell23_7003007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_7003007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003007 prefixEnd_7003007 := by exact prefixLift 7003007
  have htrace : WordTrace (prefixWord ++ tailWord_7003007) baseStart_7003007 baseEnd_7003007 := by
    simpa [prefixWord, tailWord_7003007, baseEnd_7003007] using wordTrace_append hprefix tailTrace_7003007
  have hstable : (prefixWord ++ tailWord_7003007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003007).length < 2 ^ (prefixWord ++ tailWord_7003007).sum := by decide
  have hdescent : baseEnd_7003007 < baseStart_7003007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003062 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7003062 : Nat := 118140960795 + 7003062 * 2 ^ 59
def prefixEnd_7003062 : Nat := 4983230072969 + 3 ^ 40 * 7003062 * 2
def baseEnd_7003062 : Nat := 3595936859236784721418511

theorem tailTrace_7003062 : CollatzResearch.WordTrace tailWord_7003062 prefixEnd_7003062 3595936859236784721418511 := by
  unfold tailWord_7003062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963915934694367288379715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170281769970073251076050293 15963915934694367288379715)
  ·
    refine ⟨23945873902041550932569573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15963915934694367288379715 23945873902041550932569573)
    ·
      refine ⟨4489851356632790799856795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23945873902041550932569573 4489851356632790799856795)
      ·
        refine ⟨6734777034949186199785193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489851356632790799856795 6734777034949186199785193)
        ·
          refine ⟨5051082776211889649838895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6734777034949186199785193 5051082776211889649838895)
          ·
            refine ⟨7576624164317834474758343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051082776211889649838895 7576624164317834474758343)
            ·
              refine ⟨11364936246476751712137515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576624164317834474758343 11364936246476751712137515)
              ·
                refine ⟨17047404369715127568206273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11364936246476751712137515 17047404369715127568206273)
                ·
                  refine ⟨12785553277286345676154705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17047404369715127568206273 12785553277286345676154705)
                  ·
                    refine ⟨9589164957964759257116029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12785553277286345676154705 9589164957964759257116029)
                    ·
                      refine ⟨3595936859236784721418511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589164957964759257116029 3595936859236784721418511)
                      ·
                        rfl

theorem cell23_7003062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7003062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003062 prefixEnd_7003062 := by exact prefixLift 7003062
  have htrace : WordTrace (prefixWord ++ tailWord_7003062) baseStart_7003062 baseEnd_7003062 := by
    simpa [prefixWord, tailWord_7003062, baseEnd_7003062] using wordTrace_append hprefix tailTrace_7003062
  have hstable : (prefixWord ++ tailWord_7003062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003062).length < 2 ^ (prefixWord ++ tailWord_7003062).sum := by decide
  have hdescent : baseEnd_7003062 < baseStart_7003062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003064 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 5, 2, 2]
def baseStart_7003064 : Nat := 118140960795 + 7003064 * 2 ^ 59
def prefixEnd_7003064 : Nat := 4983230072969 + 3 ^ 40 * 7003064 * 2
def baseEnd_7003064 : Nat := 3595937886198093713593501

theorem tailTrace_7003064 : CollatzResearch.WordTrace tailWord_7003064 prefixEnd_7003064 3595937886198093713593501 := by
  unfold tailWord_7003064
  simp only [CollatzResearch.WordTrace]
  refine ⟨127711363950551315477824123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170281818600735087303765497 127711363950551315477824123)
  ·
    refine ⟨191567045925826973216736185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127711363950551315477824123 191567045925826973216736185)
    ·
      refine ⟨143675284444370229912552139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191567045925826973216736185 143675284444370229912552139)
      ·
        refine ⟨215512926666555344868828209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143675284444370229912552139 215512926666555344868828209)
        ·
          refine ⟨161634694999916508651621157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215512926666555344868828209 161634694999916508651621157)
          ·
            refine ⟨30306505312484345372178967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161634694999916508651621157 30306505312484345372178967)
            ·
              refine ⟨45459757968726518058268451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30306505312484345372178967 45459757968726518058268451)
              ·
                refine ⟨68189636953089777087402677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45459757968726518058268451 68189636953089777087402677)
                ·
                  refine ⟨6392778464352166601944001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68189636953089777087402677 6392778464352166601944001)
                  ·
                    refine ⟨4794583848264124951458001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6392778464352166601944001 4794583848264124951458001)
                    ·
                      refine ⟨3595937886198093713593501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794583848264124951458001 3595937886198093713593501)
                      ·
                        rfl

theorem cell23_7003064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_7003064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003064 prefixEnd_7003064 := by exact prefixLift 7003064
  have htrace : WordTrace (prefixWord ++ tailWord_7003064) baseStart_7003064 baseEnd_7003064 := by
    simpa [prefixWord, tailWord_7003064, baseEnd_7003064] using wordTrace_append hprefix tailTrace_7003064
  have hstable : (prefixWord ++ tailWord_7003064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003064).length < 2 ^ (prefixWord ++ tailWord_7003064).sum := by decide
  have hdescent : baseEnd_7003064 < baseStart_7003064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
