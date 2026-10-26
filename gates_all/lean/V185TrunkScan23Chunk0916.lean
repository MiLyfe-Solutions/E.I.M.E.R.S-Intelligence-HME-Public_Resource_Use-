import V185TrunkScan23Chunk0915

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5421390 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_5421390 : Nat := 118140960795 + 5421390 * 2 ^ 59
def prefixEnd_5421390 : Nat := 4983230072969 + 3 ^ 40 * 5421390 * 2
def baseEnd_5421390 : Nat := 2783778885478649020392487

theorem tailTrace_5421390 : CollatzResearch.WordTrace tailWord_5421390 prefixEnd_5421390 2783778885478649020392487 := by
  unfold tailWord_5421390
  simp only [CollatzResearch.WordTrace]
  refine ⟨24716792228654675567808703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131822891886158269694979749 24716792228654675567808703)
  ·
    refine ⟨37075188342982013351713055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24716792228654675567808703 37075188342982013351713055)
    ·
      refine ⟨55612782514473020027569583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37075188342982013351713055 55612782514473020027569583)
      ·
        refine ⟨83419173771709530041354375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55612782514473020027569583 83419173771709530041354375)
        ·
          refine ⟨125128760657564295062031563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83419173771709530041354375 125128760657564295062031563)
          ·
            refine ⟨187693140986346442593047345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125128760657564295062031563 187693140986346442593047345)
            ·
              refine ⟨140769855739759831944785509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187693140986346442593047345 140769855739759831944785509)
              ·
                refine ⟨26394347951204968489647283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140769855739759831944785509 26394347951204968489647283)
                ·
                  refine ⟨39591521926807452734470925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26394347951204968489647283 39591521926807452734470925)
                  ·
                    refine ⟨14846820722552794775426597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39591521926807452734470925 14846820722552794775426597)
                    ·
                      refine ⟨2783778885478649020392487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14846820722552794775426597 2783778885478649020392487)
                      ·
                        rfl

theorem cell23_5421390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_5421390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421390 prefixEnd_5421390 := by exact prefixLift 5421390
  have htrace : WordTrace (prefixWord ++ tailWord_5421390) baseStart_5421390 baseEnd_5421390 := by
    simpa [prefixWord, tailWord_5421390, baseEnd_5421390] using wordTrace_append hprefix tailTrace_5421390
  have hstable : (prefixWord ++ tailWord_5421390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421390).length < 2 ^ (prefixWord ++ tailWord_5421390).sum := by decide
  have hdescent : baseEnd_5421390 < baseStart_5421390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421440 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_5421440 : Nat := 118140960795 + 5421440 * 2 ^ 59
def prefixEnd_5421440 : Nat := 4983230072969 + 3 ^ 40 * 5421440 * 2
def baseEnd_5421440 : Nat := 2783804559511373824767257

theorem tailTrace_5421440 : CollatzResearch.WordTrace tailWord_5421440 prefixEnd_5421440 2783804559511373824767257 := by
  unfold tailWord_5421440
  simp only [CollatzResearch.WordTrace]
  refine ⟨98868080739528131540894887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131824107652704175387859849 98868080739528131540894887)
  ·
    refine ⟨148302121109292197311342331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98868080739528131540894887 148302121109292197311342331)
    ·
      refine ⟨222453181663938295967013497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148302121109292197311342331 222453181663938295967013497)
      ·
        refine ⟨166839886247953721975260123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222453181663938295967013497 166839886247953721975260123)
        ·
          refine ⟨250259829371930582962890185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166839886247953721975260123 250259829371930582962890185)
          ·
            refine ⟨187694872028947937222167639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250259829371930582962890185 187694872028947937222167639)
            ·
              refine ⟨281542308043421905833251459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187694872028947937222167639 281542308043421905833251459)
              ·
                refine ⟨422313462065132858749877189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281542308043421905833251459 422313462065132858749877189)
                ·
                  refine ⟨79183774137212411015601973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422313462065132858749877189 79183774137212411015601973)
                  ·
                    refine ⟨7423478825363663532712685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79183774137212411015601973 7423478825363663532712685)
                    ·
                      refine ⟨2783804559511373824767257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7423478825363663532712685 2783804559511373824767257)
                      ·
                        rfl

theorem cell23_5421440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_5421440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421440 prefixEnd_5421440 := by exact prefixLift 5421440
  have htrace : WordTrace (prefixWord ++ tailWord_5421440) baseStart_5421440 baseEnd_5421440 := by
    simpa [prefixWord, tailWord_5421440, baseEnd_5421440] using wordTrace_append hprefix tailTrace_5421440
  have hstable : (prefixWord ++ tailWord_5421440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421440).length < 2 ^ (prefixWord ++ tailWord_5421440).sum := by decide
  have hdescent : baseEnd_5421440 < baseStart_5421440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421474 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_5421474 : Nat := 118140960795 + 5421474 * 2 ^ 59
def prefixEnd_5421474 : Nat := 4983230072969 + 3 ^ 40 * 5421474 * 2
def baseEnd_5421474 : Nat := 2783822017853626691742101

theorem tailTrace_5421474 : CollatzResearch.WordTrace tailWord_5421474 prefixEnd_5421474 2783822017853626691742101 := by
  unfold tailWord_5421474
  simp only [CollatzResearch.WordTrace]
  refine ⟨49434350390233271722131869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131824934373955391259018317 49434350390233271722131869)
  ·
    refine ⟨18537881396337476895799451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49434350390233271722131869 18537881396337476895799451)
    ·
      refine ⟨27806822094506215343699177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18537881396337476895799451 27806822094506215343699177)
      ·
        refine ⟨20855116570879661507774383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27806822094506215343699177 20855116570879661507774383)
        ·
          refine ⟨31282674856319492261661575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20855116570879661507774383 31282674856319492261661575)
          ·
            refine ⟨46924012284479238392492363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31282674856319492261661575 46924012284479238392492363)
            ·
              refine ⟨70386018426718857588738545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46924012284479238392492363 70386018426718857588738545)
              ·
                refine ⟨52789513820039143191553909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70386018426718857588738545 52789513820039143191553909)
                ·
                  refine ⟨4949016920628669674208179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52789513820039143191553909 4949016920628669674208179)
                  ·
                    refine ⟨7423525380943004511312269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4949016920628669674208179 7423525380943004511312269)
                    ·
                      refine ⟨2783822017853626691742101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7423525380943004511312269 2783822017853626691742101)
                      ·
                        rfl

theorem cell23_5421474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_5421474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421474 prefixEnd_5421474 := by exact prefixLift 5421474
  have htrace : WordTrace (prefixWord ++ tailWord_5421474) baseStart_5421474 baseEnd_5421474 := by
    simpa [prefixWord, tailWord_5421474, baseEnd_5421474] using wordTrace_append hprefix tailTrace_5421474
  have hstable : (prefixWord ++ tailWord_5421474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421474).length < 2 ^ (prefixWord ++ tailWord_5421474).sum := by decide
  have hdescent : baseEnd_5421474 < baseStart_5421474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421477 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_5421477 : Nat := 118140960795 + 5421477 * 2 ^ 59
def prefixEnd_5421477 : Nat := 4983230072969 + 3 ^ 40 * 5421477 * 2
def baseEnd_5421477 : Nat := 927941186098530060001529

theorem tailTrace_5421477 : CollatzResearch.WordTrace tailWord_5421477 prefixEnd_5421477 927941186098530060001529 := by
  unfold tailWord_5421477
  simp only [CollatzResearch.WordTrace]
  refine ⟨197737510979922218400886685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131825007319948145600591123 197737510979922218400886685)
  ·
    refine ⟨74151566617470831900332507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197737510979922218400886685 74151566617470831900332507)
    ·
      refine ⟨111227349926206247850498761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74151566617470831900332507 111227349926206247850498761)
      ·
        refine ⟨83420512444654685887874071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111227349926206247850498761 83420512444654685887874071)
        ·
          refine ⟨125130768666982028831811107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83420512444654685887874071 125130768666982028831811107)
          ·
            refine ⟨187696153000473043247716661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125130768666982028831811107 187696153000473043247716661)
            ·
              refine ⟨17596514343794347804473437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187696153000473043247716661 17596514343794347804473437)
              ·
                refine ⟨6598692878922880426677539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17596514343794347804473437 6598692878922880426677539)
                ·
                  refine ⟨9898039318384320640016309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598692878922880426677539 9898039318384320640016309)
                  ·
                    refine ⟨927941186098530060001529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9898039318384320640016309 927941186098530060001529)
                    ·
                      rfl

theorem cell23_5421477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_5421477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421477 prefixEnd_5421477 := by exact prefixLift 5421477
  have htrace : WordTrace (prefixWord ++ tailWord_5421477) baseStart_5421477 baseEnd_5421477 := by
    simpa [prefixWord, tailWord_5421477, baseEnd_5421477] using wordTrace_append hprefix tailTrace_5421477
  have hstable : (prefixWord ++ tailWord_5421477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421477).length < 2 ^ (prefixWord ++ tailWord_5421477).sum := by decide
  have hdescent : baseEnd_5421477 < baseStart_5421477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421514 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_5421514 : Nat := 118140960795 + 5421514 * 2 ^ 59
def prefixEnd_5421514 : Nat := 4983230072969 + 3 ^ 40 * 5421514 * 2
def baseEnd_5421514 : Nat := 2783842557079806535241917

theorem tailTrace_5421514 : CollatzResearch.WordTrace tailWord_5421514 prefixEnd_5421514 2783842557079806535241917 := by
  unfold tailWord_5421514
  simp only [CollatzResearch.WordTrace]
  refine ⟨49434715120197043429995899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131825906987192115813322397 49434715120197043429995899)
  ·
    refine ⟨74152072680295565144993849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49434715120197043429995899 74152072680295565144993849)
    ·
      refine ⟨55614054510221673858745387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74152072680295565144993849 55614054510221673858745387)
      ·
        refine ⟨83421081765332510788118081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55614054510221673858745387 83421081765332510788118081)
        ·
          refine ⟨62565811323999383091088561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83421081765332510788118081 62565811323999383091088561)
          ·
            refine ⟨46924358492999537318316421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62565811323999383091088561 46924358492999537318316421)
            ·
              refine ⟨8798317217437413247184329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46924358492999537318316421 8798317217437413247184329)
              ·
                refine ⟨6598737913078059935388247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8798317217437413247184329 6598737913078059935388247)
                ·
                  refine ⟨9898106869617089903082371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598737913078059935388247 9898106869617089903082371)
                  ·
                    refine ⟨14847160304425634854623557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9898106869617089903082371 14847160304425634854623557)
                    ·
                      refine ⟨2783842557079806535241917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14847160304425634854623557 2783842557079806535241917)
                      ·
                        rfl

theorem cell23_5421514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_5421514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421514 prefixEnd_5421514 := by exact prefixLift 5421514
  have htrace : WordTrace (prefixWord ++ tailWord_5421514) baseStart_5421514 baseEnd_5421514 := by
    simpa [prefixWord, tailWord_5421514, baseEnd_5421514] using wordTrace_append hprefix tailTrace_5421514
  have hstable : (prefixWord ++ tailWord_5421514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421514).length < 2 ^ (prefixWord ++ tailWord_5421514).sum := by decide
  have hdescent : baseEnd_5421514 < baseStart_5421514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421524 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_5421524 : Nat := 118140960795 + 5421524 * 2 ^ 59
def prefixEnd_5421524 : Nat := 4983230072969 + 3 ^ 40 * 5421524 * 2
def baseEnd_5421524 : Nat := 927949230628783832038957

theorem tailTrace_5421524 : CollatzResearch.WordTrace tailWord_5421524 prefixEnd_5421524 927949230628783832038957 := by
  unfold tailWord_5421524
  simp only [CollatzResearch.WordTrace]
  refine ⟨98869612605375972713923813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131826150140501296951898417 98869612605375972713923813)
  ·
    refine ⟨18538052363507994883860715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98869612605375972713923813 18538052363507994883860715)
    ·
      refine ⟨27807078545261992325791073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18538052363507994883860715 27807078545261992325791073)
      ·
        refine ⟨20855308908946494244343305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27807078545261992325791073 20855308908946494244343305)
        ·
          refine ⟨15641481681709870683257479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20855308908946494244343305 15641481681709870683257479)
          ·
            refine ⟨23462222522564806024886219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15641481681709870683257479 23462222522564806024886219)
            ·
              refine ⟨35193333783847209037329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23462222522564806024886219 35193333783847209037329329)
              ·
                refine ⟨26395000337885406777996997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35193333783847209037329329 26395000337885406777996997)
                ·
                  refine ⟨4949062563353513770874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26395000337885406777996997 4949062563353513770874437)
                  ·
                    refine ⟨927949230628783832038957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949062563353513770874437 927949230628783832038957)
                    ·
                      rfl

theorem cell23_5421524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_5421524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421524 prefixEnd_5421524 := by exact prefixLift 5421524
  have htrace : WordTrace (prefixWord ++ tailWord_5421524) baseStart_5421524 baseEnd_5421524 := by
    simpa [prefixWord, tailWord_5421524, baseEnd_5421524] using wordTrace_append hprefix tailTrace_5421524
  have hstable : (prefixWord ++ tailWord_5421524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421524).length < 2 ^ (prefixWord ++ tailWord_5421524).sum := by decide
  have hdescent : baseEnd_5421524 < baseStart_5421524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421554 : List Nat := [3, 2, 1, 4, 2, 1, 2, 8]
def baseStart_5421554 : Nat := 118140960795 + 5421554 * 2 ^ 59
def prefixEnd_5421554 : Nat := 4983230072969 + 3 ^ 40 * 5421554 * 2
def baseEnd_5421554 : Nat := 103106040603925421434879

theorem tailTrace_5421554 : CollatzResearch.WordTrace tailWord_5421554 prefixEnd_5421554 103106040603925421434879 := by
  unfold tailWord_5421554
  simp only [CollatzResearch.WordTrace]
  refine ⟨49435079850160815137859929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131826879600428840367626477 49435079850160815137859929)
  ·
    refine ⟨37076309887620611353394947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49435079850160815137859929 37076309887620611353394947)
    ·
      refine ⟨55614464831430917030092421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37076309887620611353394947 55614464831430917030092421)
      ·
        refine ⟨10427712155893296943142329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55614464831430917030092421 10427712155893296943142329)
        ·
          refine ⟨7820784116919972707356747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10427712155893296943142329 7820784116919972707356747)
          ·
            refine ⟨11731176175379959061035121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820784116919972707356747 11731176175379959061035121)
            ·
              refine ⟨8798382131534969295776341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11731176175379959061035121 8798382131534969295776341)
              ·
                refine ⟨103106040603925421434879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8798382131534969295776341 103106040603925421434879)
                ·
                  rfl

theorem cell23_5421554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_5421554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421554 prefixEnd_5421554 := by exact prefixLift 5421554
  have htrace : WordTrace (prefixWord ++ tailWord_5421554) baseStart_5421554 baseEnd_5421554 := by
    simpa [prefixWord, tailWord_5421554, baseEnd_5421554] using wordTrace_append hprefix tailTrace_5421554
  have hstable : (prefixWord ++ tailWord_5421554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421554).length < 2 ^ (prefixWord ++ tailWord_5421554).sum := by decide
  have hdescent : baseEnd_5421554 < baseStart_5421554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421617 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_5421617 : Nat := 118140960795 + 5421617 * 2 ^ 59
def prefixEnd_5421617 : Nat := 4983230072969 + 3 ^ 40 * 5421617 * 2
def baseEnd_5421617 : Nat := 2783895445587219632253943

theorem tailTrace_5421617 : CollatzResearch.WordTrace tailWord_5421617 prefixEnd_5421617 2783895445587219632253943 := by
  unfold tailWord_5421617
  simp only [CollatzResearch.WordTrace]
  refine ⟨197742617199415022310983105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131828411466276681540655403 197742617199415022310983105)
  ·
    refine ⟨148306962899561266733237329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197742617199415022310983105 148306962899561266733237329)
    ·
      refine ⟨111230222174670950049927997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148306962899561266733237329 111230222174670950049927997)
      ·
        refine ⟨41711333315501606268722999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111230222174670950049927997 41711333315501606268722999)
        ·
          refine ⟨62566999973252409403084499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41711333315501606268722999 62566999973252409403084499)
          ·
            refine ⟨93850499959878614104626749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62566999973252409403084499 93850499959878614104626749)
            ·
              refine ⟨35193937484954480289235031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93850499959878614104626749 35193937484954480289235031)
              ·
                refine ⟨52790906227431720433852547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35193937484954480289235031 52790906227431720433852547)
                ·
                  refine ⟨79186359341147580650778821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52790906227431720433852547 79186359341147580650778821)
                  ·
                    refine ⟨14847442376465171372021029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79186359341147580650778821 14847442376465171372021029)
                    ·
                      refine ⟨2783895445587219632253943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14847442376465171372021029 2783895445587219632253943)
                      ·
                        rfl

theorem cell23_5421617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_5421617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421617 prefixEnd_5421617 := by exact prefixLift 5421617
  have htrace : WordTrace (prefixWord ++ tailWord_5421617) baseStart_5421617 baseEnd_5421617 := by
    simpa [prefixWord, tailWord_5421617, baseEnd_5421617] using wordTrace_append hprefix tailTrace_5421617
  have hstable : (prefixWord ++ tailWord_5421617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421617).length < 2 ^ (prefixWord ++ tailWord_5421617).sum := by decide
  have hdescent : baseEnd_5421617 < baseStart_5421617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421621 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_5421621 : Nat := 118140960795 + 5421621 * 2 ^ 59
def prefixEnd_5421621 : Nat := 4983230072969 + 3 ^ 40 * 5421621 * 2
def baseEnd_5421621 : Nat := 2783897499509837616603925

theorem tailTrace_5421621 : CollatzResearch.WordTrace tailWord_5421621 prefixEnd_5421621 2783897499509837616603925 := by
  unfold tailWord_5421621
  simp only [CollatzResearch.WordTrace]
  refine ⟨197742763091400530994128717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131828508727600353996085811 197742763091400530994128717)
  ·
    refine ⟨74153536159275199122798269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197742763091400530994128717 74153536159275199122798269)
    ·
      refine ⟨27807576059728199671049351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74153536159275199122798269 27807576059728199671049351)
      ·
        refine ⟨41711364089592299506574027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27807576059728199671049351 41711364089592299506574027)
        ·
          refine ⟨62567046134388449259861041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41711364089592299506574027 62567046134388449259861041)
          ·
            refine ⟨46925284600791336944895781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62567046134388449259861041 46925284600791336944895781)
            ·
              refine ⟨8798490862648375677167959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46925284600791336944895781 8798490862648375677167959)
              ·
                refine ⟨13197736293972563515751939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8798490862648375677167959 13197736293972563515751939)
                ·
                  refine ⟨19796604440958845273627909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13197736293972563515751939 19796604440958845273627909)
                  ·
                    refine ⟨3711863332679783488805233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19796604440958845273627909 3711863332679783488805233)
                    ·
                      refine ⟨2783897499509837616603925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711863332679783488805233 2783897499509837616603925)
                      ·
                        rfl

theorem cell23_5421621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_5421621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421621 prefixEnd_5421621 := by exact prefixLift 5421621
  have htrace : WordTrace (prefixWord ++ tailWord_5421621) baseStart_5421621 baseEnd_5421621 := by
    simpa [prefixWord, tailWord_5421621, baseEnd_5421621] using wordTrace_append hprefix tailTrace_5421621
  have hstable : (prefixWord ++ tailWord_5421621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421621).length < 2 ^ (prefixWord ++ tailWord_5421621).sum := by decide
  have hdescent : baseEnd_5421621 < baseStart_5421621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421664 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 7, 2]
def baseStart_5421664 : Nat := 118140960795 + 5421664 * 2 ^ 59
def prefixEnd_5421664 : Nat := 4983230072969 + 3 ^ 40 * 5421664 * 2
def baseEnd_5421664 : Nat := 2783919579177980948366227

theorem tailTrace_5421664 : CollatzResearch.WordTrace tailWord_5421664 prefixEnd_5421664 2783919579177980948366227 := by
  unfold tailWord_5421664
  simp only [CollatzResearch.WordTrace]
  refine ⟨98872165715122374668972023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131829554286829832891962697 98872165715122374668972023)
  ·
    refine ⟨148308248572683562003458035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98872165715122374668972023 148308248572683562003458035)
    ·
      refine ⟨222462372859025343005187053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148308248572683562003458035 222462372859025343005187053)
      ·
        refine ⟨83423389822134503626945145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222462372859025343005187053 83423389822134503626945145)
        ·
          refine ⟨62567542366600877720208859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83423389822134503626945145 62567542366600877720208859)
          ·
            refine ⟨93851313549901316580313289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62567542366600877720208859 93851313549901316580313289)
            ·
              refine ⟨70388485162425987435234967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93851313549901316580313289 70388485162425987435234967)
              ·
                refine ⟨105582727743638981152852451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70388485162425987435234967 105582727743638981152852451)
                ·
                  refine ⟨158374091615458471729278677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105582727743638981152852451 158374091615458471729278677)
                  ·
                    refine ⟨3711892772237307931154969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 158374091615458471729278677 3711892772237307931154969)
                    ·
                      refine ⟨2783919579177980948366227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711892772237307931154969 2783919579177980948366227)
                      ·
                        rfl

theorem cell23_5421664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_5421664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421664 prefixEnd_5421664 := by exact prefixLift 5421664
  have htrace : WordTrace (prefixWord ++ tailWord_5421664) baseStart_5421664 baseEnd_5421664 := by
    simpa [prefixWord, tailWord_5421664, baseEnd_5421664] using wordTrace_append hprefix tailTrace_5421664
  have hstable : (prefixWord ++ tailWord_5421664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421664).length < 2 ^ (prefixWord ++ tailWord_5421664).sum := by decide
  have hdescent : baseEnd_5421664 < baseStart_5421664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421667 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5421667 : Nat := 118140960795 + 5421667 * 2 ^ 59
def prefixEnd_5421667 : Nat := 4983230072969 + 3 ^ 40 * 5421667 * 2
def baseEnd_5421667 : Nat := 2783921119619944436628713

theorem tailTrace_5421667 : CollatzResearch.WordTrace tailWord_5421667 prefixEnd_5421667 2783921119619944436628713 := by
  unfold tailWord_5421667
  simp only [CollatzResearch.WordTrace]
  refine ⟨197744440849233880850303255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131829627232822587233535503 197744440849233880850303255)
  ·
    refine ⟨296616661273850821275454883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197744440849233880850303255 296616661273850821275454883)
    ·
      refine ⟨444924991910776231913182325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296616661273850821275454883 444924991910776231913182325)
      ·
        refine ⟨41711717991635271741860843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 444924991910776231913182325 41711717991635271741860843)
        ·
          refine ⟨62567576987452907612791265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41711717991635271741860843 62567576987452907612791265)
          ·
            refine ⟨46925682740589680709593449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62567576987452907612791265 46925682740589680709593449)
            ·
              refine ⟨35194262055442260532195087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46925682740589680709593449 35194262055442260532195087)
              ·
                refine ⟨52791393083163390798292631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35194262055442260532195087 52791393083163390798292631)
                ·
                  refine ⟨79187089624745086197438947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52791393083163390798292631 79187089624745086197438947)
                  ·
                    refine ⟨118780634437117629296158421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79187089624745086197438947 118780634437117629296158421)
                    ·
                      refine ⟨2783921119619944436628713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118780634437117629296158421 2783921119619944436628713)
                      ·
                        rfl

theorem cell23_5421667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5421667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421667 prefixEnd_5421667 := by exact prefixLift 5421667
  have htrace : WordTrace (prefixWord ++ tailWord_5421667) baseStart_5421667 baseEnd_5421667 := by
    simpa [prefixWord, tailWord_5421667, baseEnd_5421667] using wordTrace_append hprefix tailTrace_5421667
  have hstable : (prefixWord ++ tailWord_5421667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421667).length < 2 ^ (prefixWord ++ tailWord_5421667).sum := by decide
  have hdescent : baseEnd_5421667 < baseStart_5421667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421672 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5421672 : Nat := 118140960795 + 5421672 * 2 ^ 59
def prefixEnd_5421672 : Nat := 4983230072969 + 3 ^ 40 * 5421672 * 2
def baseEnd_5421672 : Nat := 2783923687023216917066191

theorem tailTrace_5421672 : CollatzResearch.WordTrace tailWord_5421672 prefixEnd_5421672 2783923687023216917066191 := by
  unfold tailWord_5421672
  simp only [CollatzResearch.WordTrace]
  refine ⟨98872311607107883352117635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131829748809477177802823513 98872311607107883352117635)
  ·
    refine ⟨148308467410661825028176453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98872311607107883352117635 148308467410661825028176453)
    ·
      refine ⟨27807837639499092192783085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148308467410661825028176453 27807837639499092192783085)
      ·
        refine ⟨10427939114812159572293657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27807837639499092192783085 10427939114812159572293657)
        ·
          refine ⟨7820954336109119679220243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10427939114812159572293657 7820954336109119679220243)
          ·
            refine ⟨11731431504163679518830365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820954336109119679220243 11731431504163679518830365)
            ·
              refine ⟨4399286814061379819561387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11731431504163679518830365 4399286814061379819561387)
              ·
                refine ⟨6598930221092069729342081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399286814061379819561387 6598930221092069729342081)
                ·
                  refine ⟨4949197665819052297006561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6598930221092069729342081 4949197665819052297006561)
                  ·
                    refine ⟨3711898249364289222754921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4949197665819052297006561 3711898249364289222754921)
                    ·
                      refine ⟨2783923687023216917066191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711898249364289222754921 2783923687023216917066191)
                      ·
                        rfl

theorem cell23_5421672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5421672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421672 prefixEnd_5421672 := by exact prefixLift 5421672
  have htrace : WordTrace (prefixWord ++ tailWord_5421672) baseStart_5421672 baseEnd_5421672 := by
    simpa [prefixWord, tailWord_5421672, baseEnd_5421672] using wordTrace_append hprefix tailTrace_5421672
  have hstable : (prefixWord ++ tailWord_5421672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421672).length < 2 ^ (prefixWord ++ tailWord_5421672).sum := by decide
  have hdescent : baseEnd_5421672 < baseStart_5421672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421707 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_5421707 : Nat := 118140960795 + 5421707 * 2 ^ 59
def prefixEnd_5421707 : Nat := 4983230072969 + 3 ^ 40 * 5421707 * 2
def baseEnd_5421707 : Nat := 2783941658846124280128529

theorem tailTrace_5421707 : CollatzResearch.WordTrace tailWord_5421707 prefixEnd_5421707 2783941658846124280128529 := by
  unfold tailWord_5421707
  simp only [CollatzResearch.WordTrace]
  refine ⟨197745899769088967681759375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131830599846059311787839583 197745899769088967681759375)
  ·
    refine ⟨296618849653633451522639063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197745899769088967681759375 296618849653633451522639063)
    ·
      refine ⟨444928274480450177283958595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296618849653633451522639063 444928274480450177283958595)
      ·
        refine ⟨667392411720675265925937893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444928274480450177283958595 667392411720675265925937893)
        ·
          refine ⟨125136077197626612361113355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 667392411720675265925937893 125136077197626612361113355)
          ·
            refine ⟨187704115796439918541670033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125136077197626612361113355 187704115796439918541670033)
            ·
              refine ⟨140778086847329938906252525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187704115796439918541670033 140778086847329938906252525)
              ·
                refine ⟨52791782567748727089844697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140778086847329938906252525 52791782567748727089844697)
                ·
                  refine ⟨39593836925811545317383523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52791782567748727089844697 39593836925811545317383523)
                  ·
                    refine ⟨59390755388717317976075285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39593836925811545317383523 59390755388717317976075285)
                    ·
                      refine ⟨2783941658846124280128529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59390755388717317976075285 2783941658846124280128529)
                      ·
                        rfl

theorem cell23_5421707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_5421707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421707 prefixEnd_5421707 := by exact prefixLift 5421707
  have htrace : WordTrace (prefixWord ++ tailWord_5421707) baseStart_5421707 baseEnd_5421707 := by
    simpa [prefixWord, tailWord_5421707, baseEnd_5421707] using wordTrace_append hprefix tailTrace_5421707
  have hstable : (prefixWord ++ tailWord_5421707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421707).length < 2 ^ (prefixWord ++ tailWord_5421707).sum := by decide
  have hdescent : baseEnd_5421707 < baseStart_5421707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421737 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_5421737 : Nat := 118140960795 + 5421737 * 2 ^ 59
def prefixEnd_5421737 : Nat := 4983230072969 + 3 ^ 40 * 5421737 * 2
def baseEnd_5421737 : Nat := 2783957063265759162753391

theorem tailTrace_5421737 : CollatzResearch.WordTrace tailWord_5421737 prefixEnd_5421737 2783957063265759162753391 := by
  unfold tailWord_5421737
  simp only [CollatzResearch.WordTrace]
  refine ⟨197746993958980282805351465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131831329305986855203567643 197746993958980282805351465)
  ·
    refine ⟨148310245469235212104013599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197746993958980282805351465 148310245469235212104013599)
    ·
      refine ⟨222465368203852818156020399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148310245469235212104013599 222465368203852818156020399)
      ·
        refine ⟨333698052305779227234030599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222465368203852818156020399 333698052305779227234030599)
        ·
          refine ⟨500547078458668840851045899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333698052305779227234030599 500547078458668840851045899)
          ·
            refine ⟨750820617688003261276568849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500547078458668840851045899 750820617688003261276568849)
            ·
              refine ⟨563115463266002445957426637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750820617688003261276568849 563115463266002445957426637)
              ·
                refine ⟨211168298724750917234034989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563115463266002445957426637 211168298724750917234034989)
                ·
                  refine ⟨79188112021781593962763121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211168298724750917234034989 79188112021781593962763121)
                  ·
                    refine ⟨59391084016336195472072341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79188112021781593962763121 59391084016336195472072341)
                    ·
                      refine ⟨2783957063265759162753391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59391084016336195472072341 2783957063265759162753391)
                      ·
                        rfl

theorem cell23_5421737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_5421737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421737 prefixEnd_5421737 := by exact prefixLift 5421737
  have htrace : WordTrace (prefixWord ++ tailWord_5421737) baseStart_5421737 baseEnd_5421737 := by
    simpa [prefixWord, tailWord_5421737, baseEnd_5421737] using wordTrace_append hprefix tailTrace_5421737
  have hstable : (prefixWord ++ tailWord_5421737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421737).length < 2 ^ (prefixWord ++ tailWord_5421737).sum := by decide
  have hdescent : baseEnd_5421737 < baseStart_5421737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421772 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_5421772 : Nat := 118140960795 + 5421772 * 2 ^ 59
def prefixEnd_5421772 : Nat := 4983230072969 + 3 ^ 40 * 5421772 * 2
def baseEnd_5421772 : Nat := 927991678362888841938577

theorem tailTrace_5421772 : CollatzResearch.WordTrace tailWord_5421772 prefixEnd_5421772 927991678362888841938577 := by
  unfold tailWord_5421772
  simp only [CollatzResearch.WordTrace]
  refine ⟨98874135256926741891437785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131832180342568989188583713 98874135256926741891437785)
  ·
    refine ⟨74155601442695056418578339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98874135256926741891437785 74155601442695056418578339)
    ·
      refine ⟨111233402164042584627867509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74155601442695056418578339 111233402164042584627867509)
      ·
        refine ⟨10428131452878992308862579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111233402164042584627867509 10428131452878992308862579)
        ·
          refine ⟨15642197179318488463293869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428131452878992308862579 15642197179318488463293869)
          ·
            refine ⟨5865823942244433173735201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15642197179318488463293869 5865823942244433173735201)
            ·
              refine ⟨4399367956683324880301401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865823942244433173735201 4399367956683324880301401)
              ·
                refine ⟨3299525967512493660226051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399367956683324880301401 3299525967512493660226051)
                ·
                  refine ⟨4949288951268740490339077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299525967512493660226051 4949288951268740490339077)
                  ·
                    refine ⟨927991678362888841938577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949288951268740490339077 927991678362888841938577)
                    ·
                      rfl

theorem cell23_5421772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_5421772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421772 prefixEnd_5421772 := by exact prefixLift 5421772
  have htrace : WordTrace (prefixWord ++ tailWord_5421772) baseStart_5421772 baseEnd_5421772 := by
    simpa [prefixWord, tailWord_5421772, baseEnd_5421772] using wordTrace_append hprefix tailTrace_5421772
  have hstable : (prefixWord ++ tailWord_5421772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421772).length < 2 ^ (prefixWord ++ tailWord_5421772).sum := by decide
  have hdescent : baseEnd_5421772 < baseStart_5421772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421818 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4]
def baseStart_5421818 : Nat := 118140960795 + 5421818 * 2 ^ 59
def prefixEnd_5421818 : Nat := 4983230072969 + 3 ^ 40 * 5421818 * 2
def baseEnd_5421818 : Nat := 2783998655198773345840519

theorem tailTrace_5421818 : CollatzResearch.WordTrace tailWord_5421818 prefixEnd_5421818 2783998655198773345840519 := by
  unfold tailWord_5421818
  simp only [CollatzResearch.WordTrace]
  refine ⟨49437487067921708409762527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131833298847791222426033405 49437487067921708409762527)
  ·
    refine ⟨74156230601882562614643791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49437487067921708409762527 74156230601882562614643791)
    ·
      refine ⟨111234345902823843921965687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74156230601882562614643791 111234345902823843921965687)
      ·
        refine ⟨166851518854235765882948531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111234345902823843921965687 166851518854235765882948531)
        ·
          refine ⟨250277278281353648824422797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166851518854235765882948531 250277278281353648824422797)
          ·
            refine ⟨93853979355507618309158549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250277278281353648824422797 93853979355507618309158549)
            ·
              refine ⟨4399405282289419608241807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93853979355507618309158549 4399405282289419608241807)
              ·
                refine ⟨6599107923434129412362711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399405282289419608241807 6599107923434129412362711)
                ·
                  refine ⟨9898661885151194118544067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6599107923434129412362711 9898661885151194118544067)
                  ·
                    refine ⟨14847992827726791177816101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9898661885151194118544067 14847992827726791177816101)
                    ·
                      refine ⟨2783998655198773345840519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14847992827726791177816101 2783998655198773345840519)
                      ·
                        rfl

theorem cell23_5421818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_5421818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421818 prefixEnd_5421818 := by exact prefixLift 5421818
  have htrace : WordTrace (prefixWord ++ tailWord_5421818) baseStart_5421818 baseEnd_5421818 := by
    simpa [prefixWord, tailWord_5421818, baseEnd_5421818] using wordTrace_append hprefix tailTrace_5421818
  have hstable : (prefixWord ++ tailWord_5421818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421818).length < 2 ^ (prefixWord ++ tailWord_5421818).sum := by decide
  have hdescent : baseEnd_5421818 < baseStart_5421818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421851 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 3]
def baseStart_5421851 : Nat := 118140960795 + 5421851 * 2 ^ 59
def prefixEnd_5421851 : Nat := 4983230072969 + 3 ^ 40 * 5421851 * 2
def baseEnd_5421851 : Nat := 2784015600060371716727867

theorem tailTrace_5421851 : CollatzResearch.WordTrace tailWord_5421851 prefixEnd_5421851 2784015600060371716727867 := by
  unfold tailWord_5421851
  simp only [CollatzResearch.WordTrace]
  refine ⟨197751151880567280275001407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131834101253711520183334271 197751151880567280275001407)
  ·
    refine ⟨296626727820850920412502111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197751151880567280275001407 296626727820850920412502111)
    ·
      refine ⟨444940091731276380618753167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296626727820850920412502111 444940091731276380618753167)
      ·
        refine ⟨667410137596914570928129751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444940091731276380618753167 667410137596914570928129751)
        ·
          refine ⟨1001115206395371856392194627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667410137596914570928129751 1001115206395371856392194627)
          ·
            refine ⟨1501672809593057784588291941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001115206395371856392194627 1501672809593057784588291941)
            ·
              refine ⟨281563651798698334610304739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1501672809593057784588291941 281563651798698334610304739)
              ·
                refine ⟨422345477698047501915457109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281563651798698334610304739 422345477698047501915457109)
                ·
                  refine ⟨4949361066773994163071763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 422345477698047501915457109 4949361066773994163071763)
                  ·
                    refine ⟨7424041600160991244607645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4949361066773994163071763 7424041600160991244607645)
                    ·
                      refine ⟨2784015600060371716727867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7424041600160991244607645 2784015600060371716727867)
                      ·
                        rfl

theorem cell23_5421851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 3].length) (baseStart_5421851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421851 prefixEnd_5421851 := by exact prefixLift 5421851
  have htrace : WordTrace (prefixWord ++ tailWord_5421851) baseStart_5421851 baseEnd_5421851 := by
    simpa [prefixWord, tailWord_5421851, baseEnd_5421851] using wordTrace_append hprefix tailTrace_5421851
  have hstable : (prefixWord ++ tailWord_5421851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421851).length < 2 ^ (prefixWord ++ tailWord_5421851).sum := by decide
  have hdescent : baseEnd_5421851 < baseStart_5421851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421858 : List Nat := [3, 3, 1, 1, 2, 4, 2, 7]
def baseStart_5421858 : Nat := 118140960795 + 5421858 * 2 ^ 59
def prefixEnd_5421858 : Nat := 4983230072969 + 3 ^ 40 * 5421858 * 2
def baseEnd_5421858 : Nat := 103111822015739007012605

theorem tailTrace_5421858 : CollatzResearch.WordTrace tailWord_5421858 prefixEnd_5421858 103111822015739007012605 := by
  unfold tailWord_5421858
  simp only [CollatzResearch.WordTrace]
  refine ⟨49437851797885480117626557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131834271461027946980337485 49437851797885480117626557)
  ·
    refine ⟨18539194424207055044109959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49437851797885480117626557 18539194424207055044109959)
    ·
      refine ⟨27808791636310582566164939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18539194424207055044109959 27808791636310582566164939)
      ·
        refine ⟨41713187454465873849247409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27808791636310582566164939 41713187454465873849247409)
        ·
          refine ⟨31284890590849405386935557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41713187454465873849247409 31284890590849405386935557)
          ·
            refine ⟨5865916985784263510050417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31284890590849405386935557 5865916985784263510050417)
            ·
              refine ⟨4399437739338197632537813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865916985784263510050417 4399437739338197632537813)
              ·
                refine ⟨103111822015739007012605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4399437739338197632537813 103111822015739007012605)
                ·
                  rfl

theorem cell23_5421858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_5421858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421858 prefixEnd_5421858 := by exact prefixLift 5421858
  have htrace : WordTrace (prefixWord ++ tailWord_5421858) baseStart_5421858 baseEnd_5421858 := by
    simpa [prefixWord, tailWord_5421858, baseEnd_5421858] using wordTrace_append hprefix tailTrace_5421858
  have hstable : (prefixWord ++ tailWord_5421858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421858).length < 2 ^ (prefixWord ++ tailWord_5421858).sum := by decide
  have hdescent : baseEnd_5421858 < baseStart_5421858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421886 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_5421886 : Nat := 118140960795 + 5421886 * 2 ^ 59
def prefixEnd_5421886 : Nat := 4983230072969 + 3 ^ 40 * 5421886 * 2
def baseEnd_5421886 : Nat := 2784033571883279079790207

theorem tailTrace_5421886 : CollatzResearch.WordTrace tailWord_5421886 prefixEnd_5421886 2784033571883279079790207 := by
  unfold tailWord_5421886
  simp only [CollatzResearch.WordTrace]
  refine ⟨24719053554430060156565689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131834952290293654168350341 24719053554430060156565689)
  ·
    refine ⟨18539290165822545117424267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24719053554430060156565689 18539290165822545117424267)
    ·
      refine ⟨27808935248733817676136401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18539290165822545117424267 27808935248733817676136401)
      ·
        refine ⟨20856701436550363257102301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27808935248733817676136401 20856701436550363257102301)
        ·
          refine ⟨7821263038706386221413363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20856701436550363257102301 7821263038706386221413363)
          ·
            refine ⟨11731894558059579332120045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821263038706386221413363 11731894558059579332120045)
            ·
              refine ⟨4399460459272342249545017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11731894558059579332120045 4399460459272342249545017)
              ·
                refine ⟨3299595344454256687158763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399460459272342249545017 3299595344454256687158763)
                ·
                  refine ⟨4949393016681385030738145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299595344454256687158763 4949393016681385030738145)
                  ·
                    refine ⟨3712044762511038773053609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4949393016681385030738145 3712044762511038773053609)
                    ·
                      refine ⟨2784033571883279079790207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712044762511038773053609 2784033571883279079790207)
                      ·
                        rfl

theorem cell23_5421886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_5421886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421886 prefixEnd_5421886 := by exact prefixLift 5421886
  have htrace : WordTrace (prefixWord ++ tailWord_5421886) baseStart_5421886 baseEnd_5421886 := by
    simpa [prefixWord, tailWord_5421886, baseEnd_5421886] using wordTrace_append hprefix tailTrace_5421886
  have hstable : (prefixWord ++ tailWord_5421886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421886).length < 2 ^ (prefixWord ++ tailWord_5421886).sum := by decide
  have hdescent : baseEnd_5421886 < baseStart_5421886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421911 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_5421911 : Nat := 118140960795 + 5421911 * 2 ^ 59
def prefixEnd_5421911 : Nat := 4983230072969 + 3 ^ 40 * 5421911 * 2
def baseEnd_5421911 : Nat := 2784046408899641481977591

theorem tailTrace_5421911 : CollatzResearch.WordTrace tailWord_5421911 prefixEnd_5421911 2784046408899641481977591 := by
  unfold tailWord_5421911
  simp only [CollatzResearch.WordTrace]
  refine ⟨197753340260349910522185587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131835560173566607014790391 197753340260349910522185587)
  ·
    refine ⟨296630010390524865783278381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197753340260349910522185587 296630010390524865783278381)
    ·
      refine ⟨111236253896446824668729393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296630010390524865783278381 111236253896446824668729393)
      ·
        refine ⟨83427190422335118501547045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111236253896446824668729393 83427190422335118501547045)
        ·
          refine ⟨15642598204187834719040071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83427190422335118501547045 15642598204187834719040071)
          ·
            refine ⟨23463897306281752078560107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15642598204187834719040071 23463897306281752078560107)
            ·
              refine ⟨35195845959422628117840161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23463897306281752078560107 35195845959422628117840161)
              ·
                refine ⟨26396884469566971088380121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35195845959422628117840161 26396884469566971088380121)
                ·
                  refine ⟨19797663352175228316285091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26396884469566971088380121 19797663352175228316285091)
                  ·
                    refine ⟨29696495028262842474427637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19797663352175228316285091 29696495028262842474427637)
                    ·
                      refine ⟨2784046408899641481977591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29696495028262842474427637 2784046408899641481977591)
                      ·
                        rfl

theorem cell23_5421911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_5421911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421911 prefixEnd_5421911 := by exact prefixLift 5421911
  have htrace : WordTrace (prefixWord ++ tailWord_5421911) baseStart_5421911 baseEnd_5421911 := by
    simpa [prefixWord, tailWord_5421911, baseEnd_5421911] using wordTrace_append hprefix tailTrace_5421911
  have hstable : (prefixWord ++ tailWord_5421911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421911).length < 2 ^ (prefixWord ++ tailWord_5421911).sum := by decide
  have hdescent : baseEnd_5421911 < baseStart_5421911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421978 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_5421978 : Nat := 118140960795 + 5421978 * 2 ^ 59
def prefixEnd_5421978 : Nat := 4983230072969 + 3 ^ 40 * 5421978 * 2
def baseEnd_5421978 : Nat := 928026937367830906613261

theorem tailTrace_5421978 : CollatzResearch.WordTrace tailWord_5421978 prefixEnd_5421978 928026937367830906613261 := by
  unfold tailWord_5421978
  simp only [CollatzResearch.WordTrace]
  refine ⟨49438945987776795241218647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131837189300738120643249725 49438945987776795241218647)
  ·
    refine ⟨74158418981665192861827971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49438945987776795241218647 74158418981665192861827971)
    ·
      refine ⟨111237628472497789292741957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74158418981665192861827971 111237628472497789292741957)
      ·
        refine ⟨20857055338593335492389117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111237628472497789292741957 20857055338593335492389117)
        ·
          refine ⟨7821395751972500809645919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20857055338593335492389117 7821395751972500809645919)
          ·
            refine ⟨11732093627958751214468879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821395751972500809645919 11732093627958751214468879)
            ·
              refine ⟨17598140441938126821703319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11732093627958751214468879 17598140441938126821703319)
              ·
                refine ⟨26397210662907190232554979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17598140441938126821703319 26397210662907190232554979)
                ·
                  refine ⟨39595815994360785348832469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26397210662907190232554979 39595815994360785348832469)
                  ·
                    refine ⟨928026937367830906613261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39595815994360785348832469 928026937367830906613261)
                    ·
                      rfl

theorem cell23_5421978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_5421978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421978 prefixEnd_5421978 := by exact prefixLift 5421978
  have htrace : WordTrace (prefixWord ++ tailWord_5421978) baseStart_5421978 baseEnd_5421978 := by
    simpa [prefixWord, tailWord_5421978, baseEnd_5421978] using wordTrace_append hprefix tailTrace_5421978
  have hstable : (prefixWord ++ tailWord_5421978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421978).length < 2 ^ (prefixWord ++ tailWord_5421978).sum := by decide
  have hdescent : baseEnd_5421978 < baseStart_5421978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422008 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 3, 4]
def baseStart_5422008 : Nat := 118140960795 + 5422008 * 2 ^ 59
def prefixEnd_5422008 : Nat := 4983230072969 + 3 ^ 40 * 5422008 * 2
def baseEnd_5422008 : Nat := 928032072174375867488215

theorem tailTrace_5422008 : CollatzResearch.WordTrace tailWord_5422008 prefixEnd_5422008 928032072174375867488215 := by
  unfold tailWord_5422008
  simp only [CollatzResearch.WordTrace]
  refine ⟨98878439070499248044233339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131837918760665664058977785 98878439070499248044233339)
  ·
    refine ⟨148317658605748872066350009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98878439070499248044233339 148317658605748872066350009)
    ·
      refine ⟨111238243954311654049762507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148317658605748872066350009 111238243954311654049762507)
      ·
        refine ⟨166857365931467481074643761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111238243954311654049762507 166857365931467481074643761)
        ·
          refine ⟨125143024448600610805982821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166857365931467481074643761 125143024448600610805982821)
          ·
            refine ⟨23464317084112614526121779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125143024448600610805982821 23464317084112614526121779)
            ·
              refine ⟨35196475626168921789182669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23464317084112614526121779 35196475626168921789182669)
              ·
                refine ⟨13198678359813345670943501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35196475626168921789182669 13198678359813345670943501)
                ·
                  refine ⟨4949504384930004626603813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13198678359813345670943501 4949504384930004626603813)
                  ·
                    refine ⟨928032072174375867488215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949504384930004626603813 928032072174375867488215)
                    ·
                      rfl

theorem cell23_5422008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_5422008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422008 prefixEnd_5422008 := by exact prefixLift 5422008
  have htrace : WordTrace (prefixWord ++ tailWord_5422008) baseStart_5422008 baseEnd_5422008 := by
    simpa [prefixWord, tailWord_5422008, baseEnd_5422008] using wordTrace_append hprefix tailTrace_5422008
  have hstable : (prefixWord ++ tailWord_5422008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422008).length < 2 ^ (prefixWord ++ tailWord_5422008).sum := by decide
  have hdescent : baseEnd_5422008 < baseStart_5422008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422042 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_5422042 : Nat := 118140960795 + 5422042 * 2 ^ 59
def prefixEnd_5422042 : Nat := 4983230072969 + 3 ^ 40 * 5422042 * 2
def baseEnd_5422042 : Nat := 928037891621793489813163

theorem tailTrace_5422042 : CollatzResearch.WordTrace tailWord_5422042 prefixEnd_5422042 928037891621793489813163 := by
  unfold tailWord_5422042
  simp only [CollatzResearch.WordTrace]
  refine ⟨49439529555718829973801095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131838745481916879930136253 49439529555718829973801095)
  ·
    refine ⟨74159294333578244960701643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49439529555718829973801095 74159294333578244960701643)
    ·
      refine ⟨111238941500367367441052465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74159294333578244960701643 111238941500367367441052465)
      ·
        refine ⟨83429206125275525580789349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111238941500367367441052465 83429206125275525580789349)
        ·
          refine ⟨15642976148489161046398003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83429206125275525580789349 15642976148489161046398003)
          ·
            refine ⟨23464464222733741569597005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15642976148489161046398003 23464464222733741569597005)
            ·
              refine ⟨8799174083525153088598877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23464464222733741569597005 8799174083525153088598877)
              ·
                refine ⟨3299690281321932408224579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8799174083525153088598877 3299690281321932408224579)
                ·
                  refine ⟨4949535421982898612336869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299690281321932408224579 4949535421982898612336869)
                  ·
                    refine ⟨928037891621793489813163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949535421982898612336869 928037891621793489813163)
                    ·
                      rfl

theorem cell23_5422042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_5422042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422042 prefixEnd_5422042 := by exact prefixLift 5422042
  have htrace : WordTrace (prefixWord ++ tailWord_5422042) baseStart_5422042 baseEnd_5422042 := by
    simpa [prefixWord, tailWord_5422042, baseEnd_5422042] using wordTrace_append hprefix tailTrace_5422042
  have hstable : (prefixWord ++ tailWord_5422042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422042).length < 2 ^ (prefixWord ++ tailWord_5422042).sum := by decide
  have hdescent : baseEnd_5422042 < baseStart_5422042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422092 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 2, 3, 2]
def baseStart_5422092 : Nat := 118140960795 + 5422092 * 2 ^ 59
def prefixEnd_5422092 : Nat := 4983230072969 + 3 ^ 40 * 5422092 * 2
def baseEnd_5422092 : Nat := 2784139348898105273814259

theorem tailTrace_5422092 : CollatzResearch.WordTrace tailWord_5422092 prefixEnd_5422092 2784139348898105273814259 := by
  unfold tailWord_5422092
  simp only [CollatzResearch.WordTrace]
  refine ⟨98879970936347089217262265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131839961248462785623016353 98879970936347089217262265)
  ·
    refine ⟨74159978202260316912946699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98879970936347089217262265 74159978202260316912946699)
    ·
      refine ⟨111239967303390475369420049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74159978202260316912946699 111239967303390475369420049)
      ·
        refine ⟨83429975477542856527065037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111239967303390475369420049 83429975477542856527065037)
        ·
          refine ⟨31286240804078571197649389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83429975477542856527065037 31286240804078571197649389)
          ·
            refine ⟨11732340301529464199118521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31286240804078571197649389 11732340301529464199118521)
            ·
              refine ⟨8799255226147098149338891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11732340301529464199118521 8799255226147098149338891)
              ·
                refine ⟨13198882839220647224008337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799255226147098149338891 13198882839220647224008337)
                ·
                  refine ⟨9899162129415485418006253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13198882839220647224008337 9899162129415485418006253)
                  ·
                    refine ⟨3712185798530807031752345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9899162129415485418006253 3712185798530807031752345)
                    ·
                      refine ⟨2784139348898105273814259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712185798530807031752345 2784139348898105273814259)
                      ·
                        rfl

theorem cell23_5422092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_5422092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422092 prefixEnd_5422092 := by exact prefixLift 5422092
  have htrace : WordTrace (prefixWord ++ tailWord_5422092) baseStart_5422092 baseEnd_5422092 := by
    simpa [prefixWord, tailWord_5422092, baseEnd_5422092] using wordTrace_append hprefix tailTrace_5422092
  have hstable : (prefixWord ++ tailWord_5422092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422092).length < 2 ^ (prefixWord ++ tailWord_5422092).sum := by decide
  have hdescent : baseEnd_5422092 < baseStart_5422092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422111 : List Nat := [1, 1, 2, 4, 1, 14]
def baseStart_5422111 : Nat := 118140960795 + 5422111 * 2 ^ 59
def prefixEnd_5422111 : Nat := 4983230072969 + 3 ^ 40 * 5422111 * 2
def baseEnd_5422111 : Nat := 11457403724405517281797

theorem tailTrace_5422111 : CollatzResearch.WordTrace tailWord_5422111 prefixEnd_5422111 11457403724405517281797 := by
  unfold tailWord_5422111
  simp only [CollatzResearch.WordTrace]
  refine ⟨197760634859625344679466187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131840423239750229786310791 197760634859625344679466187)
  ·
    refine ⟨296640952289438017019199281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197760634859625344679466187 296640952289438017019199281)
    ·
      refine ⟨222480714217078512764399461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296640952289438017019199281 222480714217078512764399461)
      ·
        refine ⟨41715133915702221143324899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222480714217078512764399461 41715133915702221143324899)
        ·
          refine ⟨62572700873553331714987349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41715133915702221143324899 62572700873553331714987349)
          ·
            refine ⟨11457403724405517281797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 62572700873553331714987349 11457403724405517281797)
            ·
              rfl

theorem cell23_5422111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 14].length) (baseStart_5422111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422111 prefixEnd_5422111 := by exact prefixLift 5422111
  have htrace : WordTrace (prefixWord ++ tailWord_5422111) baseStart_5422111 baseEnd_5422111 := by
    simpa [prefixWord, tailWord_5422111, baseEnd_5422111] using wordTrace_append hprefix tailTrace_5422111
  have hstable : (prefixWord ++ tailWord_5422111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422111).length < 2 ^ (prefixWord ++ tailWord_5422111).sum := by decide
  have hdescent : baseEnd_5422111 < baseStart_5422111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422115 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 2, 4]
def baseStart_5422115 : Nat := 118140960795 + 5422115 * 2 ^ 59
def prefixEnd_5422115 : Nat := 4983230072969 + 3 ^ 40 * 5422115 * 2
def baseEnd_5422115 : Nat := 928050386317719561275551

theorem tailTrace_5422115 : CollatzResearch.WordTrace tailWord_5422115 prefixEnd_5422115 928050386317719561275551 := by
  unfold tailWord_5422115
  simp only [CollatzResearch.WordTrace]
  refine ⟨197760780751610853362611799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131840520501073902241741199 197760780751610853362611799)
  ·
    refine ⟨296641171127416280043917699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197760780751610853362611799 296641171127416280043917699)
    ·
      refine ⟨444961756691124420065876549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296641171127416280043917699 444961756691124420065876549)
      ·
        refine ⟨83430329379585828762351853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 444961756691124420065876549 83430329379585828762351853)
        ·
          refine ⟨31286373517344685785881945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83430329379585828762351853 31286373517344685785881945)
          ·
            refine ⟨23464780138008514339411459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31286373517344685785881945 23464780138008514339411459)
            ·
              refine ⟨35197170207012771509117189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23464780138008514339411459 35197170207012771509117189)
              ·
                refine ⟨6599469413814894657959473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35197170207012771509117189 6599469413814894657959473)
                ·
                  refine ⟨4949602060361170993469605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6599469413814894657959473 4949602060361170993469605)
                  ·
                    refine ⟨928050386317719561275551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949602060361170993469605 928050386317719561275551)
                    ·
                      rfl

theorem cell23_5422115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 4].length) (baseStart_5422115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422115 prefixEnd_5422115 := by exact prefixLift 5422115
  have htrace : WordTrace (prefixWord ++ tailWord_5422115) baseStart_5422115 baseEnd_5422115 := by
    simpa [prefixWord, tailWord_5422115, baseEnd_5422115] using wordTrace_append hprefix tailTrace_5422115
  have hstable : (prefixWord ++ tailWord_5422115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422115).length < 2 ^ (prefixWord ++ tailWord_5422115).sum := by decide
  have hdescent : baseEnd_5422115 < baseStart_5422115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422116 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_5422116 : Nat := 118140960795 + 5422116 * 2 ^ 59
def prefixEnd_5422116 : Nat := 4983230072969 + 3 ^ 40 * 5422116 * 2
def baseEnd_5422116 : Nat := 2784151672433813179914149

theorem tailTrace_5422116 : CollatzResearch.WordTrace tailWord_5422116 prefixEnd_5422116 2784151672433813179914149 := by
  unfold tailWord_5422116
  simp only [CollatzResearch.WordTrace]
  refine ⟨98880408612303615266699101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131840544816404820355598801 98880408612303615266699101)
  ·
    refine ⟨37080153229613855725012163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98880408612303615266699101 37080153229613855725012163)
    ·
      refine ⟨55620229844420783587518245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37080153229613855725012163 55620229844420783587518245)
      ·
        refine ⟨10428793095828896922659671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55620229844420783587518245 10428793095828896922659671)
        ·
          refine ⟨15643189643743345383989507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428793095828896922659671 15643189643743345383989507)
          ·
            refine ⟨23464784465615018075984261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15643189643743345383989507 23464784465615018075984261)
            ·
              refine ⟨4399647087302815889247049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23464784465615018075984261 4399647087302815889247049)
              ·
                refine ⟨3299735315477111916935287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399647087302815889247049 3299735315477111916935287)
                ·
                  refine ⟨4949602973215667875402931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299735315477111916935287 4949602973215667875402931)
                  ·
                    refine ⟨7424404459823501813104397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4949602973215667875402931 7424404459823501813104397)
                    ·
                      refine ⟨2784151672433813179914149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7424404459823501813104397 2784151672433813179914149)
                      ·
                        rfl

theorem cell23_5422116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_5422116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422116 prefixEnd_5422116 := by exact prefixLift 5422116
  have htrace : WordTrace (prefixWord ++ tailWord_5422116) baseStart_5422116 baseEnd_5422116 := by
    simpa [prefixWord, tailWord_5422116, baseEnd_5422116] using wordTrace_append hprefix tailTrace_5422116
  have hstable : (prefixWord ++ tailWord_5422116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422116).length < 2 ^ (prefixWord ++ tailWord_5422116).sum := by decide
  have hdescent : baseEnd_5422116 < baseStart_5422116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422132 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_5422132 : Nat := 118140960795 + 5422132 * 2 ^ 59
def prefixEnd_5422132 : Nat := 4983230072969 + 3 ^ 40 * 5422132 * 2
def baseEnd_5422132 : Nat := 928053296041428372438025

theorem tailTrace_5422132 : CollatzResearch.WordTrace tailWord_5422132 prefixEnd_5422132 928053296041428372438025 := by
  unfold tailWord_5422132
  simp only [CollatzResearch.WordTrace]
  refine ⟨98880700396274632632990325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131840933861699510177320433 98880700396274632632990325)
  ·
    refine ⟨9270065662150746809342843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98880700396274632632990325 9270065662150746809342843)
    ·
      refine ⟨13905098493226120214014265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9270065662150746809342843 13905098493226120214014265)
      ·
        refine ⟨10428823869919590160510699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13905098493226120214014265 10428823869919590160510699)
        ·
          refine ⟨15643235804879385240766049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428823869919590160510699 15643235804879385240766049)
          ·
            refine ⟨11732426853659538930574537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15643235804879385240766049 11732426853659538930574537)
            ·
              refine ⟨8799320140244654197930903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11732426853659538930574537 8799320140244654197930903)
              ·
                refine ⟨13198980210366981296896355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799320140244654197930903 13198980210366981296896355)
                ·
                  refine ⟨19798470315550471945344533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13198980210366981296896355 19798470315550471945344533)
                  ·
                    refine ⟨928053296041428372438025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19798470315550471945344533 928053296041428372438025)
                    ·
                      rfl

theorem cell23_5422132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_5422132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422132 prefixEnd_5422132 := by exact prefixLift 5422132
  have htrace : WordTrace (prefixWord ++ tailWord_5422132) baseStart_5422132 baseEnd_5422132 := by
    simpa [prefixWord, tailWord_5422132, baseEnd_5422132] using wordTrace_append hprefix tailTrace_5422132
  have hstable : (prefixWord ++ tailWord_5422132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422132).length < 2 ^ (prefixWord ++ tailWord_5422132).sum := by decide
  have hdescent : baseEnd_5422132 < baseStart_5422132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422142 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5422142 : Nat := 118140960795 + 5422142 * 2 ^ 59
def prefixEnd_5422142 : Nat := 4983230072969 + 3 ^ 40 * 5422142 * 2
def baseEnd_5422142 : Nat := 2784165022930830078189029

theorem tailTrace_5422142 : CollatzResearch.WordTrace tailWord_5422142 prefixEnd_5422142 2784165022930830078189029 := by
  unfold tailWord_5422142
  simp only [CollatzResearch.WordTrace]
  refine ⟨24720220690314129621730585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131841177015008691315896453 24720220690314129621730585)
  ·
    refine ⟨18540165517735597216297939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24720220690314129621730585 18540165517735597216297939)
    ·
      refine ⟨27810248276603395824446909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18540165517735597216297939 27810248276603395824446909)
      ·
        refine ⟨10428843103726273434167591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27810248276603395824446909 10428843103726273434167591)
        ·
          refine ⟨15643264655589410151251387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428843103726273434167591 15643264655589410151251387)
          ·
            refine ⟨23464896983384115226877081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15643264655589410151251387 23464896983384115226877081)
            ·
              refine ⟨17598672737538086420157811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23464896983384115226877081 17598672737538086420157811)
              ·
                refine ⟨26398009106307129630236717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17598672737538086420157811 26398009106307129630236717)
                ·
                  refine ⟨9899253414865173611338769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26398009106307129630236717 9899253414865173611338769)
                  ·
                    refine ⟨7424440061148880208504077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9899253414865173611338769 7424440061148880208504077)
                    ·
                      refine ⟨2784165022930830078189029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7424440061148880208504077 2784165022930830078189029)
                      ·
                        rfl

theorem cell23_5422142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5422142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422142 prefixEnd_5422142 := by exact prefixLift 5422142
  have htrace : WordTrace (prefixWord ++ tailWord_5422142) baseStart_5422142 baseEnd_5422142 := by
    simpa [prefixWord, tailWord_5422142, baseEnd_5422142] using wordTrace_append hprefix tailTrace_5422142
  have hstable : (prefixWord ++ tailWord_5422142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422142).length < 2 ^ (prefixWord ++ tailWord_5422142).sum := by decide
  have hdescent : baseEnd_5422142 < baseStart_5422142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422172 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_5422172 : Nat := 118140960795 + 5422172 * 2 ^ 59
def prefixEnd_5422172 : Nat := 4983230072969 + 3 ^ 40 * 5422172 * 2
def baseEnd_5422172 : Nat := 2784180427350464960813891

theorem tailTrace_5422172 : CollatzResearch.WordTrace tailWord_5422172 prefixEnd_5422172 2784180427350464960813891 := by
  unfold tailWord_5422172
  simp only [CollatzResearch.WordTrace]
  refine ⟨98881429856202176048718385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131841906474936234731624513 98881429856202176048718385)
  ·
    refine ⟨74161072392151632036538789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98881429856202176048718385 74161072392151632036538789)
    ·
      refine ⟨13905201073528431006851023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74161072392151632036538789 13905201073528431006851023)
      ·
        refine ⟨20857801610292646510276535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905201073528431006851023 20857801610292646510276535)
        ·
          refine ⟨31286702415438969765414803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20857801610292646510276535 31286702415438969765414803)
          ·
            refine ⟨46930053623158454648122205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31286702415438969765414803 46930053623158454648122205)
            ·
              refine ⟨17598770108684420493045827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46930053623158454648122205 17598770108684420493045827)
              ·
                refine ⟨26398155163026630739568741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17598770108684420493045827 26398155163026630739568741)
                ·
                  refine ⟨4949654093067493263669139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26398155163026630739568741 4949654093067493263669139)
                  ·
                    refine ⟨7424481139601239895503709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4949654093067493263669139 7424481139601239895503709)
                    ·
                      refine ⟨2784180427350464960813891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7424481139601239895503709 2784180427350464960813891)
                      ·
                        rfl

theorem cell23_5422172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_5422172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422172 prefixEnd_5422172 := by exact prefixLift 5422172
  have htrace : WordTrace (prefixWord ++ tailWord_5422172) baseStart_5422172 baseEnd_5422172 := by
    simpa [prefixWord, tailWord_5422172, baseEnd_5422172] using wordTrace_append hprefix tailTrace_5422172
  have hstable : (prefixWord ++ tailWord_5422172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422172).length < 2 ^ (prefixWord ++ tailWord_5422172).sum := by decide
  have hdescent : baseEnd_5422172 < baseStart_5422172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422188 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_5422188 : Nat := 118140960795 + 5422188 * 2 ^ 59
def prefixEnd_5422188 : Nat := 4983230072969 + 3 ^ 40 * 5422188 * 2
def baseEnd_5422188 : Nat := 928062881013645632737939

theorem tailTrace_5422188 : CollatzResearch.WordTrace tailWord_5422188 prefixEnd_5422188 928062881013645632737939 := by
  unfold tailWord_5422188
  simp only [CollatzResearch.WordTrace]
  refine ⟨98881721640173193415009609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131842295520230924553346145 98881721640173193415009609)
  ·
    refine ⟨74161291230129895061257207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98881721640173193415009609 74161291230129895061257207)
    ·
      refine ⟨111241936845194842591885811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74161291230129895061257207 111241936845194842591885811)
      ·
        refine ⟨166862905267792263887828717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111241936845194842591885811 166862905267792263887828717)
        ·
          refine ⟨62573589475422098957935769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166862905267792263887828717 62573589475422098957935769)
          ·
            refine ⟨46930192106566574218451827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62573589475422098957935769 46930192106566574218451827)
            ·
              refine ⟨70395288159849861327677741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46930192106566574218451827 70395288159849861327677741)
              ·
                refine ⟨26398233059943697997879153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70395288159849861327677741 26398233059943697997879153)
                ·
                  refine ⟨19798674794957773498409365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26398233059943697997879153 19798674794957773498409365)
                  ·
                    refine ⟨928062881013645632737939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19798674794957773498409365 928062881013645632737939)
                    ·
                      rfl

theorem cell23_5422188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_5422188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422188 prefixEnd_5422188 := by exact prefixLift 5422188
  have htrace : WordTrace (prefixWord ++ tailWord_5422188) baseStart_5422188 baseEnd_5422188 := by
    simpa [prefixWord, tailWord_5422188, baseEnd_5422188] using wordTrace_append hprefix tailTrace_5422188
  have hstable : (prefixWord ++ tailWord_5422188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422188).length < 2 ^ (prefixWord ++ tailWord_5422188).sum := by decide
  have hdescent : baseEnd_5422188 < baseStart_5422188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422208 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_5422208 : Nat := 118140960795 + 5422208 * 2 ^ 59
def prefixEnd_5422208 : Nat := 4983230072969 + 3 ^ 40 * 5422208 * 2
def baseEnd_5422208 : Nat := 2784198912654026819963725

theorem tailTrace_5422208 : CollatzResearch.WordTrace tailWord_5422208 prefixEnd_5422208 2784198912654026819963725 := by
  unfold tailWord_5422208
  simp only [CollatzResearch.WordTrace]
  refine ⟨98882086370136965122873639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131842781826849286830498185 98882086370136965122873639)
  ·
    refine ⟨148323129555205447684310459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98882086370136965122873639 148323129555205447684310459)
    ·
      refine ⟨222484694332808171526465689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148323129555205447684310459 222484694332808171526465689)
      ·
        refine ⟨166863520749606128644849267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222484694332808171526465689 166863520749606128644849267)
        ·
          refine ⟨250295281124409192967273901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166863520749606128644849267 250295281124409192967273901)
          ·
            refine ⟨93860730421653447362727713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250295281124409192967273901 93860730421653447362727713)
            ·
              refine ⟨70395547816240085522045785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93860730421653447362727713 70395547816240085522045785)
              ·
                refine ⟨52796660862180064141534339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70395547816240085522045785 52796660862180064141534339)
                ·
                  refine ⟨79194991293270096212301509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52796660862180064141534339 79194991293270096212301509)
                  ·
                    refine ⟨14849060867488143039806533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79194991293270096212301509 14849060867488143039806533)
                    ·
                      refine ⟨2784198912654026819963725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14849060867488143039806533 2784198912654026819963725)
                      ·
                        rfl

theorem cell23_5422208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_5422208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422208 prefixEnd_5422208 := by exact prefixLift 5422208
  have htrace : WordTrace (prefixWord ++ tailWord_5422208) baseStart_5422208 baseEnd_5422208 := by
    simpa [prefixWord, tailWord_5422208, baseEnd_5422208] using wordTrace_append hprefix tailTrace_5422208
  have hstable : (prefixWord ++ tailWord_5422208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422208).length < 2 ^ (prefixWord ++ tailWord_5422208).sum := by decide
  have hdescent : baseEnd_5422208 < baseStart_5422208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422265 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_5422265 : Nat := 118140960795 + 5422265 * 2 ^ 59
def prefixEnd_5422265 : Nat := 4983230072969 + 3 ^ 40 * 5422265 * 2
def baseEnd_5422265 : Nat := 928076060350444365650321

theorem tailTrace_5422265 : CollatzResearch.WordTrace tailWord_5422265 prefixEnd_5422265 928076060350444365650321 := by
  unfold tailWord_5422265
  simp only [CollatzResearch.WordTrace]
  refine ⟨197766251701067428980572249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131844167800711619320381499 197766251701067428980572249)
  ·
    refine ⟨148324688775800571735429187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197766251701067428980572249 148324688775800571735429187)
    ·
      refine ⟨222487033163700857603143781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148324688775800571735429187 222487033163700857603143781)
      ·
        refine ⟨41716318718193910800589459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222487033163700857603143781 41716318718193910800589459)
        ·
          refine ⟨62574478077290866200884189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41716318718193910800589459 62574478077290866200884189)
          ·
            refine ⟨23465429278984074825331571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62574478077290866200884189 23465429278984074825331571)
            ·
              refine ⟨35198143918476112237997357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23465429278984074825331571 35198143918476112237997357)
              ·
                refine ⟨13199303969428542089249009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35198143918476112237997357 13199303969428542089249009)
                ·
                  refine ⟨9899477977071406566936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13199303969428542089249009 9899477977071406566936757)
                  ·
                    refine ⟨928076060350444365650321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9899477977071406566936757 928076060350444365650321)
                    ·
                      rfl

theorem cell23_5422265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_5422265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422265 prefixEnd_5422265 := by exact prefixLift 5422265
  have htrace : WordTrace (prefixWord ++ tailWord_5422265) baseStart_5422265 baseEnd_5422265 := by
    simpa [prefixWord, tailWord_5422265, baseEnd_5422265] using wordTrace_append hprefix tailTrace_5422265
  have hstable : (prefixWord ++ tailWord_5422265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422265).length < 2 ^ (prefixWord ++ tailWord_5422265).sum := by decide
  have hdescent : baseEnd_5422265 < baseStart_5422265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422286 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_5422286 : Nat := 118140960795 + 5422286 * 2 ^ 59
def prefixEnd_5422286 : Nat := 4983230072969 + 3 ^ 40 * 5422286 * 2
def baseEnd_5422286 : Nat := 309359884905008612754263

theorem tailTrace_5422286 : CollatzResearch.WordTrace tailWord_5422286 prefixEnd_5422286 309359884905008612754263 := by
  unfold tailWord_5422286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24720877204248918695885839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131844678422660899711391141 24720877204248918695885839)
  ·
    refine ⟨37081315806373378043828759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24720877204248918695885839 37081315806373378043828759)
    ·
      refine ⟨55621973709560067065743139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37081315806373378043828759 55621973709560067065743139)
      ·
        refine ⟨83432960564340100598614709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55621973709560067065743139 83432960564340100598614709)
        ·
          refine ⟨7821840052906884431120129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83432960564340100598614709 7821840052906884431120129)
          ·
            refine ⟨5866380039680163323340097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7821840052906884431120129 5866380039680163323340097)
            ·
              refine ⟨4399785029760122492505073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5866380039680163323340097 4399785029760122492505073)
              ·
                refine ⟨3299838772320091869378805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399785029760122492505073 3299838772320091869378805)
                ·
                  refine ⟨309359884905008612754263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3299838772320091869378805 309359884905008612754263)
                  ·
                    rfl

theorem cell23_5422286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_5422286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422286 prefixEnd_5422286 := by exact prefixLift 5422286
  have htrace : WordTrace (prefixWord ++ tailWord_5422286) baseStart_5422286 baseEnd_5422286 := by
    simpa [prefixWord, tailWord_5422286, baseEnd_5422286] using wordTrace_append hprefix tailTrace_5422286
  have hstable : (prefixWord ++ tailWord_5422286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422286).length < 2 ^ (prefixWord ++ tailWord_5422286).sum := by decide
  have hdescent : baseEnd_5422286 < baseStart_5422286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422312 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 3, 4]
def baseStart_5422312 : Nat := 118140960795 + 5422312 * 2 ^ 59
def prefixEnd_5422312 : Nat := 4983230072969 + 3 ^ 40 * 5422312 * 2
def baseEnd_5422312 : Nat := 928084104880698137687749

theorem tailTrace_5422312 : CollatzResearch.WordTrace tailWord_5422312 prefixEnd_5422312 928084104880698137687749 := by
  unfold tailWord_5422312
  simp only [CollatzResearch.WordTrace]
  refine ⟨98883982965948578003766595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131845310621264770671688793 98883982965948578003766595)
  ·
    refine ⟨148325974448922867005649893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98883982965948578003766595 148325974448922867005649893)
    ·
      refine ⟨27811120209173037563559355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148325974448922867005649893 27811120209173037563559355)
      ·
        refine ⟨41716680313759556345339033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27811120209173037563559355 41716680313759556345339033)
        ·
          refine ⟨31287510235319667259004275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41716680313759556345339033 31287510235319667259004275)
          ·
            refine ⟨46931265352979500888506413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31287510235319667259004275 46931265352979500888506413)
            ·
              refine ⟨17599224507367312833189905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46931265352979500888506413 17599224507367312833189905)
              ·
                refine ⟨13199418380525484624892429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17599224507367312833189905 13199418380525484624892429)
                ·
                  refine ⟨4949781892697056734334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13199418380525484624892429 4949781892697056734334661)
                  ·
                    refine ⟨928084104880698137687749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949781892697056734334661 928084104880698137687749)
                    ·
                      rfl

theorem cell23_5422312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_5422312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422312 prefixEnd_5422312 := by exact prefixLift 5422312
  have htrace : WordTrace (prefixWord ++ tailWord_5422312) baseStart_5422312 baseEnd_5422312 := by
    simpa [prefixWord, tailWord_5422312, baseEnd_5422312] using wordTrace_append hprefix tailTrace_5422312
  have hstable : (prefixWord ++ tailWord_5422312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422312).length < 2 ^ (prefixWord ++ tailWord_5422312).sum := by decide
  have hdescent : baseEnd_5422312 < baseStart_5422312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422319 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 4]
def baseStart_5422319 : Nat := 118140960795 + 5422319 * 2 ^ 59
def prefixEnd_5422319 : Nat := 4983230072969 + 3 ^ 40 * 5422319 * 2
def baseEnd_5422319 : Nat := 2784255909006675885675715

theorem tailTrace_5422319 : CollatzResearch.WordTrace tailWord_5422319 prefixEnd_5422319 2784255909006675885675715 := by
  unfold tailWord_5422319
  simp only [CollatzResearch.WordTrace]
  refine ⟨197768221242871796203038011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131845480828581197468692007 197768221242871796203038011)
  ·
    refine ⟨296652331864307694304557017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197768221242871796203038011 296652331864307694304557017)
    ·
      refine ⟨222489248898230770728417763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296652331864307694304557017 222489248898230770728417763)
      ·
        refine ⟨333733873347346156092626645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222489248898230770728417763 333733873347346156092626645)
        ·
          refine ⟨7821887656578425533420937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 333733873347346156092626645 7821887656578425533420937)
          ·
            refine ⟨5866415742433819150065703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7821887656578425533420937 5866415742433819150065703)
            ·
              refine ⟨8799623613650728725098555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866415742433819150065703 8799623613650728725098555)
              ·
                refine ⟨13199435420476093087647833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799623613650728725098555 13199435420476093087647833)
                ·
                  refine ⟨9899576565357069815735875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13199435420476093087647833 9899576565357069815735875)
                  ·
                    refine ⟨14849364848035604723603813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9899576565357069815735875 14849364848035604723603813)
                    ·
                      refine ⟨2784255909006675885675715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14849364848035604723603813 2784255909006675885675715)
                      ·
                        rfl

theorem cell23_5422319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_5422319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422319 prefixEnd_5422319 := by exact prefixLift 5422319
  have htrace : WordTrace (prefixWord ++ tailWord_5422319) baseStart_5422319 baseEnd_5422319 := by
    simpa [prefixWord, tailWord_5422319, baseEnd_5422319] using wordTrace_append hprefix tailTrace_5422319
  have hstable : (prefixWord ++ tailWord_5422319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422319).length < 2 ^ (prefixWord ++ tailWord_5422319).sum := by decide
  have hdescent : baseEnd_5422319 < baseStart_5422319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422329 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 1, 4]
def baseStart_5422329 : Nat := 118140960795 + 5422329 * 2 ^ 59
def prefixEnd_5422329 : Nat := 4983230072969 + 3 ^ 40 * 5422329 * 2
def baseEnd_5422329 : Nat := 928087014604406948850223

theorem tailTrace_5422329 : CollatzResearch.WordTrace tailWord_5422329 prefixEnd_5422329 928087014604406948850223 := by
  unfold tailWord_5422329
  simp only [CollatzResearch.WordTrace]
  refine ⟨197768585972835567910902041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131845723981890378607268027 197768585972835567910902041)
  ·
    refine ⟨148326439479626675933176531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197768585972835567910902041 148326439479626675933176531)
    ·
      refine ⟨222489659219440013899764797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148326439479626675933176531 222489659219440013899764797)
      ·
        refine ⟨83433622207290005212411799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222489659219440013899764797 83433622207290005212411799)
        ·
          refine ⟨125150433310935007818617699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83433622207290005212411799 125150433310935007818617699)
          ·
            refine ⟨187725649966402511727926549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125150433310935007818617699 187725649966402511727926549)
            ·
              refine ⟨8799639842175117737246557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187725649966402511727926549 8799639842175117737246557)
              ·
                refine ⟨3299864940815669151467459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8799639842175117737246557 3299864940815669151467459)
                ·
                  refine ⟨4949797411223503727201189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299864940815669151467459 4949797411223503727201189)
                  ·
                    refine ⟨928087014604406948850223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949797411223503727201189 928087014604406948850223)
                    ·
                      rfl

theorem cell23_5422329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 4].length) (baseStart_5422329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422329 prefixEnd_5422329 := by exact prefixLift 5422329
  have htrace : WordTrace (prefixWord ++ tailWord_5422329) baseStart_5422329 baseEnd_5422329 := by
    simpa [prefixWord, tailWord_5422329, baseEnd_5422329] using wordTrace_append hprefix tailTrace_5422329
  have hstable : (prefixWord ++ tailWord_5422329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422329).length < 2 ^ (prefixWord ++ tailWord_5422329).sum := by decide
  have hdescent : baseEnd_5422329 < baseStart_5422329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422395 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 3]
def baseStart_5422395 : Nat := 118140960795 + 5422395 * 2 ^ 59
def prefixEnd_5422395 : Nat := 4983230072969 + 3 ^ 40 * 5422395 * 2
def baseEnd_5422395 : Nat := 2784294933536417588325365

theorem tailTrace_5422395 : CollatzResearch.WordTrace tailWord_5422395 prefixEnd_5422395 2784294933536417588325365 := by
  unfold tailWord_5422395
  simp only [CollatzResearch.WordTrace]
  refine ⟨197770993190596461182804639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131847328793730974121869759 197770993190596461182804639)
  ·
    refine ⟨296656489785894691774206959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197770993190596461182804639 296656489785894691774206959)
    ·
      refine ⟨444984734678842037661310439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296656489785894691774206959 444984734678842037661310439)
      ·
        refine ⟨667477102018263056491965659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444984734678842037661310439 667477102018263056491965659)
        ·
          refine ⟨1001215653027394584737948489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667477102018263056491965659 1001215653027394584737948489)
          ·
            refine ⟨750911739770545938553461367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001215653027394584737948489 750911739770545938553461367)
            ·
              refine ⟨1126367609655818907830192051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750911739770545938553461367 1126367609655818907830192051)
              ·
                refine ⟨1689551414483728361745288077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126367609655818907830192051 1689551414483728361745288077)
                ·
                  refine ⟨633581780431398135654483029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1689551414483728361745288077 633581780431398135654483029)
                  ·
                    refine ⟨7424786489430446902200973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 633581780431398135654483029 7424786489430446902200973)
                    ·
                      refine ⟨2784294933536417588325365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7424786489430446902200973 2784294933536417588325365)
                      ·
                        rfl

theorem cell23_5422395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 3].length) (baseStart_5422395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422395 prefixEnd_5422395 := by exact prefixLift 5422395
  have htrace : WordTrace (prefixWord ++ tailWord_5422395) baseStart_5422395 baseEnd_5422395 := by
    simpa [prefixWord, tailWord_5422395, baseEnd_5422395] using wordTrace_append hprefix tailTrace_5422395
  have hstable : (prefixWord ++ tailWord_5422395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422395).length < 2 ^ (prefixWord ++ tailWord_5422395).sum := by decide
  have hdescent : baseEnd_5422395 < baseStart_5422395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422412 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5422412 : Nat := 118140960795 + 5422412 * 2 ^ 59
def prefixEnd_5422412 : Nat := 4983230072969 + 3 ^ 40 * 5422412 * 2
def baseEnd_5422412 : Nat := 2784303662707544021812787

theorem tailTrace_5422412 : CollatzResearch.WordTrace tailWord_5422412 prefixEnd_5422412 2784303662707544021812787 := by
  unfold tailWord_5422412
  simp only [CollatzResearch.WordTrace]
  refine ⟨98885806615767436543086745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131847742154356582057448993 98885806615767436543086745)
  ·
    refine ⟨74164354961825577407315059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98885806615767436543086745 74164354961825577407315059)
    ·
      refine ⟨111246532442738366110972589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74164354961825577407315059 111246532442738366110972589)
      ·
        refine ⟨41717449666026887291614721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111246532442738366110972589 41717449666026887291614721)
        ·
          refine ⟨31288087249520165468711041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41717449666026887291614721 31288087249520165468711041)
          ·
            refine ⟨23466065437140124101533281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31288087249520165468711041 23466065437140124101533281)
            ·
              refine ⟨17599549077855093076149961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23466065437140124101533281 17599549077855093076149961)
              ·
                refine ⟨13199661808391319807112471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17599549077855093076149961 13199661808391319807112471)
                ·
                  refine ⟨19799492712586979710668707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13199661808391319807112471 19799492712586979710668707)
                  ·
                    refine ⟨29699239068880469566003061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19799492712586979710668707 29699239068880469566003061)
                    ·
                      refine ⟨2784303662707544021812787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29699239068880469566003061 2784303662707544021812787)
                      ·
                        rfl

theorem cell23_5422412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5422412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422412 prefixEnd_5422412 := by exact prefixLift 5422412
  have htrace : WordTrace (prefixWord ++ tailWord_5422412) baseStart_5422412 baseEnd_5422412 := by
    simpa [prefixWord, tailWord_5422412, baseEnd_5422412] using wordTrace_append hprefix tailTrace_5422412
  have hstable : (prefixWord ++ tailWord_5422412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422412).length < 2 ^ (prefixWord ++ tailWord_5422412).sum := by decide
  have hdescent : baseEnd_5422412 < baseStart_5422412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422439 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_5422439 : Nat := 118140960795 + 5422439 * 2 ^ 59
def prefixEnd_5422439 : Nat := 4983230072969 + 3 ^ 40 * 5422439 * 2
def baseEnd_5422439 : Nat := 2784317526685215416175163

theorem tailTrace_5422439 : CollatzResearch.WordTrace tailWord_5422439 prefixEnd_5422439 2784317526685215416175163 := by
  unfold tailWord_5422439
  simp only [CollatzResearch.WordTrace]
  refine ⟨197772598002437056697406371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131848398668291371131604247 197772598002437056697406371)
  ·
    refine ⟨296658897003655585046109557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197772598002437056697406371 296658897003655585046109557)
    ·
      refine ⟨27811771594092711098072771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296658897003655585046109557 27811771594092711098072771)
      ·
        refine ⟨41717657391139066647109157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27811771594092711098072771 41717657391139066647109157)
        ·
          refine ⟨7822060760838574996332967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41717657391139066647109157 7822060760838574996332967)
          ·
            refine ⟨11733091141257862494499451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7822060760838574996332967 11733091141257862494499451)
            ·
              refine ⟨17599636711886793741749177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11733091141257862494499451 17599636711886793741749177)
              ·
                refine ⟨13199727533915095306311883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17599636711886793741749177 13199727533915095306311883)
                ·
                  refine ⟨19799591300872642959467825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13199727533915095306311883 19799591300872642959467825)
                  ·
                    refine ⟨14849693475654482219600869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19799591300872642959467825 14849693475654482219600869)
                    ·
                      refine ⟨2784317526685215416175163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14849693475654482219600869 2784317526685215416175163)
                      ·
                        rfl

theorem cell23_5422439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_5422439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422439 prefixEnd_5422439 := by exact prefixLift 5422439
  have htrace : WordTrace (prefixWord ++ tailWord_5422439) baseStart_5422439 baseEnd_5422439 := by
    simpa [prefixWord, tailWord_5422439, baseEnd_5422439] using wordTrace_append hprefix tailTrace_5422439
  have hstable : (prefixWord ++ tailWord_5422439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422439).length < 2 ^ (prefixWord ++ tailWord_5422439).sum := by decide
  have hdescent : baseEnd_5422439 < baseStart_5422439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422466 : List Nat := [3, 4, 2, 1, 1, 3, 1, 8]
def baseStart_5422466 : Nat := 118140960795 + 5422466 * 2 ^ 59
def prefixEnd_5422466 : Nat := 4983230072969 + 3 ^ 40 * 5422466 * 2
def baseEnd_5422466 : Nat := 103123384839366178168057

theorem tailTrace_5422466 : CollatzResearch.WordTrace tailWord_5422466 prefixEnd_5422466 103123384839366178168057 := by
  unfold tailWord_5422466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49443395693334810077159813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131849055182226160205759501 49443395693334810077159813)
  ·
    refine ⟨9270636692500276889467465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49443395693334810077159813 9270636692500276889467465)
    ·
      refine ⟨6952977519375207667100599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9270636692500276889467465 6952977519375207667100599)
      ·
        refine ⟨10429466279062811500650899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952977519375207667100599 10429466279062811500650899)
        ·
          refine ⟨15644199418594217250976349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10429466279062811500650899 15644199418594217250976349)
          ·
            refine ⟨5866574781972831469116131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15644199418594217250976349 5866574781972831469116131)
            ·
              refine ⟨8799862172959247203674197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866574781972831469116131 8799862172959247203674197)
              ·
                refine ⟨103123384839366178168057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8799862172959247203674197 103123384839366178168057)
                ·
                  rfl

theorem cell23_5422466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_5422466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422466 prefixEnd_5422466 := by exact prefixLift 5422466
  have htrace : WordTrace (prefixWord ++ tailWord_5422466) baseStart_5422466 baseEnd_5422466 := by
    simpa [prefixWord, tailWord_5422466, baseEnd_5422466] using wordTrace_append hprefix tailTrace_5422466
  have hstable : (prefixWord ++ tailWord_5422466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422466).length < 2 ^ (prefixWord ++ tailWord_5422466).sum := by decide
  have hdescent : baseEnd_5422466 < baseStart_5422466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422469 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 3, 3, 2]
def baseStart_5422469 : Nat := 118140960795 + 5422469 * 2 ^ 59
def prefixEnd_5422469 : Nat := 4983230072969 + 3 ^ 40 * 5422469 * 2
def baseEnd_5422469 : Nat := 2784332931104850298800025

theorem tailTrace_5422469 : CollatzResearch.WordTrace tailWord_5422469 prefixEnd_5422469 2784332931104850298800025 := by
  unfold tailWord_5422469
  simp only [CollatzResearch.WordTrace]
  refine ⟨197773692192328371820998461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131849128128218914547332307 197773692192328371820998461)
  ·
    refine ⟨74165134572123139432874423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197773692192328371820998461 74165134572123139432874423)
    ·
      refine ⟨111247701858184709149311635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74165134572123139432874423 111247701858184709149311635)
      ·
        refine ⟨166871552787277063723967453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111247701858184709149311635 166871552787277063723967453)
        ·
          refine ⟨62576832295228898896487795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166871552787277063723967453 62576832295228898896487795)
          ·
            refine ⟨93865248442843348344731693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62576832295228898896487795 93865248442843348344731693)
            ·
              refine ⟨35199468166066255629274385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93865248442843348344731693 35199468166066255629274385)
              ·
                refine ⟨26399601124549691721955789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35199468166066255629274385 26399601124549691721955789)
                ·
                  refine ⟨9899850421706134395733421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26399601124549691721955789 9899850421706134395733421)
                  ·
                    refine ⟨3712443908139800398400033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9899850421706134395733421 3712443908139800398400033)
                    ·
                      refine ⟨2784332931104850298800025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712443908139800398400033 2784332931104850298800025)
                      ·
                        rfl

theorem cell23_5422469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_5422469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422469 prefixEnd_5422469 := by exact prefixLift 5422469
  have htrace : WordTrace (prefixWord ++ tailWord_5422469) baseStart_5422469 baseEnd_5422469 := by
    simpa [prefixWord, tailWord_5422469, baseEnd_5422469] using wordTrace_append hprefix tailTrace_5422469
  have hstable : (prefixWord ++ tailWord_5422469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422469).length < 2 ^ (prefixWord ++ tailWord_5422469).sum := by decide
  have hdescent : baseEnd_5422469 < baseStart_5422469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422499 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 1, 4, 2]
def baseStart_5422499 : Nat := 118140960795 + 5422499 * 2 ^ 59
def prefixEnd_5422499 : Nat := 4983230072969 + 3 ^ 40 * 5422499 * 2
def baseEnd_5422499 : Nat := 2784348335524485181424887

theorem tailTrace_5422499 : CollatzResearch.WordTrace tailWord_5422499 prefixEnd_5422499 2784348335524485181424887 := by
  unfold tailWord_5422499
  simp only [CollatzResearch.WordTrace]
  refine ⟨197774786382219686944590551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131849857588146457963060367 197774786382219686944590551)
  ·
    refine ⟨296662179573329530416885827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197774786382219686944590551 296662179573329530416885827)
    ·
      refine ⟨444993269359994295625328741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296662179573329530416885827 444993269359994295625328741)
      ·
        refine ⟨83436238004998930429749139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 444993269359994295625328741 83436238004998930429749139)
        ·
          refine ⟨125154357007498395644623709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83436238004998930429749139 125154357007498395644623709)
          ·
            refine ⟨46932883877811898366733891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125154357007498395644623709 46932883877811898366733891)
            ·
              refine ⟨70399325816717847550100837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46932883877811898366733891 70399325816717847550100837)
              ·
                refine ⟨13199873590634596415643907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70399325816717847550100837 13199873590634596415643907)
                ·
                  refine ⟨19799810385951894623465861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13199873590634596415643907 19799810385951894623465861)
                  ·
                    refine ⟨3712464447365980241899849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19799810385951894623465861 3712464447365980241899849)
                    ·
                      refine ⟨2784348335524485181424887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712464447365980241899849 2784348335524485181424887)
                      ·
                        rfl

theorem cell23_5422499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_5422499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422499 prefixEnd_5422499 := by exact prefixLift 5422499
  have htrace : WordTrace (prefixWord ++ tailWord_5422499) baseStart_5422499 baseEnd_5422499 := by
    simpa [prefixWord, tailWord_5422499, baseEnd_5422499] using wordTrace_append hprefix tailTrace_5422499
  have hstable : (prefixWord ++ tailWord_5422499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422499).length < 2 ^ (prefixWord ++ tailWord_5422499).sum := by decide
  have hdescent : baseEnd_5422499 < baseStart_5422499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422509 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_5422509 : Nat := 118140960795 + 5422509 * 2 ^ 59
def prefixEnd_5422509 : Nat := 4983230072969 + 3 ^ 40 * 5422509 * 2
def baseEnd_5422509 : Nat := 928117823443676714099947

theorem tailTrace_5422509 : CollatzResearch.WordTrace tailWord_5422509 prefixEnd_5422509 928117823443676714099947 := by
  unfold tailWord_5422509
  simp only [CollatzResearch.WordTrace]
  refine ⟨197775151112183458652454581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131850100741455639101636387 197775151112183458652454581)
  ·
    refine ⟨18541420416767199248667617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197775151112183458652454581 18541420416767199248667617)
    ·
      refine ⟨13906065312575399436500713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18541420416767199248667617 13906065312575399436500713)
      ·
        refine ⟨10429548984431549577375535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13906065312575399436500713 10429548984431549577375535)
        ·
          refine ⟨15644323476647324366063303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10429548984431549577375535 15644323476647324366063303)
          ·
            refine ⟨23466485214970986549094955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15644323476647324366063303 23466485214970986549094955)
            ·
              refine ⟨35199727822456479823642433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23466485214970986549094955 35199727822456479823642433)
              ·
                refine ⟨26399795866842359867731825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35199727822456479823642433 26399795866842359867731825)
                ·
                  refine ⟨19799846900131769900798869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26399795866842359867731825 19799846900131769900798869)
                  ·
                    refine ⟨928117823443676714099947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19799846900131769900798869 928117823443676714099947)
                    ·
                      rfl

theorem cell23_5422509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_5422509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422509 prefixEnd_5422509 := by exact prefixLift 5422509
  have htrace : WordTrace (prefixWord ++ tailWord_5422509) baseStart_5422509 baseEnd_5422509 := by
    simpa [prefixWord, tailWord_5422509, baseEnd_5422509] using wordTrace_append hprefix tailTrace_5422509
  have hstable : (prefixWord ++ tailWord_5422509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422509).length < 2 ^ (prefixWord ++ tailWord_5422509).sum := by decide
  have hdescent : baseEnd_5422509 < baseStart_5422509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422552 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_5422552 : Nat := 118140960795 + 5422552 * 2 ^ 59
def prefixEnd_5422552 : Nat := 4983230072969 + 3 ^ 40 * 5422552 * 2
def baseEnd_5422552 : Nat := 928125183333057824687381

theorem tailTrace_5422552 : CollatzResearch.WordTrace tailWord_5422552 prefixEnd_5422552 928125183333057824687381 := by
  unfold tailWord_5422552
  simp only [CollatzResearch.WordTrace]
  refine ⟨98888359725513838498134955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131851146300685117997513273 98888359725513838498134955)
  ·
    refine ⟨148332539588270757747202433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98888359725513838498134955 148332539588270757747202433)
    ·
      refine ⟨111249404691203068310401825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148332539588270757747202433 111249404691203068310401825)
      ·
        refine ⟨83437053518402301232801369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111249404691203068310401825 83437053518402301232801369)
        ·
          refine ⟨62577790138801725924601027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83437053518402301232801369 62577790138801725924601027)
          ·
            refine ⟨93866685208202588886901541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62577790138801725924601027 93866685208202588886901541)
            ·
              refine ⟨17600003476537985416294039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93866685208202588886901541 17600003476537985416294039)
              ·
                refine ⟨26400005214806978124441059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17600003476537985416294039 26400005214806978124441059)
                ·
                  refine ⟨39600007822210467186661589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26400005214806978124441059 39600007822210467186661589)
                  ·
                    refine ⟨928125183333057824687381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39600007822210467186661589 928125183333057824687381)
                    ·
                      rfl

theorem cell23_5422552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_5422552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422552 prefixEnd_5422552 := by exact prefixLift 5422552
  have htrace : WordTrace (prefixWord ++ tailWord_5422552) baseStart_5422552 baseEnd_5422552 := by
    simpa [prefixWord, tailWord_5422552, baseEnd_5422552] using wordTrace_append hprefix tailTrace_5422552
  have hstable : (prefixWord ++ tailWord_5422552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422552).length < 2 ^ (prefixWord ++ tailWord_5422552).sum := by decide
  have hdescent : baseEnd_5422552 < baseStart_5422552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422572 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_5422572 : Nat := 118140960795 + 5422572 * 2 ^ 59
def prefixEnd_5422572 : Nat := 4983230072969 + 3 ^ 40 * 5422572 * 2
def baseEnd_5422572 : Nat := 2784385819612263395812051

theorem tailTrace_5422572 : CollatzResearch.WordTrace tailWord_5422572 prefixEnd_5422572 2784385819612263395812051 := by
  unfold tailWord_5422572
  simp only [CollatzResearch.WordTrace]
  refine ⟨98888724455477610205998985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131851632607303480274665313 98888724455477610205998985)
  ·
    refine ⟨74166543341608207654499239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98888724455477610205998985 74166543341608207654499239)
    ·
      refine ⟨111249815012412311481748859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74166543341608207654499239 111249815012412311481748859)
      ·
        refine ⟨166874722518618467222623289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111249815012412311481748859 166874722518618467222623289)
        ·
          refine ⟨125156041888963850416967467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166874722518618467222623289 125156041888963850416967467)
          ·
            refine ⟨187734062833445775625451201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125156041888963850416967467 187734062833445775625451201)
            ·
              refine ⟨140800547125084331719088401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187734062833445775625451201 140800547125084331719088401)
              ·
                refine ⟨105600410343813248789316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140800547125084331719088401 105600410343813248789316301)
                ·
                  refine ⟨39600153878929968295993613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105600410343813248789316301 39600153878929968295993613)
                  ·
                    refine ⟨14850057704598738110997605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39600153878929968295993613 14850057704598738110997605)
                    ·
                      refine ⟨2784385819612263395812051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14850057704598738110997605 2784385819612263395812051)
                      ·
                        rfl

theorem cell23_5422572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_5422572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422572 prefixEnd_5422572 := by exact prefixLift 5422572
  have htrace : WordTrace (prefixWord ++ tailWord_5422572) baseStart_5422572 baseEnd_5422572 := by
    simpa [prefixWord, tailWord_5422572, baseEnd_5422572] using wordTrace_append hprefix tailTrace_5422572
  have hstable : (prefixWord ++ tailWord_5422572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422572).length < 2 ^ (prefixWord ++ tailWord_5422572).sum := by decide
  have hdescent : baseEnd_5422572 < baseStart_5422572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422573 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 7]
def baseStart_5422573 : Nat := 118140960795 + 5422573 * 2 ^ 59
def prefixEnd_5422573 : Nat := 4983230072969 + 3 ^ 40 * 5422573 * 2
def baseEnd_5422573 : Nat := 309376259232546432433283

theorem tailTrace_5422573 : CollatzResearch.WordTrace tailWord_5422573 prefixEnd_5422573 309376259232546432433283 := by
  unfold tailWord_5422573
  simp only [CollatzResearch.WordTrace]
  refine ⟨197777485383951597582784373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131851656922634398388522915 197777485383951597582784373)
  ·
    refine ⟨18541639254745462273386035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197777485383951597582784373 18541639254745462273386035)
    ·
      refine ⟨27812458882118193410079053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18541639254745462273386035 27812458882118193410079053)
      ·
        refine ⟨10429672080794322528779645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27812458882118193410079053 10429672080794322528779645)
        ·
          refine ⟨3911127030297870948292367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10429672080794322528779645 3911127030297870948292367)
          ·
            refine ⟨5866690545446806422438551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911127030297870948292367 5866690545446806422438551)
            ·
              refine ⟨8800035818170209633657827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866690545446806422438551 8800035818170209633657827)
              ·
                refine ⟨13200053727255314450486741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800035818170209633657827 13200053727255314450486741)
                ·
                  refine ⟨309376259232546432433283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13200053727255314450486741 309376259232546432433283)
                  ·
                    rfl

theorem cell23_5422573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_5422573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422573 prefixEnd_5422573 := by exact prefixLift 5422573
  have htrace : WordTrace (prefixWord ++ tailWord_5422573) baseStart_5422573 baseEnd_5422573 := by
    simpa [prefixWord, tailWord_5422573, baseEnd_5422573] using wordTrace_append hprefix tailTrace_5422573
  have hstable : (prefixWord ++ tailWord_5422573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422573).length < 2 ^ (prefixWord ++ tailWord_5422573).sum := by decide
  have hdescent : baseEnd_5422573 < baseStart_5422573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422626 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_5422626 : Nat := 118140960795 + 5422626 * 2 ^ 59
def prefixEnd_5422626 : Nat := 4983230072969 + 3 ^ 40 * 5422626 * 2
def baseEnd_5422626 : Nat := 2784413547567606184536803

theorem tailTrace_5422626 : CollatzResearch.WordTrace tailWord_5422626 prefixEnd_5422626 2784413547567606184536803 := by
  unfold tailWord_5422626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49444854613189896908615933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131852945635173058422975821 49444854613189896908615933)
  ·
    refine ⟨18541820479946211340730975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49444854613189896908615933 18541820479946211340730975)
    ·
      refine ⟨27812730719919317011096463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18541820479946211340730975 27812730719919317011096463)
      ·
        refine ⟨41719096079878975516644695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27812730719919317011096463 41719096079878975516644695)
        ·
          refine ⟨62578644119818463274967043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41719096079878975516644695 62578644119818463274967043)
          ·
            refine ⟨93867966179727694912450565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62578644119818463274967043 93867966179727694912450565)
            ·
              refine ⟨17600243658698942796084481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93867966179727694912450565 17600243658698942796084481)
              ·
                refine ⟨13200182744024207097063361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17600243658698942796084481 13200182744024207097063361)
                ·
                  refine ⟨9900137058018155322797521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13200182744024207097063361 9900137058018155322797521)
                  ·
                    refine ⟨7425102793513616492098141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9900137058018155322797521 7425102793513616492098141)
                    ·
                      refine ⟨2784413547567606184536803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7425102793513616492098141 2784413547567606184536803)
                      ·
                        rfl

theorem cell23_5422626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_5422626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422626 prefixEnd_5422626 := by exact prefixLift 5422626
  have htrace : WordTrace (prefixWord ++ tailWord_5422626) baseStart_5422626 baseEnd_5422626 := by
    simpa [prefixWord, tailWord_5422626, baseEnd_5422626] using wordTrace_append hprefix tailTrace_5422626
  have hstable : (prefixWord ++ tailWord_5422626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422626).length < 2 ^ (prefixWord ++ tailWord_5422626).sum := by decide
  have hdescent : baseEnd_5422626 < baseStart_5422626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422666 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_5422666 : Nat := 118140960795 + 5422666 * 2 ^ 59
def prefixEnd_5422666 : Nat := 4983230072969 + 3 ^ 40 * 5422666 * 2
def baseEnd_5422666 : Nat := 2784434086793786028036619

theorem tailTrace_5422666 : CollatzResearch.WordTrace tailWord_5422666 prefixEnd_5422666 2784434086793786028036619 := by
  unfold tailWord_5422666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49445219343153668616479963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131853918248409782977279901 49445219343153668616479963)
  ·
    refine ⟨74167829014730502924719945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49445219343153668616479963 74167829014730502924719945)
    ·
      refine ⟨55625871761047877193539959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74167829014730502924719945 55625871761047877193539959)
      ·
        refine ⟨83438807641571815790309939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55625871761047877193539959 83438807641571815790309939)
        ·
          refine ⟨125158211462357723685464909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83438807641571815790309939 125158211462357723685464909)
          ·
            refine ⟨46934329298384146382049341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125158211462357723685464909 46934329298384146382049341)
            ·
              refine ⟨17600373486894054893268503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46934329298384146382049341 17600373486894054893268503)
              ·
                refine ⟨26400560230341082339902755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17600373486894054893268503 26400560230341082339902755)
                ·
                  refine ⟨39600840345511623509854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26400560230341082339902755 39600840345511623509854133)
                  ·
                    refine ⟨3712578782391714704048825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39600840345511623509854133 3712578782391714704048825)
                    ·
                      refine ⟨2784434086793786028036619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712578782391714704048825 2784434086793786028036619)
                      ·
                        rfl

theorem cell23_5422666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_5422666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422666 prefixEnd_5422666 := by exact prefixLift 5422666
  have htrace : WordTrace (prefixWord ++ tailWord_5422666) baseStart_5422666 baseEnd_5422666 := by
    simpa [prefixWord, tailWord_5422666, baseEnd_5422666] using wordTrace_append hprefix tailTrace_5422666
  have hstable : (prefixWord ++ tailWord_5422666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422666).length < 2 ^ (prefixWord ++ tailWord_5422666).sum := by decide
  have hdescent : baseEnd_5422666 < baseStart_5422666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422676 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_5422676 : Nat := 118140960795 + 5422676 * 2 ^ 59
def prefixEnd_5422676 : Nat := 4983230072969 + 3 ^ 40 * 5422676 * 2
def baseEnd_5422676 : Nat := 928146407200110329637191

theorem tailTrace_5422676 : CollatzResearch.WordTrace tailWord_5422676 prefixEnd_5422676 928146407200110329637191 := by
  unfold tailWord_5422676
  simp only [CollatzResearch.WordTrace]
  refine ⟨98890621051289223086891941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131854161401718964115855921 98890621051289223086891941)
  ·
    refine ⟨18541991447116729328792239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98890621051289223086891941 18541991447116729328792239)
    ·
      refine ⟨27812987170675093993188359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18541991447116729328792239 27812987170675093993188359)
      ·
        refine ⟨41719480756012640989782539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27812987170675093993188359 41719480756012640989782539)
        ·
          refine ⟨62579221134018961484673809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41719480756012640989782539 62579221134018961484673809)
          ·
            refine ⟨46934415850514221113505357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62579221134018961484673809 46934415850514221113505357)
            ·
              refine ⟨17600405943942832917564509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46934415850514221113505357 17600405943942832917564509)
              ·
                refine ⟨6600152228978562344086691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17600405943942832917564509 6600152228978562344086691)
                ·
                  refine ⟨9900228343467843516130037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6600152228978562344086691 9900228343467843516130037)
                  ·
                    refine ⟨928146407200110329637191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9900228343467843516130037 928146407200110329637191)
                    ·
                      rfl

theorem cell23_5422676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_5422676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422676 prefixEnd_5422676 := by exact prefixLift 5422676
  have htrace : WordTrace (prefixWord ++ tailWord_5422676) baseStart_5422676 baseEnd_5422676 := by
    simpa [prefixWord, tailWord_5422676, baseEnd_5422676] using wordTrace_append hprefix tailTrace_5422676
  have hstable : (prefixWord ++ tailWord_5422676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422676).length < 2 ^ (prefixWord ++ tailWord_5422676).sum := by decide
  have hdescent : baseEnd_5422676 < baseStart_5422676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422706 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_5422706 : Nat := 118140960795 + 5422706 * 2 ^ 59
def prefixEnd_5422706 : Nat := 4983230072969 + 3 ^ 40 * 5422706 * 2
def baseEnd_5422706 : Nat := 928151542006655290512145

theorem tailTrace_5422706 : CollatzResearch.WordTrace tailWord_5422706 prefixEnd_5422706 928151542006655290512145 := by
  unfold tailWord_5422706
  simp only [CollatzResearch.WordTrace]
  refine ⟨49445584073117440324343993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131854890861646507531583981 49445584073117440324343993)
  ·
    refine ⟨37084188054838080243257995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49445584073117440324343993 37084188054838080243257995)
    ·
      refine ⟨55626282082257120364886993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37084188054838080243257995 55626282082257120364886993)
      ·
        refine ⟨41719711561692840273665245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55626282082257120364886993 41719711561692840273665245)
        ·
          refine ⟨15644891835634815102624467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41719711561692840273665245 15644891835634815102624467)
          ·
            refine ⟨23467337753452222653936701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15644891835634815102624467 23467337753452222653936701)
            ·
              refine ⟨8800251657544583495226263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23467337753452222653936701 8800251657544583495226263)
              ·
                refine ⟨13200377486316875242839395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800251657544583495226263 13200377486316875242839395)
                ·
                  refine ⟨19800566229475312864259093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13200377486316875242839395 19800566229475312864259093)
                  ·
                    refine ⟨928151542006655290512145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19800566229475312864259093 928151542006655290512145)
                    ·
                      rfl

theorem cell23_5422706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_5422706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422706 prefixEnd_5422706 := by exact prefixLift 5422706
  have htrace : WordTrace (prefixWord ++ tailWord_5422706) baseStart_5422706 baseEnd_5422706 := by
    simpa [prefixWord, tailWord_5422706, baseEnd_5422706] using wordTrace_append hprefix tailTrace_5422706
  have hstable : (prefixWord ++ tailWord_5422706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422706).length < 2 ^ (prefixWord ++ tailWord_5422706).sum := by decide
  have hdescent : baseEnd_5422706 < baseStart_5422706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422713 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 3, 2, 2]
def baseStart_5422713 : Nat := 118140960795 + 5422713 * 2 ^ 59
def prefixEnd_5422713 : Nat := 4983230072969 + 3 ^ 40 * 5422713 * 2
def baseEnd_5422713 : Nat := 2784458220384547344148903

theorem tailTrace_5422713 : CollatzResearch.WordTrace tailWord_5422713 prefixEnd_5422713 2784458220384547344148903 := by
  unfold tailWord_5422713
  simp only [CollatzResearch.WordTrace]
  refine ⟨197782591603444401492880793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131855061068962934328587195 197782591603444401492880793)
  ·
    refine ⟨148336943702583301119660595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197782591603444401492880793 148336943702583301119660595)
    ·
      refine ⟨222505415553874951679490893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148336943702583301119660595 222505415553874951679490893)
      ·
        refine ⟨83439530832703106879809085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222505415553874951679490893 83439530832703106879809085)
        ·
          refine ⟨31289824062263665079928407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83439530832703106879809085 31289824062263665079928407)
          ·
            refine ⟨46934736093395497619892611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31289824062263665079928407 46934736093395497619892611)
            ·
              refine ⟨70402104140093246429838917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46934736093395497619892611 70402104140093246429838917)
              ·
                refine ⟨13200394526267483705594797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70402104140093246429838917 13200394526267483705594797)
                ·
                  refine ⟨4950147947350306389598049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13200394526267483705594797 4950147947350306389598049)
                  ·
                    refine ⟨3712610960512729792198537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4950147947350306389598049 3712610960512729792198537)
                    ·
                      refine ⟨2784458220384547344148903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712610960512729792198537 2784458220384547344148903)
                      ·
                        rfl

theorem cell23_5422713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_5422713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422713 prefixEnd_5422713 := by exact prefixLift 5422713
  have htrace : WordTrace (prefixWord ++ tailWord_5422713) baseStart_5422713 baseEnd_5422713 := by
    simpa [prefixWord, tailWord_5422713, baseEnd_5422713] using wordTrace_append hprefix tailTrace_5422713
  have hstable : (prefixWord ++ tailWord_5422713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422713).length < 2 ^ (prefixWord ++ tailWord_5422713).sum := by decide
  have hdescent : baseEnd_5422713 < baseStart_5422713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422724 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_5422724 : Nat := 118140960795 + 5422724 * 2 ^ 59
def prefixEnd_5422724 : Nat := 4983230072969 + 3 ^ 40 * 5422724 * 2
def baseEnd_5422724 : Nat := 2784463868671746801111353

theorem tailTrace_5422724 : CollatzResearch.WordTrace tailWord_5422724 prefixEnd_5422724 2784463868671746801111353 := by
  unfold tailWord_5422724
  simp only [CollatzResearch.WordTrace]
  refine ⟨98891496403202275185765613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131855328537603033581020817 98891496403202275185765613)
  ·
    refine ⟨37084311151200853194662105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98891496403202275185765613 37084311151200853194662105)
    ·
      refine ⟨27813233363400639895996579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37084311151200853194662105 27813233363400639895996579)
      ·
        refine ⟨41719850045100959843994869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27813233363400639895996579 41719850045100959843994869)
        ·
          refine ⟨3911235941728214985374519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41719850045100959843994869 3911235941728214985374519)
          ·
            refine ⟨5866853912592322478061779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911235941728214985374519 5866853912592322478061779)
            ·
              refine ⟨8800280868888483717092669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866853912592322478061779 8800280868888483717092669)
              ·
                refine ⟨3300105325833181393909751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8800280868888483717092669 3300105325833181393909751)
                ·
                  refine ⟨4950157988749772090864627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300105325833181393909751 4950157988749772090864627)
                  ·
                    refine ⟨7425236983124658136296941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4950157988749772090864627 7425236983124658136296941)
                    ·
                      refine ⟨2784463868671746801111353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7425236983124658136296941 2784463868671746801111353)
                      ·
                        rfl

theorem cell23_5422724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_5422724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422724 prefixEnd_5422724 := by exact prefixLift 5422724
  have htrace : WordTrace (prefixWord ++ tailWord_5422724) baseStart_5422724 baseEnd_5422724 := by
    simpa [prefixWord, tailWord_5422724, baseEnd_5422724] using wordTrace_append hprefix tailTrace_5422724
  have hstable : (prefixWord ++ tailWord_5422724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422724).length < 2 ^ (prefixWord ++ tailWord_5422724).sum := by decide
  have hdescent : baseEnd_5422724 < baseStart_5422724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422749 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_5422749 : Nat := 118140960795 + 5422749 * 2 ^ 59
def prefixEnd_5422749 : Nat := 4983230072969 + 3 ^ 40 * 5422749 * 2
def baseEnd_5422749 : Nat := 928158901896036401099579

theorem tailTrace_5422749 : CollatzResearch.WordTrace tailWord_5422749 prefixEnd_5422749 928158901896036401099579 := by
  unfold tailWord_5422749
  simp only [CollatzResearch.WordTrace]
  refine ⟨197783904631313979641191301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131855936420875986427460867 197783904631313979641191301)
  ·
    refine ⟨37084482118371371182723369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197783904631313979641191301 37084482118371371182723369)
    ·
      refine ⟨27813361588778528387042527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37084482118371371182723369 27813361588778528387042527)
      ·
        refine ⟨41720042383167792580563791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27813361588778528387042527 41720042383167792580563791)
        ·
          refine ⟨62580063574751688870845687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41720042383167792580563791 62580063574751688870845687)
          ·
            refine ⟨93870095362127533306268531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62580063574751688870845687 93870095362127533306268531)
            ·
              refine ⟨140805143043191299959402797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93870095362127533306268531 140805143043191299959402797)
              ·
                refine ⟨52801928641196737484776049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140805143043191299959402797 52801928641196737484776049)
                ·
                  refine ⟨39601446480897553113582037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52801928641196737484776049 39601446480897553113582037)
                  ·
                    refine ⟨928158901896036401099579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39601446480897553113582037 928158901896036401099579)
                    ·
                      rfl

theorem cell23_5422749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_5422749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422749 prefixEnd_5422749 := by exact prefixLift 5422749
  have htrace : WordTrace (prefixWord ++ tailWord_5422749) baseStart_5422749 baseEnd_5422749 := by
    simpa [prefixWord, tailWord_5422749, baseEnd_5422749] using wordTrace_append hprefix tailTrace_5422749
  have hstable : (prefixWord ++ tailWord_5422749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422749).length < 2 ^ (prefixWord ++ tailWord_5422749).sum := by decide
  have hdescent : baseEnd_5422749 < baseStart_5422749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422797 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5422797 : Nat := 118140960795 + 5422797 * 2 ^ 59
def prefixEnd_5422797 : Nat := 4983230072969 + 3 ^ 40 * 5422797 * 2
def baseEnd_5422797 : Nat := 2784501352759525015498517

theorem tailTrace_5422797 : CollatzResearch.WordTrace tailWord_5422797 prefixEnd_5422797 2784501352759525015498517 := by
  unfold tailWord_5422797
  simp only [CollatzResearch.WordTrace]
  refine ⟨197785655335140083838938645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131857103556760055892625763 197785655335140083838938645)
  ·
    refine ⟨9271202593834691429950249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197785655335140083838938645 9271202593834691429950249)
    ·
      refine ⟨6953401945376018572462687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9271202593834691429950249 6953401945376018572462687)
      ·
        refine ⟨10430102918064027858694031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6953401945376018572462687 10430102918064027858694031)
        ·
          refine ⟨15645154377096041788041047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10430102918064027858694031 15645154377096041788041047)
          ·
            refine ⟨23467731565644062682061571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15645154377096041788041047 23467731565644062682061571)
            ·
              refine ⟨35201597348466094023092357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23467731565644062682061571 35201597348466094023092357)
              ·
                refine ⟨6600299502837392629329817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35201597348466094023092357 6600299502837392629329817)
                ·
                  refine ⟨4950224627128044471997363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6600299502837392629329817 4950224627128044471997363)
                  ·
                    refine ⟨7425336940692066707996045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4950224627128044471997363 7425336940692066707996045)
                    ·
                      refine ⟨2784501352759525015498517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7425336940692066707996045 2784501352759525015498517)
                      ·
                        rfl

theorem cell23_5422797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5422797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422797 prefixEnd_5422797 := by exact prefixLift 5422797
  have htrace : WordTrace (prefixWord ++ tailWord_5422797) baseStart_5422797 baseEnd_5422797 := by
    simpa [prefixWord, tailWord_5422797, baseEnd_5422797] using wordTrace_append hprefix tailTrace_5422797
  have hstable : (prefixWord ++ tailWord_5422797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422797).length < 2 ^ (prefixWord ++ tailWord_5422797).sum := by decide
  have hdescent : baseEnd_5422797 < baseStart_5422797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422799 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_5422799 : Nat := 118140960795 + 5422799 * 2 ^ 59
def prefixEnd_5422799 : Nat := 4983230072969 + 3 ^ 40 * 5422799 * 2
def baseEnd_5422799 : Nat := 2784502379720834007673507

theorem tailTrace_5422799 : CollatzResearch.WordTrace tailWord_5422799 prefixEnd_5422799 2784502379720834007673507 := by
  unfold tailWord_5422799
  simp only [CollatzResearch.WordTrace]
  refine ⟨197785728281132838180511451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131857152187421892120340967 197785728281132838180511451)
  ·
    refine ⟨296678592421699257270767177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197785728281132838180511451 296678592421699257270767177)
    ·
      refine ⟨222508944316274442953075383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296678592421699257270767177 222508944316274442953075383)
      ·
        refine ⟨333763416474411664429613075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222508944316274442953075383 333763416474411664429613075)
        ·
          refine ⟨500645124711617496644419613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333763416474411664429613075 500645124711617496644419613)
          ·
            refine ⟨187741921766856561241657355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500645124711617496644419613 187741921766856561241657355)
            ·
              refine ⟨281612882650284841862486033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187741921766856561241657355 281612882650284841862486033)
              ·
                refine ⟨211209661987713631396864525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281612882650284841862486033 211209661987713631396864525)
                ·
                  refine ⟨79203623245392611773824197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211209661987713631396864525 79203623245392611773824197)
                  ·
                    refine ⟨14850679358511114707592037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79203623245392611773824197 14850679358511114707592037)
                    ·
                      refine ⟨2784502379720834007673507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14850679358511114707592037 2784502379720834007673507)
                      ·
                        rfl

theorem cell23_5422799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_5422799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422799 prefixEnd_5422799 := by exact prefixLift 5422799
  have htrace : WordTrace (prefixWord ++ tailWord_5422799) baseStart_5422799 baseEnd_5422799 := by
    simpa [prefixWord, tailWord_5422799, baseEnd_5422799] using wordTrace_append hprefix tailTrace_5422799
  have hstable : (prefixWord ++ tailWord_5422799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422799).length < 2 ^ (prefixWord ++ tailWord_5422799).sum := by decide
  have hdescent : baseEnd_5422799 < baseStart_5422799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422820 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_5422820 : Nat := 118140960795 + 5422820 * 2 ^ 59
def prefixEnd_5422820 : Nat := 4983230072969 + 3 ^ 40 * 5422820 * 2
def baseEnd_5422820 : Nat := 2784513162814578425510911

theorem tailTrace_5422820 : CollatzResearch.WordTrace tailWord_5422820 prefixEnd_5422820 2784513162814578425510911 := by
  unfold tailWord_5422820
  simp only [CollatzResearch.WordTrace]
  refine ⟨98893247107028379383512957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131857662809371172511350609 98893247107028379383512957)
  ·
    refine ⟨37084967665135642268817359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98893247107028379383512957 37084967665135642268817359)
    ·
      refine ⟨55627451497703463403226039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37084967665135642268817359 55627451497703463403226039)
      ·
        refine ⟨83441177246555195104839059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55627451497703463403226039 83441177246555195104839059)
        ·
          refine ⟨125161765869832792657258589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83441177246555195104839059 125161765869832792657258589)
          ·
            refine ⟨46935662201187297246471971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125161765869832792657258589 46935662201187297246471971)
            ·
              refine ⟨70403493301780945869707957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46935662201187297246471971 70403493301780945869707957)
              ·
                refine ⟨6600327497041963675285121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70403493301780945869707957 6600327497041963675285121)
                ·
                  refine ⟨4950245622781472756463841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6600327497041963675285121 4950245622781472756463841)
                  ·
                    refine ⟨3712684217086104567347881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4950245622781472756463841 3712684217086104567347881)
                    ·
                      refine ⟨2784513162814578425510911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712684217086104567347881 2784513162814578425510911)
                      ·
                        rfl

theorem cell23_5422820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_5422820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422820 prefixEnd_5422820 := by exact prefixLift 5422820
  have htrace : WordTrace (prefixWord ++ tailWord_5422820) baseStart_5422820 baseEnd_5422820 := by
    simpa [prefixWord, tailWord_5422820, baseEnd_5422820] using wordTrace_append hprefix tailTrace_5422820
  have hstable : (prefixWord ++ tailWord_5422820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422820).length < 2 ^ (prefixWord ++ tailWord_5422820).sum := by decide
  have hdescent : baseEnd_5422820 < baseStart_5422820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422856 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_5422856 : Nat := 118140960795 + 5422856 * 2 ^ 59
def prefixEnd_5422856 : Nat := 4983230072969 + 3 ^ 40 * 5422856 * 2
def baseEnd_5422856 : Nat := 928177216039380094886915

theorem tailTrace_5422856 : CollatzResearch.WordTrace tailWord_5422856 prefixEnd_5422856 928177216039380094886915 := by
  unfold tailWord_5422856
  simp only [CollatzResearch.WordTrace]
  refine ⟨98893903620963168457668211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131858538161284224610224281 98893903620963168457668211)
  ·
    refine ⟨148340855431444752686502317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98893903620963168457668211 148340855431444752686502317)
    ·
      refine ⟨55627820786791782257438369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148340855431444752686502317 55627820786791782257438369)
      ·
        refine ⟨41720865590093836693078777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55627820786791782257438369 41720865590093836693078777)
        ·
          refine ⟨31290649192570377519809083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41720865590093836693078777 31290649192570377519809083)
          ·
            refine ⟨46935973788855566279713625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31290649192570377519809083 46935973788855566279713625)
            ·
              refine ⟨35201980341641674709785219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46935973788855566279713625 35201980341641674709785219)
              ·
                refine ⟨52802970512462512064677829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35201980341641674709785219 52802970512462512064677829)
                ·
                  refine ⟨9900556971086721012127093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52802970512462512064677829 9900556971086721012127093)
                  ·
                    refine ⟨928177216039380094886915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9900556971086721012127093 928177216039380094886915)
                    ·
                      rfl

theorem cell23_5422856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_5422856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422856 prefixEnd_5422856 := by exact prefixLift 5422856
  have htrace : WordTrace (prefixWord ++ tailWord_5422856) baseStart_5422856 baseEnd_5422856 := by
    simpa [prefixWord, tailWord_5422856, baseEnd_5422856] using wordTrace_append hprefix tailTrace_5422856
  have hstable : (prefixWord ++ tailWord_5422856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422856).length < 2 ^ (prefixWord ++ tailWord_5422856).sum := by decide
  have hdescent : baseEnd_5422856 < baseStart_5422856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422876 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5422876 : Nat := 118140960795 + 5422876 * 2 ^ 59
def prefixEnd_5422876 : Nat := 4983230072969 + 3 ^ 40 * 5422876 * 2
def baseEnd_5422876 : Nat := 2784541917731230206410653

theorem tailTrace_5422876 : CollatzResearch.WordTrace tailWord_5422876 prefixEnd_5422876 2784541917731230206410653 := by
  unfold tailWord_5422876
  simp only [CollatzResearch.WordTrace]
  refine ⟨98894268350926940165532241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131859024467902586887376321 98894268350926940165532241)
  ·
    refine ⟨74170701263195205124149181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98894268350926940165532241 74170701263195205124149181)
    ·
      refine ⟨27814012973698201921555943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74170701263195205124149181 27814012973698201921555943)
      ·
        refine ⟨41721019460547302882333915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27814012973698201921555943 41721019460547302882333915)
        ·
          refine ⟨62581529190820954323500873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41721019460547302882333915 62581529190820954323500873)
          ·
            refine ⟨46936146893115715742625655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62581529190820954323500873 46936146893115715742625655)
            ·
              refine ⟨70404220339673573613938483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46936146893115715742625655 70404220339673573613938483)
              ·
                refine ⟨105606330509510360420907725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70404220339673573613938483 105606330509510360420907725)
                ·
                  refine ⟨39602373941066385157840397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105606330509510360420907725 39602373941066385157840397)
                  ·
                    refine ⟨14850890227899894434190149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39602373941066385157840397 14850890227899894434190149)
                    ·
                      refine ⟨2784541917731230206410653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14850890227899894434190149 2784541917731230206410653)
                      ·
                        rfl

theorem cell23_5422876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5422876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422876 prefixEnd_5422876 := by exact prefixLift 5422876
  have htrace : WordTrace (prefixWord ++ tailWord_5422876) baseStart_5422876 baseEnd_5422876 := by
    simpa [prefixWord, tailWord_5422876, baseEnd_5422876] using wordTrace_append hprefix tailTrace_5422876
  have hstable : (prefixWord ++ tailWord_5422876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422876).length < 2 ^ (prefixWord ++ tailWord_5422876).sum := by decide
  have hdescent : baseEnd_5422876 < baseStart_5422876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422894 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_5422894 : Nat := 118140960795 + 5422894 * 2 ^ 59
def prefixEnd_5422894 : Nat := 4983230072969 + 3 ^ 40 * 5422894 * 2
def baseEnd_5422894 : Nat := 309394573375890126220619

theorem tailTrace_5422894 : CollatzResearch.WordTrace tailWord_5422894 prefixEnd_5422894 309394573375890126220619 := by
  unfold tailWord_5422894
  simp only [CollatzResearch.WordTrace]
  refine ⟨24723649151973583675652467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131859462143859112936813157 24723649151973583675652467)
  ·
    refine ⟨37085473727960375513478701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24723649151973583675652467 37085473727960375513478701)
    ·
      refine ⟨13907052647985140817554513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37085473727960375513478701 13907052647985140817554513)
      ·
        refine ⟨10430289485988855613165885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13907052647985140817554513 10430289485988855613165885)
        ·
          refine ⟨3911358557245820854937207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10430289485988855613165885 3911358557245820854937207)
          ·
            refine ⟨5867037835868731282405811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911358557245820854937207 5867037835868731282405811)
            ·
              refine ⟨8800556753803096923608717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867037835868731282405811 8800556753803096923608717)
              ·
                refine ⟨3300208782676161346353269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8800556753803096923608717 3300208782676161346353269)
                ·
                  refine ⟨309394573375890126220619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3300208782676161346353269 309394573375890126220619)
                  ·
                    rfl

theorem cell23_5422894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_5422894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422894 prefixEnd_5422894 := by exact prefixLift 5422894
  have htrace : WordTrace (prefixWord ++ tailWord_5422894) baseStart_5422894 baseEnd_5422894 := by
    simpa [prefixWord, tailWord_5422894, baseEnd_5422894] using wordTrace_append hprefix tailTrace_5422894
  have hstable : (prefixWord ++ tailWord_5422894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422894).length < 2 ^ (prefixWord ++ tailWord_5422894).sum := by decide
  have hdescent : baseEnd_5422894 < baseStart_5422894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422910 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5422910 : Nat := 118140960795 + 5422910 * 2 ^ 59
def prefixEnd_5422910 : Nat := 4983230072969 + 3 ^ 40 * 5422910 * 2
def baseEnd_5422910 : Nat := 2784559376073483073385497

theorem tailTrace_5422910 : CollatzResearch.WordTrace tailWord_5422910 prefixEnd_5422910 2784559376073483073385497 := by
  unfold tailWord_5422910
  simp only [CollatzResearch.WordTrace]
  refine ⟨24723722097966338017225273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131859851189153802758534789 24723722097966338017225273)
  ·
    refine ⟨18542791573474753512918955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24723722097966338017225273 18542791573474753512918955)
    ·
      refine ⟨27814187360212130269378433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18542791573474753512918955 27814187360212130269378433)
      ·
        refine ⟨20860640520159097702033825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27814187360212130269378433 20860640520159097702033825)
        ·
          refine ⟨15645480390119323276525369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20860640520159097702033825 15645480390119323276525369)
          ·
            refine ⟨11734110292589492457394027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15645480390119323276525369 11734110292589492457394027)
            ·
              refine ⟨17601165438884238686091041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11734110292589492457394027 17601165438884238686091041)
              ·
                refine ⟨13200874079163179014568281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17601165438884238686091041 13200874079163179014568281)
                ·
                  refine ⟨9900655559372384260926211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13200874079163179014568281 9900655559372384260926211)
                  ·
                    refine ⟨14850983339058576391389317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9900655559372384260926211 14850983339058576391389317)
                    ·
                      refine ⟨2784559376073483073385497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14850983339058576391389317 2784559376073483073385497)
                      ·
                        rfl

theorem cell23_5422910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5422910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422910 prefixEnd_5422910 := by exact prefixLift 5422910
  have htrace : WordTrace (prefixWord ++ tailWord_5422910) baseStart_5422910 baseEnd_5422910 := by
    simpa [prefixWord, tailWord_5422910, baseEnd_5422910] using wordTrace_append hprefix tailTrace_5422910
  have hstable : (prefixWord ++ tailWord_5422910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422910).length < 2 ^ (prefixWord ++ tailWord_5422910).sum := by decide
  have hdescent : baseEnd_5422910 < baseStart_5422910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422920 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 3, 4]
def baseStart_5422920 : Nat := 118140960795 + 5422920 * 2 ^ 59
def prefixEnd_5422920 : Nat := 4983230072969 + 3 ^ 40 * 5422920 * 2
def baseEnd_5422920 : Nat := 928188170293342678086817

theorem tailTrace_5422920 : CollatzResearch.WordTrace tailWord_5422920 prefixEnd_5422920 928188170293342678086817 := by
  unfold tailWord_5422920
  simp only [CollatzResearch.WordTrace]
  refine ⟨98895070756847237922833107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131860094342462983897110809 98895070756847237922833107)
  ·
    refine ⟨148342606135270856884249661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98895070756847237922833107 148342606135270856884249661)
    ·
      refine ⟨55628477300726571331593623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148342606135270856884249661 55628477300726571331593623)
      ·
        refine ⟨83442715951089856997390435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55628477300726571331593623 83442715951089856997390435)
        ·
          refine ⟨125164073926634785496085653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83442715951089856997390435 125164073926634785496085653)
          ·
            refine ⟨5867065965311005570129015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125164073926634785496085653 5867065965311005570129015)
            ·
              refine ⟨8800598947966508355193523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867065965311005570129015 8800598947966508355193523)
              ·
                refine ⟨13200898421949762532790285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800598947966508355193523 13200898421949762532790285)
                ·
                  refine ⟨4950336908231160949796357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13200898421949762532790285 4950336908231160949796357)
                  ·
                    refine ⟨928188170293342678086817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4950336908231160949796357 928188170293342678086817)
                    ·
                      rfl

theorem cell23_5422920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_5422920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422920 prefixEnd_5422920 := by exact prefixLift 5422920
  have htrace : WordTrace (prefixWord ++ tailWord_5422920) baseStart_5422920 baseEnd_5422920 := by
    simpa [prefixWord, tailWord_5422920, baseEnd_5422920] using wordTrace_append hprefix tailTrace_5422920
  have hstable : (prefixWord ++ tailWord_5422920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422920).length < 2 ^ (prefixWord ++ tailWord_5422920).sum := by decide
  have hdescent : baseEnd_5422920 < baseStart_5422920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422933 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 6]
def baseStart_5422933 : Nat := 118140960795 + 5422933 * 2 ^ 59
def prefixEnd_5422933 : Nat := 4983230072969 + 3 ^ 40 * 5422933 * 2
def baseEnd_5422933 : Nat := 309396798458726275933099

theorem tailTrace_5422933 : CollatzResearch.WordTrace tailWord_5422933 prefixEnd_5422933 309396798458726275933099 := by
  unfold tailWord_5422933
  simp only [CollatzResearch.WordTrace]
  refine ⟨197790615662647379065889453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131860410441764919377259635 197790615662647379065889453)
  ·
    refine ⟨74171480873492767149708545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197790615662647379065889453 74171480873492767149708545)
    ·
      refine ⟨55628610655119575362281409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74171480873492767149708545 55628610655119575362281409)
      ·
        refine ⟨41721457991339681521711057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55628610655119575362281409 41721457991339681521711057)
        ·
          refine ⟨31291093493504761141283293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41721457991339681521711057 31291093493504761141283293)
          ·
            refine ⟨11734160060064285427981235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31291093493504761141283293 11734160060064285427981235)
            ·
              refine ⟨17601240090096428141971853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11734160060064285427981235 17601240090096428141971853)
              ·
                refine ⟨6600465033786160553239445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17601240090096428141971853 6600465033786160553239445)
                ·
                  refine ⟨309396798458726275933099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6600465033786160553239445 309396798458726275933099)
                  ·
                    rfl

theorem cell23_5422933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_5422933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422933 prefixEnd_5422933 := by exact prefixLift 5422933
  have htrace : WordTrace (prefixWord ++ tailWord_5422933) baseStart_5422933 baseEnd_5422933 := by
    simpa [prefixWord, tailWord_5422933, baseEnd_5422933] using wordTrace_append hprefix tailTrace_5422933
  have hstable : (prefixWord ++ tailWord_5422933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422933).length < 2 ^ (prefixWord ++ tailWord_5422933).sum := by decide
  have hdescent : baseEnd_5422933 < baseStart_5422933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422953 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 1, 5, 2]
def baseStart_5422953 : Nat := 118140960795 + 5422953 * 2 ^ 59
def prefixEnd_5422953 : Nat := 4983230072969 + 3 ^ 40 * 5422953 * 2
def baseEnd_5422953 : Nat := 2784581455741626405147799

theorem tailTrace_5422953 : CollatzResearch.WordTrace tailWord_5422953 prefixEnd_5422953 2784581455741626405147799 := by
  unfold tailWord_5422953
  simp only [CollatzResearch.WordTrace]
  refine ⟨197791345122574922481617513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131860896748383281654411675 197791345122574922481617513)
  ·
    refine ⟨148343508841931191861213135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197791345122574922481617513 148343508841931191861213135)
    ·
      refine ⟨222515263262896787791819703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148343508841931191861213135 222515263262896787791819703)
      ·
        refine ⟨333772894894345181687729555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222515263262896787791819703 333772894894345181687729555)
        ·
          refine ⟨500659342341517772531594333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333772894894345181687729555 500659342341517772531594333)
          ·
            refine ⟨187747253378069164699347875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500659342341517772531594333 187747253378069164699347875)
            ·
              refine ⟨281620880067103747049021813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187747253378069164699347875 281620880067103747049021813)
              ·
                refine ⟨26401957506290976285845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281620880067103747049021813 26401957506290976285845795)
                ·
                  refine ⟨39602936259436464428768693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26401957506290976285845795 39602936259436464428768693)
                  ·
                    refine ⟨3712775274322168540197065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39602936259436464428768693 3712775274322168540197065)
                    ·
                      refine ⟨2784581455741626405147799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712775274322168540197065 2784581455741626405147799)
                      ·
                        rfl

theorem cell23_5422953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 5, 2].length) (baseStart_5422953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422953 prefixEnd_5422953 := by exact prefixLift 5422953
  have htrace : WordTrace (prefixWord ++ tailWord_5422953) baseStart_5422953 baseEnd_5422953 := by
    simpa [prefixWord, tailWord_5422953, baseEnd_5422953] using wordTrace_append hprefix tailTrace_5422953
  have hstable : (prefixWord ++ tailWord_5422953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422953).length < 2 ^ (prefixWord ++ tailWord_5422953).sum := by decide
  have hdescent : baseEnd_5422953 < baseStart_5422953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422970 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2]
def baseStart_5422970 : Nat := 118140960795 + 5422970 * 2 ^ 59
def prefixEnd_5422970 : Nat := 4983230072969 + 3 ^ 40 * 5422970 * 2
def baseEnd_5422970 : Nat := 2784590184912752838635221

theorem tailTrace_5422970 : CollatzResearch.WordTrace tailWord_5422970 prefixEnd_5422970 2784590184912752838635221 := by
  unfold tailWord_5422970
  simp only [CollatzResearch.WordTrace]
  refine ⟨49447991290878333596246591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131861310109008889589990909 49447991290878333596246591)
  ·
    refine ⟨74171986936317500394369887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49447991290878333596246591 74171986936317500394369887)
    ·
      refine ⟨111257980404476250591554831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74171986936317500394369887 111257980404476250591554831)
      ·
        refine ⟨166886970606714375887332247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111257980404476250591554831 166886970606714375887332247)
        ·
          refine ⟨250330455910071563830998371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166886970606714375887332247 250330455910071563830998371)
          ·
            refine ⟨375495683865107345746497557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250330455910071563830998371 375495683865107345746497557)
            ·
              refine ⟨17601360181176906831867073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 375495683865107345746497557 17601360181176906831867073)
              ·
                refine ⟨13201020135882680123900305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17601360181176906831867073 13201020135882680123900305)
                ·
                  refine ⟨9900765101912010092925229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13201020135882680123900305 9900765101912010092925229)
                  ·
                    refine ⟨3712786913217003784846961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9900765101912010092925229 3712786913217003784846961)
                    ·
                      refine ⟨2784590184912752838635221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712786913217003784846961 2784590184912752838635221)
                      ·
                        rfl

theorem cell23_5422970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_5422970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422970 prefixEnd_5422970 := by exact prefixLift 5422970
  have htrace : WordTrace (prefixWord ++ tailWord_5422970) baseStart_5422970 baseEnd_5422970 := by
    simpa [prefixWord, tailWord_5422970, baseEnd_5422970] using wordTrace_append hprefix tailTrace_5422970
  have hstable : (prefixWord ++ tailWord_5422970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422970).length < 2 ^ (prefixWord ++ tailWord_5422970).sum := by decide
  have hdescent : baseEnd_5422970 < baseStart_5422970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422976 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_5422976 : Nat := 118140960795 + 5422976 * 2 ^ 59
def prefixEnd_5422976 : Nat := 4983230072969 + 3 ^ 40 * 5422976 * 2
def baseEnd_5422976 : Nat := 928197755265559938386731

theorem tailTrace_5422976 : CollatzResearch.WordTrace tailWord_5422976 prefixEnd_5422976 928197755265559938386731 := by
  unfold tailWord_5422976
  simp only [CollatzResearch.WordTrace]
  refine ⟨98896092000745798704852391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131861456000994398273136521 98896092000745798704852391)
  ·
    refine ⟨148344138001118698057278587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98896092000745798704852391 148344138001118698057278587)
    ·
      refine ⟨222516207001678047085917881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148344138001118698057278587 222516207001678047085917881)
      ·
        refine ⟨166887155251258535314438411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222516207001678047085917881 166887155251258535314438411)
        ·
          refine ⟨250330732876887802971657617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166887155251258535314438411 250330732876887802971657617)
          ·
            refine ⟨187748049657665852228743213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250330732876887802971657617 187748049657665852228743213)
            ·
              refine ⟨70405518621624694585778705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187748049657665852228743213 70405518621624694585778705)
              ·
                refine ⟨52804138966218520939334029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70405518621624694585778705 52804138966218520939334029)
                ·
                  refine ⟨19801552112331945352250261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52804138966218520939334029 19801552112331945352250261)
                  ·
                    refine ⟨928197755265559938386731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19801552112331945352250261 928197755265559938386731)
                    ·
                      rfl

theorem cell23_5422976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_5422976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422976 prefixEnd_5422976 := by exact prefixLift 5422976
  have htrace : WordTrace (prefixWord ++ tailWord_5422976) baseStart_5422976 baseEnd_5422976 := by
    simpa [prefixWord, tailWord_5422976, baseEnd_5422976] using wordTrace_append hprefix tailTrace_5422976
  have hstable : (prefixWord ++ tailWord_5422976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422976).length < 2 ^ (prefixWord ++ tailWord_5422976).sum := by decide
  have hdescent : baseEnd_5422976 < baseStart_5422976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422998 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5422998 : Nat := 118140960795 + 5422998 * 2 ^ 59
def prefixEnd_5422998 : Nat := 4983230072969 + 3 ^ 40 * 5422998 * 2
def baseEnd_5422998 : Nat := 2784604562371078729085093

theorem tailTrace_5422998 : CollatzResearch.WordTrace tailWord_5422998 prefixEnd_5422998 2784604562371078729085093 := by
  unfold tailWord_5422998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12362061650463243447937853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131861990938274596778003765 12362061650463243447937853)
  ·
    refine ⟨4635773118923716292976695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12362061650463243447937853 4635773118923716292976695)
    ·
      refine ⟨6953659678385574439465043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4635773118923716292976695 6953659678385574439465043)
      ·
        refine ⟨10430489517578361659197565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6953659678385574439465043 10430489517578361659197565)
        ·
          refine ⟨3911433569091885622199087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10430489517578361659197565 3911433569091885622199087)
          ·
            refine ⟨5867150353637828433298631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911433569091885622199087 5867150353637828433298631)
            ·
              refine ⟨8800725530456742649947947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867150353637828433298631 8800725530456742649947947)
              ·
                refine ⟨13201088295685113974921921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800725530456742649947947 13201088295685113974921921)
                ·
                  refine ⟨9900816221763835481191441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13201088295685113974921921 9900816221763835481191441)
                  ·
                    refine ⟨7425612166322876610893581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9900816221763835481191441 7425612166322876610893581)
                    ·
                      refine ⟨2784604562371078729085093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7425612166322876610893581 2784604562371078729085093)
                      ·
                        rfl

theorem cell23_5422998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5422998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5422998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5422998 prefixEnd_5422998 := by exact prefixLift 5422998
  have htrace : WordTrace (prefixWord ++ tailWord_5422998) baseStart_5422998 baseEnd_5422998 := by
    simpa [prefixWord, tailWord_5422998, baseEnd_5422998] using wordTrace_append hprefix tailTrace_5422998
  have hstable : (prefixWord ++ tailWord_5422998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422998).length < 2 ^ (prefixWord ++ tailWord_5422998).sum := by decide
  have hdescent : baseEnd_5422998 < baseStart_5422998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423004 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5423004 : Nat := 118140960795 + 5423004 * 2 ^ 59
def prefixEnd_5423004 : Nat := 4983230072969 + 3 ^ 40 * 5423004 * 2
def baseEnd_5423004 : Nat := 2784607643255005705610065

theorem tailTrace_5423004 : CollatzResearch.WordTrace tailWord_5423004 prefixEnd_5423004 2784607643255005705610065 := by
  unfold tailWord_5423004
  simp only [CollatzResearch.WordTrace]
  refine ⟨98896602622695079095862033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131862136830260105461149377 98896602622695079095862033)
  ·
    refine ⟨74172451967021309321896525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98896602622695079095862033 74172451967021309321896525)
    ·
      refine ⟨27814669487632990995711197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74172451967021309321896525 27814669487632990995711197)
      ·
        refine ⟨10430501057862371623391699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27814669487632990995711197 10430501057862371623391699)
        ·
          refine ⟨15645751586793557435087549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10430501057862371623391699 15645751586793557435087549)
          ·
            refine ⟨5867156845047584038157831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15645751586793557435087549 5867156845047584038157831)
            ·
              refine ⟨8800735267571376057236747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867156845047584038157831 8800735267571376057236747)
              ·
                refine ⟨13201102901357064085855121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800735267571376057236747 13201102901357064085855121)
                ·
                  refine ⟨9900827176017798064391341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13201102901357064085855121 9900827176017798064391341)
                  ·
                    refine ⟨3712810191006674274146753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9900827176017798064391341 3712810191006674274146753)
                    ·
                      refine ⟨2784607643255005705610065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712810191006674274146753 2784607643255005705610065)
                      ·
                        rfl

theorem cell23_5423004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5423004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423004 prefixEnd_5423004 := by exact prefixLift 5423004
  have htrace : WordTrace (prefixWord ++ tailWord_5423004) baseStart_5423004 baseEnd_5423004 := by
    simpa [prefixWord, tailWord_5423004, baseEnd_5423004] using wordTrace_append hprefix tailTrace_5423004
  have hstable : (prefixWord ++ tailWord_5423004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423004).length < 2 ^ (prefixWord ++ tailWord_5423004).sum := by decide
  have hdescent : baseEnd_5423004 < baseStart_5423004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423050 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_5423050 : Nat := 118140960795 + 5423050 * 2 ^ 59
def prefixEnd_5423050 : Nat := 4983230072969 + 3 ^ 40 * 5423050 * 2
def baseEnd_5423050 : Nat := 2784631263365112525634853

theorem tailTrace_5423050 : CollatzResearch.WordTrace tailWord_5423050 prefixEnd_5423050 2784631263365112525634853 := by
  unfold tailWord_5423050
  simp only [CollatzResearch.WordTrace]
  refine ⟨49448720750805877011974651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131863255335482338698599069 49448720750805877011974651)
  ·
    refine ⟨74173081126208815517961977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49448720750805877011974651 74173081126208815517961977)
    ·
      refine ⟨55629810844656611638471483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74173081126208815517961977 55629810844656611638471483)
      ·
        refine ⟨83444716266984917457707225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55629810844656611638471483 83444716266984917457707225)
        ·
          refine ⟨62583537200238688093280419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83444716266984917457707225 62583537200238688093280419)
          ·
            refine ⟨93875305800358032139920629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62583537200238688093280419 93875305800358032139920629)
            ·
              refine ⟨8800809918783565513117559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93875305800358032139920629 8800809918783565513117559)
              ·
                refine ⟨13201214878175348269676339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800809918783565513117559 13201214878175348269676339)
                ·
                  refine ⟨19801822317263022404514509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13201214878175348269676339 19801822317263022404514509)
                  ·
                    refine ⟨7425683368973633401692941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19801822317263022404514509 7425683368973633401692941)
                    ·
                      refine ⟨2784631263365112525634853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7425683368973633401692941 2784631263365112525634853)
                      ·
                        rfl

theorem cell23_5423050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_5423050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423050 prefixEnd_5423050 := by exact prefixLift 5423050
  have htrace : WordTrace (prefixWord ++ tailWord_5423050) baseStart_5423050 baseEnd_5423050 := by
    simpa [prefixWord, tailWord_5423050, baseEnd_5423050] using wordTrace_append hprefix tailTrace_5423050
  have hstable : (prefixWord ++ tailWord_5423050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423050).length < 2 ^ (prefixWord ++ tailWord_5423050).sum := by decide
  have hdescent : baseEnd_5423050 < baseStart_5423050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423085 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5423085 : Nat := 118140960795 + 5423085 * 2 ^ 59
def prefixEnd_5423085 : Nat := 4983230072969 + 3 ^ 40 * 5423085 * 2
def baseEnd_5423085 : Nat := 2784649235188019888697193

theorem tailTrace_5423085 : CollatzResearch.WordTrace tailWord_5423085 prefixEnd_5423085 2784649235188019888697193 := by
  unfold tailWord_5423085
  simp only [CollatzResearch.WordTrace]
  refine ⟨197796159558096709025422709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131864106372064472683615139 197796159558096709025422709)
  ·
    refine ⟨18543389958571566471133379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197796159558096709025422709 18543389958571566471133379)
    ·
      refine ⟨27815084937857349706700069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18543389958571566471133379 27815084937857349706700069)
      ·
        refine ⟨5215328425848253070006263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27815084937857349706700069 5215328425848253070006263)
        ·
          refine ⟨7822992638772379605009395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215328425848253070006263 7822992638772379605009395)
          ·
            refine ⟨11734488958158569407514093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7822992638772379605009395 11734488958158569407514093)
            ·
              refine ⟨4400433359309463527817785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11734488958158569407514093 4400433359309463527817785)
              ·
                refine ⟨3300325019482097645863339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4400433359309463527817785 3300325019482097645863339)
                ·
                  refine ⟨4950487529223146468795009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300325019482097645863339 4950487529223146468795009)
                  ·
                    refine ⟨3712865646917359851596257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4950487529223146468795009 3712865646917359851596257)
                    ·
                      refine ⟨2784649235188019888697193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3712865646917359851596257 2784649235188019888697193)
                      ·
                        rfl

theorem cell23_5423085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5423085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423085 prefixEnd_5423085 := by exact prefixLift 5423085
  have htrace : WordTrace (prefixWord ++ tailWord_5423085) baseStart_5423085 baseEnd_5423085 := by
    simpa [prefixWord, tailWord_5423085, baseEnd_5423085] using wordTrace_append hprefix tailTrace_5423085
  have hstable : (prefixWord ++ tailWord_5423085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423085).length < 2 ^ (prefixWord ++ tailWord_5423085).sum := by decide
  have hdescent : baseEnd_5423085 < baseStart_5423085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423103 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_5423103 : Nat := 118140960795 + 5423103 * 2 ^ 59
def prefixEnd_5423103 : Nat := 4983230072969 + 3 ^ 40 * 5423103 * 2
def baseEnd_5423103 : Nat := 2784658477839800818272109

theorem tailTrace_5423103 : CollatzResearch.WordTrace tailWord_5423103 prefixEnd_5423103 2784658477839800818272109 := by
  unfold tailWord_5423103
  simp only [CollatzResearch.WordTrace]
  refine ⟨197796816072031498099577963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131864544048020998733051975 197796816072031498099577963)
  ·
    refine ⟨296695224108047247149366945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197796816072031498099577963 296695224108047247149366945)
    ·
      refine ⟨222521418081035435362025209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296695224108047247149366945 222521418081035435362025209)
      ·
        refine ⟨166891063560776576521518907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222521418081035435362025209 166891063560776576521518907)
        ·
          refine ⟨250336595341164864782278361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166891063560776576521518907 250336595341164864782278361)
          ·
            refine ⟨187752446505873648586708771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250336595341164864782278361 187752446505873648586708771)
            ·
              refine ⟨281628669758810472880063157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187752446505873648586708771 281628669758810472880063157)
              ·
                refine ⟨26402687789888481832505921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281628669758810472880063157 26402687789888481832505921)
                ·
                  refine ⟨19802015842416361374379441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26402687789888481832505921 19802015842416361374379441)
                  ·
                    refine ⟨14851511881812271030784581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19802015842416361374379441 14851511881812271030784581)
                    ·
                      refine ⟨2784658477839800818272109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14851511881812271030784581 2784658477839800818272109)
                      ·
                        rfl

theorem cell23_5423103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_5423103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423103 prefixEnd_5423103 := by exact prefixLift 5423103
  have htrace : WordTrace (prefixWord ++ tailWord_5423103) baseStart_5423103 baseEnd_5423103 := by
    simpa [prefixWord, tailWord_5423103, baseEnd_5423103] using wordTrace_append hprefix tailTrace_5423103
  have hstable : (prefixWord ++ tailWord_5423103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423103).length < 2 ^ (prefixWord ++ tailWord_5423103).sum := by decide
  have hdescent : baseEnd_5423103 < baseStart_5423103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423163 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4]
def baseStart_5423163 : Nat := 118140960795 + 5423163 * 2 ^ 59
def prefixEnd_5423163 : Nat := 4983230072969 + 3 ^ 40 * 5423163 * 2
def baseEnd_5423163 : Nat := 2784689286679070583521833

theorem tailTrace_5423163 : CollatzResearch.WordTrace tailWord_5423163 prefixEnd_5423163 2784689286679070583521833 := by
  unfold tailWord_5423163
  simp only [CollatzResearch.WordTrace]
  refine ⟨197799004451814128346762143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131866002967876085564508095 197799004451814128346762143)
  ·
    refine ⟨296698506677721192520143215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197799004451814128346762143 296698506677721192520143215)
    ·
      refine ⟨445047760016581788780214823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296698506677721192520143215 445047760016581788780214823)
      ·
        refine ⟨667571640024872683170322235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445047760016581788780214823 667571640024872683170322235)
        ·
          refine ⟨1001357460037309024755483353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667571640024872683170322235 1001357460037309024755483353)
          ·
            refine ⟨751018095027981768566612515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001357460037309024755483353 751018095027981768566612515)
            ·
              refine ⟨1126527142541972652849918773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751018095027981768566612515 1126527142541972652849918773)
              ·
                refine ⟨105611919613309936204679885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1126527142541972652849918773 105611919613309936204679885)
                ·
                  refine ⟨39604469854991226076754957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105611919613309936204679885 39604469854991226076754957)
                  ·
                    refine ⟨14851676195621709778783109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39604469854991226076754957 14851676195621709778783109)
                    ·
                      refine ⟨2784689286679070583521833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14851676195621709778783109 2784689286679070583521833)
                      ·
                        rfl

theorem cell23_5423163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_5423163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423163 prefixEnd_5423163 := by exact prefixLift 5423163
  have htrace : WordTrace (prefixWord ++ tailWord_5423163) baseStart_5423163 baseEnd_5423163 := by
    simpa [prefixWord, tailWord_5423163, baseEnd_5423163] using wordTrace_append hprefix tailTrace_5423163
  have hstable : (prefixWord ++ tailWord_5423163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423163).length < 2 ^ (prefixWord ++ tailWord_5423163).sum := by decide
  have hdescent : baseEnd_5423163 < baseStart_5423163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423193 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_5423193 : Nat := 118140960795 + 5423193 * 2 ^ 59
def prefixEnd_5423193 : Nat := 4983230072969 + 3 ^ 40 * 5423193 * 2
def baseEnd_5423193 : Nat := 2784704691098705466146695

theorem tailTrace_5423193 : CollatzResearch.WordTrace tailWord_5423193 prefixEnd_5423193 2784704691098705466146695 := by
  unfold tailWord_5423193
  simp only [CollatzResearch.WordTrace]
  refine ⟨197800098641705443470354233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131866732427803628980236155 197800098641705443470354233)
  ·
    refine ⟨148350073981279082602765675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197800098641705443470354233 148350073981279082602765675)
    ·
      refine ⟨222525110971918623904148513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148350073981279082602765675 222525110971918623904148513)
      ·
        refine ⟨166893833228938967928111385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222525110971918623904148513 166893833228938967928111385)
        ·
          refine ⟨125170374921704225946083539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166893833228938967928111385 125170374921704225946083539)
          ·
            refine ⟨187755562382556338919125309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125170374921704225946083539 187755562382556338919125309)
            ·
              refine ⟨70408335893458627094671991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187755562382556338919125309 70408335893458627094671991)
              ·
                refine ⟨105612503840187940642007987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70408335893458627094671991 105612503840187940642007987)
                ·
                  refine ⟨158418755760281910963011981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105612503840187940642007987 158418755760281910963011981)
                  ·
                    refine ⟨59407033410105716611129493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158418755760281910963011981 59407033410105716611129493)
                    ·
                      refine ⟨2784704691098705466146695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59407033410105716611129493 2784704691098705466146695)
                      ·
                        rfl

theorem cell23_5423193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_5423193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423193 prefixEnd_5423193 := by exact prefixLift 5423193
  have htrace : WordTrace (prefixWord ++ tailWord_5423193) baseStart_5423193 baseEnd_5423193 := by
    simpa [prefixWord, tailWord_5423193, baseEnd_5423193] using wordTrace_append hprefix tailTrace_5423193
  have hstable : (prefixWord ++ tailWord_5423193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423193).length < 2 ^ (prefixWord ++ tailWord_5423193).sum := by decide
  have hdescent : baseEnd_5423193 < baseStart_5423193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423207 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 3, 4]
def baseStart_5423207 : Nat := 118140960795 + 5423207 * 2 ^ 59
def prefixEnd_5423207 : Nat := 4983230072969 + 3 ^ 40 * 5423207 * 2
def baseEnd_5423207 : Nat := 928237293275956137123877

theorem tailTrace_5423207 : CollatzResearch.WordTrace tailWord_5423207 prefixEnd_5423207 928237293275956137123877 := by
  unfold tailWord_5423207
  simp only [CollatzResearch.WordTrace]
  refine ⟨197800609263654723861363875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131867072842436482574242583 197800609263654723861363875)
  ·
    refine ⟨296700913895482085792045813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197800609263654723861363875 296700913895482085792045813)
    ·
      refine ⟨27815710677701445543004295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296700913895482085792045813 27815710677701445543004295)
      ·
        refine ⟨41723566016552168314506443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27815710677701445543004295 41723566016552168314506443)
        ·
          refine ⟨62585349024828252471759665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41723566016552168314506443 62585349024828252471759665)
          ·
            refine ⟨46939011768621189353819749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62585349024828252471759665 46939011768621189353819749)
            ·
              refine ⟨8801064706616473003841203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46939011768621189353819749 8801064706616473003841203)
              ·
                refine ⟨13201597059924709505761805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801064706616473003841203 13201597059924709505761805)
                ·
                  refine ⟨4950598897471766064660677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13201597059924709505761805 4950598897471766064660677)
                  ·
                    refine ⟨928237293275956137123877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4950598897471766064660677 928237293275956137123877)
                    ·
                      rfl

theorem cell23_5423207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_5423207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423207 prefixEnd_5423207 := by exact prefixLift 5423207
  have htrace : WordTrace (prefixWord ++ tailWord_5423207) baseStart_5423207 baseEnd_5423207 := by
    simpa [prefixWord, tailWord_5423207, baseEnd_5423207] using wordTrace_append hprefix tailTrace_5423207
  have hstable : (prefixWord ++ tailWord_5423207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423207).length < 2 ^ (prefixWord ++ tailWord_5423207).sum := by decide
  have hdescent : baseEnd_5423207 < baseStart_5423207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423258 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_5423258 : Nat := 118140960795 + 5423258 * 2 ^ 59
def prefixEnd_5423258 : Nat := 4983230072969 + 3 ^ 40 * 5423258 * 2
def baseEnd_5423258 : Nat := 928246022447082570611299

theorem tailTrace_5423258 : CollatzResearch.WordTrace tailWord_5423258 prefixEnd_5423258 928246022447082570611299 := by
  unfold tailWord_5423258
  simp only [CollatzResearch.WordTrace]
  refine ⟨49450617346617489892867607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131868312924313306380980285 49450617346617489892867607)
  ·
    refine ⟨74175926019926234839301411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49450617346617489892867607 74175926019926234839301411)
    ·
      refine ⟨111263889029889352258952117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74175926019926234839301411 111263889029889352258952117)
      ·
        refine ⟨10430989596552126774276761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111263889029889352258952117 10430989596552126774276761)
        ·
          refine ⟨7823242197414095080707571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10430989596552126774276761 7823242197414095080707571)
          ·
            refine ⟨11734863296121142621061357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7823242197414095080707571 11734863296121142621061357)
            ·
              refine ⟨4400573736045428482898009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11734863296121142621061357 4400573736045428482898009)
              ·
                refine ⟨3300430302034071362173507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4400573736045428482898009 3300430302034071362173507)
                ·
                  refine ⟨4950645453051107043260261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300430302034071362173507 4950645453051107043260261)
                  ·
                    refine ⟨928246022447082570611299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4950645453051107043260261 928246022447082570611299)
                    ·
                      rfl

theorem cell23_5423258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_5423258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423258 prefixEnd_5423258 := by exact prefixLift 5423258
  have htrace : WordTrace (prefixWord ++ tailWord_5423258) baseStart_5423258 baseEnd_5423258 := by
    simpa [prefixWord, tailWord_5423258, baseEnd_5423258] using wordTrace_append hprefix tailTrace_5423258
  have hstable : (prefixWord ++ tailWord_5423258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423258).length < 2 ^ (prefixWord ++ tailWord_5423258).sum := by decide
  have hdescent : baseEnd_5423258 < baseStart_5423258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423264 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 3, 1, 3]
def baseStart_5423264 : Nat := 118140960795 + 5423264 * 2 ^ 59
def prefixEnd_5423264 : Nat := 4983230072969 + 3 ^ 40 * 5423264 * 2
def baseEnd_5423264 : Nat := 2784741148225174688358869

theorem tailTrace_5423264 : CollatzResearch.WordTrace tailWord_5423264 prefixEnd_5423264 2784741148225174688358869 := by
  unfold tailWord_5423264
  simp only [CollatzResearch.WordTrace]
  refine ⟨98901344112224111298094423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131868458816298815064125897 98901344112224111298094423)
  ·
    refine ⟨148352016168336166947141635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98901344112224111298094423 148352016168336166947141635)
    ·
      refine ⟨222528024252504250420712453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148352016168336166947141635 222528024252504250420712453)
      ·
        refine ⟨41724004547344546953883585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222528024252504250420712453 41724004547344546953883585)
        ·
          refine ⟨31293003410508410215412689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41724004547344546953883585 31293003410508410215412689)
          ·
            refine ⟨23469752557881307661559517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31293003410508410215412689 23469752557881307661559517)
            ·
              refine ⟨8801157209205490373084819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23469752557881307661559517 8801157209205490373084819)
              ·
                refine ⟨13201735813808235559627229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801157209205490373084819 13201735813808235559627229)
                ·
                  refine ⟨4950650930178088334860211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13201735813808235559627229 4950650930178088334860211)
                  ·
                    refine ⟨7425976395267132502290317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4950650930178088334860211 7425976395267132502290317)
                    ·
                      refine ⟨2784741148225174688358869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7425976395267132502290317 2784741148225174688358869)
                      ·
                        rfl

theorem cell23_5423264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_5423264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423264 prefixEnd_5423264 := by exact prefixLift 5423264
  have htrace : WordTrace (prefixWord ++ tailWord_5423264) baseStart_5423264 baseEnd_5423264 := by
    simpa [prefixWord, tailWord_5423264, baseEnd_5423264] using wordTrace_append hprefix tailTrace_5423264
  have hstable : (prefixWord ++ tailWord_5423264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423264).length < 2 ^ (prefixWord ++ tailWord_5423264).sum := by decide
  have hdescent : baseEnd_5423264 < baseStart_5423264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423271 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 6]
def baseStart_5423271 : Nat := 118140960795 + 5423271 * 2 ^ 59
def prefixEnd_5423271 : Nat := 4983230072969 + 3 ^ 40 * 5423271 * 2
def baseEnd_5423271 : Nat := 309416082509972906774593

theorem tailTrace_5423271 : CollatzResearch.WordTrace tailWord_5423271 prefixEnd_5423271 309416082509972906774593 := by
  unfold tailWord_5423271
  simp only [CollatzResearch.WordTrace]
  refine ⟨197802943535422862791693667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131868629023615241861129111 197802943535422862791693667)
  ·
    refine ⟨296704415303134294187540501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197802943535422862791693667 296704415303134294187540501)
    ·
      refine ⟨13908019467334420040040961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 296704415303134294187540501 13908019467334420040040961)
      ·
        refine ⟨10431014600500815030030721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13908019467334420040040961 10431014600500815030030721)
        ·
          refine ⟨7823260950375611272523041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10431014600500815030030721 7823260950375611272523041)
          ·
            refine ⟨5867445712781708454392281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7823260950375611272523041 5867445712781708454392281)
            ·
              refine ⟨4400584284586281340794211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5867445712781708454392281 4400584284586281340794211)
              ·
                refine ⟨6600876426879422011191317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400584284586281340794211 6600876426879422011191317)
                ·
                  refine ⟨309416082509972906774593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6600876426879422011191317 309416082509972906774593)
                  ·
                    rfl

theorem cell23_5423271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 6].length) (baseStart_5423271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423271 prefixEnd_5423271 := by exact prefixLift 5423271
  have htrace : WordTrace (prefixWord ++ tailWord_5423271) baseStart_5423271 baseEnd_5423271 := by
    simpa [prefixWord, tailWord_5423271, baseEnd_5423271] using wordTrace_append hprefix tailTrace_5423271
  have hstable : (prefixWord ++ tailWord_5423271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423271).length < 2 ^ (prefixWord ++ tailWord_5423271).sum := by decide
  have hdescent : baseEnd_5423271 < baseStart_5423271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423287 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_5423287 : Nat := 118140960795 + 5423287 * 2 ^ 59
def prefixEnd_5423287 : Nat := 4983230072969 + 3 ^ 40 * 5423287 * 2
def baseEnd_5423287 : Nat := 2784752958280228098371263

theorem tailTrace_5423287 : CollatzResearch.WordTrace tailWord_5423287 prefixEnd_5423287 2784752958280228098371263 := by
  unfold tailWord_5423287
  simp only [CollatzResearch.WordTrace]
  refine ⟨197803527103364897524276115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131869018068909931682850743 197803527103364897524276115)
  ·
    refine ⟨296705290655047346286414173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197803527103364897524276115 296705290655047346286414173)
    ·
      refine ⟨111264483995642754857405315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296705290655047346286414173 111264483995642754857405315)
      ·
        refine ⟨166896725993464132286107973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111264483995642754857405315 166896725993464132286107973)
        ·
          refine ⟨31293136123774524803645245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166896725993464132286107973 31293136123774524803645245)
          ·
            refine ⟨11734926046415446801366967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31293136123774524803645245 11734926046415446801366967)
            ·
              refine ⟨17602389069623170202050451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11734926046415446801366967 17602389069623170202050451)
              ·
                refine ⟨26403583604434755303075677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17602389069623170202050451 26403583604434755303075677)
                ·
                  refine ⟨9901343851663033238653379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26403583604434755303075677 9901343851663033238653379)
                  ·
                    refine ⟨14852015777494549857980069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9901343851663033238653379 14852015777494549857980069)
                    ·
                      refine ⟨2784752958280228098371263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14852015777494549857980069 2784752958280228098371263)
                      ·
                        rfl

theorem cell23_5423287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_5423287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423287 prefixEnd_5423287 := by exact prefixLift 5423287
  have htrace : WordTrace (prefixWord ++ tailWord_5423287) baseStart_5423287 baseEnd_5423287 := by
    simpa [prefixWord, tailWord_5423287, baseEnd_5423287] using wordTrace_append hprefix tailTrace_5423287
  have hstable : (prefixWord ++ tailWord_5423287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423287).length < 2 ^ (prefixWord ++ tailWord_5423287).sum := by decide
  have hdescent : baseEnd_5423287 < baseStart_5423287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423290 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_5423290 : Nat := 118140960795 + 5423290 * 2 ^ 59
def prefixEnd_5423290 : Nat := 4983230072969 + 3 ^ 40 * 5423290 * 2
def baseEnd_5423290 : Nat := 2784754498722191586633749

theorem tailTrace_5423290 : CollatzResearch.WordTrace tailWord_5423290 prefixEnd_5423290 2784754498722191586633749 := by
  unfold tailWord_5423290
  simp only [CollatzResearch.WordTrace]
  refine ⟨49450909130588507259158831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131869091014902686024423549 49450909130588507259158831)
  ·
    refine ⟨74176363695882760888738247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49450909130588507259158831 74176363695882760888738247)
    ·
      refine ⟨111264545543824141333107371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74176363695882760888738247 111264545543824141333107371)
      ·
        refine ⟨166896818315736211999661057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111264545543824141333107371 166896818315736211999661057)
        ·
          refine ⟨125172613736802158999745793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166896818315736211999661057 125172613736802158999745793)
          ·
            refine ⟨93879460302601619249809345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125172613736802158999745793 93879460302601619249809345)
            ·
              refine ⟨70409595226951214437357009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93879460302601619249809345 70409595226951214437357009)
              ·
                refine ⟨52807196420213410828017757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70409595226951214437357009 52807196420213410828017757)
                ·
                  refine ⟨19802698657580029060506659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52807196420213410828017757 19802698657580029060506659)
                  ·
                    refine ⟨29704047986370043590759989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19802698657580029060506659 29704047986370043590759989)
                    ·
                      refine ⟨2784754498722191586633749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29704047986370043590759989 2784754498722191586633749)
                      ·
                        rfl

theorem cell23_5423290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_5423290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423290 prefixEnd_5423290 := by exact prefixLift 5423290
  have htrace : WordTrace (prefixWord ++ tailWord_5423290) baseStart_5423290 baseEnd_5423290 := by
    simpa [prefixWord, tailWord_5423290, baseEnd_5423290] using wordTrace_append hprefix tailTrace_5423290
  have hstable : (prefixWord ++ tailWord_5423290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423290).length < 2 ^ (prefixWord ++ tailWord_5423290).sum := by decide
  have hdescent : baseEnd_5423290 < baseStart_5423290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423310 : List Nat := [4, 1, 1, 1, 4, 12]
def baseStart_5423310 : Nat := 118140960795 + 5423310 * 2 ^ 59
def prefixEnd_5423310 : Nat := 4983230072969 + 3 ^ 40 * 5423310 * 2
def baseEnd_5423310 : Nat := 11459937318252187277299

theorem tailTrace_5423310 : CollatzResearch.WordTrace tailWord_5423310 prefixEnd_5423310 11459937318252187277299 := by
  unfold tailWord_5423310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24725545747785196556545423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131869577321521048301575589 24725545747785196556545423)
  ·
    refine ⟨37088318621677794834818135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24725545747785196556545423 37088318621677794834818135)
    ·
      refine ⟨55632477932516692252227203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37088318621677794834818135 55632477932516692252227203)
      ·
        refine ⟨83448716898775038378340805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55632477932516692252227203 83448716898775038378340805)
        ·
          refine ⟨15646634418520319695938901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83448716898775038378340805 15646634418520319695938901)
          ·
            refine ⟨11459937318252187277299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15646634418520319695938901 11459937318252187277299)
            ·
              rfl

theorem cell23_5423310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 12].length) (baseStart_5423310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423310 prefixEnd_5423310 := by exact prefixLift 5423310
  have htrace : WordTrace (prefixWord ++ tailWord_5423310) baseStart_5423310 baseEnd_5423310 := by
    simpa [prefixWord, tailWord_5423310, baseEnd_5423310] using wordTrace_append hprefix tailTrace_5423310
  have hstable : (prefixWord ++ tailWord_5423310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423310).length < 2 ^ (prefixWord ++ tailWord_5423310).sum := by decide
  have hdescent : baseEnd_5423310 < baseStart_5423310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423314 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_5423314 : Nat := 118140960795 + 5423314 * 2 ^ 59
def prefixEnd_5423314 : Nat := 4983230072969 + 3 ^ 40 * 5423314 * 2
def baseEnd_5423314 : Nat := 928255607419299830911213

theorem tailTrace_5423314 : CollatzResearch.WordTrace tailWord_5423314 prefixEnd_5423314 928255607419299830911213 := by
  unfold tailWord_5423314
  simp only [CollatzResearch.WordTrace]
  refine ⟨49451127968566770283877249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131869674582844720757005997 49451127968566770283877249)
  ·
    refine ⟨37088345976425077712907937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49451127968566770283877249 37088345976425077712907937)
    ·
      refine ⟨27816259482318808284680953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37088345976425077712907937 27816259482318808284680953)
      ·
        refine ⟨20862194611739106213510715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27816259482318808284680953 20862194611739106213510715)
        ·
          refine ⟨31293291917608659320266073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20862194611739106213510715 31293291917608659320266073)
          ·
            refine ⟨23469968938206494490199555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31293291917608659320266073 23469968938206494490199555)
            ·
              refine ⟨35204953407309741735299333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23469968938206494490199555 35204953407309741735299333)
              ·
                refine ⟨6600928763870576575368625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35204953407309741735299333 6600928763870576575368625)
                ·
                  refine ⟨4950696572902932431526469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6600928763870576575368625 4950696572902932431526469)
                  ·
                    refine ⟨928255607419299830911213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4950696572902932431526469 928255607419299830911213)
                    ·
                      rfl

theorem cell23_5423314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_5423314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423314 prefixEnd_5423314 := by exact prefixLift 5423314
  have htrace : WordTrace (prefixWord ++ tailWord_5423314) baseStart_5423314 baseEnd_5423314 := by
    simpa [prefixWord, tailWord_5423314, baseEnd_5423314] using wordTrace_append hprefix tailTrace_5423314
  have hstable : (prefixWord ++ tailWord_5423314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423314).length < 2 ^ (prefixWord ++ tailWord_5423314).sum := by decide
  have hdescent : baseEnd_5423314 < baseStart_5423314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423340 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_5423340 : Nat := 118140960795 + 5423340 * 2 ^ 59
def prefixEnd_5423340 : Nat := 4983230072969 + 3 ^ 40 * 5423340 * 2
def baseEnd_5423340 : Nat := 928260057584972130336173

theorem tailTrace_5423340 : CollatzResearch.WordTrace tailWord_5423340 prefixEnd_5423340 928260057584972130336173 := by
  unfold tailWord_5423340
  simp only [CollatzResearch.WordTrace]
  refine ⟨98902730086086443787977737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131870306781448591717303649 98902730086086443787977737)
  ·
    refine ⟨74177047564564832840983303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98902730086086443787977737 74177047564564832840983303)
    ·
      refine ⟨111265571346847249261474955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74177047564564832840983303 111265571346847249261474955)
      ·
        refine ⟨166898357020270873892212433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111265571346847249261474955 166898357020270873892212433)
        ·
          refine ⟨125173767765203155419159325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166898357020270873892212433 125173767765203155419159325)
          ·
            refine ⟨46940162911951183282184747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125173767765203155419159325 46940162911951183282184747)
            ·
              refine ⟨70410244367926774923277121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46940162911951183282184747 70410244367926774923277121)
              ·
                refine ⟨52807683275945081192457841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70410244367926774923277121 52807683275945081192457841)
                ·
                  refine ⟨39605762456958810894343381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52807683275945081192457841 39605762456958810894343381)
                  ·
                    refine ⟨928260057584972130336173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39605762456958810894343381 928260057584972130336173)
                    ·
                      rfl

theorem cell23_5423340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_5423340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423340 prefixEnd_5423340 := by exact prefixLift 5423340
  have htrace : WordTrace (prefixWord ++ tailWord_5423340) baseStart_5423340 baseEnd_5423340 := by
    simpa [prefixWord, tailWord_5423340, baseEnd_5423340] using wordTrace_append hprefix tailTrace_5423340
  have hstable : (prefixWord ++ tailWord_5423340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423340).length < 2 ^ (prefixWord ++ tailWord_5423340).sum := by decide
  have hdescent : baseEnd_5423340 < baseStart_5423340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423427 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 3]
def baseStart_5423427 : Nat := 118140960795 + 5423427 * 2 ^ 59
def prefixEnd_5423427 : Nat := 4983230072969 + 3 ^ 40 * 5423427 * 2
def baseEnd_5423427 : Nat := 2784824845571857550620619

theorem tailTrace_5423427 : CollatzResearch.WordTrace tailWord_5423427 prefixEnd_5423427 2784824845571857550620619 := by
  unfold tailWord_5423427
  simp only [CollatzResearch.WordTrace]
  refine ⟨197808633322857701434372535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131872422215238467622915023 197808633322857701434372535)
  ·
    refine ⟨296712949984286552151558803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197808633322857701434372535 296712949984286552151558803)
    ·
      refine ⟨445069424976429828227338205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296712949984286552151558803 445069424976429828227338205)
      ·
        refine ⟨166901034366161185585251827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 445069424976429828227338205 166901034366161185585251827)
        ·
          refine ⟨250351551549241778377877741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166901034366161185585251827 250351551549241778377877741)
          ·
            refine ⟨93881831830965666891704153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250351551549241778377877741 93881831830965666891704153)
            ·
              refine ⟨70411373873224250168778115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93881831830965666891704153 70411373873224250168778115)
              ·
                refine ⟨105617060809836375253167173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70411373873224250168778115 105617060809836375253167173)
                ·
                  refine ⟨19803198901844320359968845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105617060809836375253167173 19803198901844320359968845)
                  ·
                    refine ⟨7426199588191620134988317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19803198901844320359968845 7426199588191620134988317)
                    ·
                      refine ⟨2784824845571857550620619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426199588191620134988317 2784824845571857550620619)
                      ·
                        rfl

theorem cell23_5423427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_5423427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423427 prefixEnd_5423427 := by exact prefixLift 5423427
  have htrace : WordTrace (prefixWord ++ tailWord_5423427) baseStart_5423427 baseEnd_5423427 := by
    simpa [prefixWord, tailWord_5423427, baseEnd_5423427] using wordTrace_append hprefix tailTrace_5423427
  have hstable : (prefixWord ++ tailWord_5423427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423427).length < 2 ^ (prefixWord ++ tailWord_5423427).sum := by decide
  have hdescent : baseEnd_5423427 < baseStart_5423427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423447 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 4, 5]
def baseStart_5423447 : Nat := 118140960795 + 5423447 * 2 ^ 59
def prefixEnd_5423447 : Nat := 4983230072969 + 3 ^ 40 * 5423447 * 2
def baseEnd_5423447 : Nat := 928278371728315824123509

theorem tailTrace_5423447 : CollatzResearch.WordTrace tailWord_5423447 prefixEnd_5423447 928278371728315824123509 := by
  unfold tailWord_5423447
  simp only [CollatzResearch.WordTrace]
  refine ⟨197809362782785244850100595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131872908521856829900067063 197809362782785244850100595)
  ·
    refine ⟨296714044174177867275150893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197809362782785244850100595 296714044174177867275150893)
    ·
      refine ⟨111267766565316700228181585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296714044174177867275150893 111267766565316700228181585)
      ·
        refine ⟨83450824923987525171136189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111267766565316700228181585 83450824923987525171136189)
        ·
          refine ⟨31294059346495321939176071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83450824923987525171136189 31294059346495321939176071)
          ·
            refine ⟨46941089019742982908764107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31294059346495321939176071 46941089019742982908764107)
            ·
              refine ⟨70411633529614474363146161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46941089019742982908764107 70411633529614474363146161)
              ·
                refine ⟨52808725147210855772359621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70411633529614474363146161 52808725147210855772359621)
                ·
                  refine ⟨9901635965102035457317429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52808725147210855772359621 9901635965102035457317429)
                  ·
                    refine ⟨928278371728315824123509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901635965102035457317429 928278371728315824123509)
                    ·
                      rfl

theorem cell23_5423447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_5423447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423447 prefixEnd_5423447 := by exact prefixLift 5423447
  have htrace : WordTrace (prefixWord ++ tailWord_5423447) baseStart_5423447 baseEnd_5423447 := by
    simpa [prefixWord, tailWord_5423447, baseEnd_5423447] using wordTrace_append hprefix tailTrace_5423447
  have hstable : (prefixWord ++ tailWord_5423447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423447).length < 2 ^ (prefixWord ++ tailWord_5423447).sum := by decide
  have hdescent : baseEnd_5423447 < baseStart_5423447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423464 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_5423464 : Nat := 118140960795 + 5423464 * 2 ^ 59
def prefixEnd_5423464 : Nat := 4983230072969 + 3 ^ 40 * 5423464 * 2
def baseEnd_5423464 : Nat := 928281281452024635285983

theorem tailTrace_5423464 : CollatzResearch.WordTrace tailWord_5423464 prefixEnd_5423464 928281281452024635285983 := by
  unfold tailWord_5423464
  simp only [CollatzResearch.WordTrace]
  refine ⟨98904991411861828376734723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131873321882482437835646297 98904991411861828376734723)
  ·
    refine ⟨148357487117792742565102085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98904991411861828376734723 148357487117792742565102085)
    ·
      refine ⟨27817028834586139230956641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148357487117792742565102085 27817028834586139230956641)
      ·
        refine ⟨20862771625939604423217481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27817028834586139230956641 20862771625939604423217481)
        ·
          refine ⟨15647078719454703317413111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20862771625939604423217481 15647078719454703317413111)
          ·
            refine ⟨23470618079182054976119667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647078719454703317413111 23470618079182054976119667)
            ·
              refine ⟨35205927118773082464179501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23470618079182054976119667 35205927118773082464179501)
              ·
                refine ⟨13202222669539905924067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35205927118773082464179501 13202222669539905924067313)
                ·
                  refine ⟨9901667002154929443050485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13202222669539905924067313 9901667002154929443050485)
                  ·
                    refine ⟨928281281452024635285983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901667002154929443050485 928281281452024635285983)
                    ·
                      rfl

theorem cell23_5423464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_5423464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423464 prefixEnd_5423464 := by exact prefixLift 5423464
  have htrace : WordTrace (prefixWord ++ tailWord_5423464) baseStart_5423464 baseEnd_5423464 := by
    simpa [prefixWord, tailWord_5423464, baseEnd_5423464] using wordTrace_append hprefix tailTrace_5423464
  have hstable : (prefixWord ++ tailWord_5423464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423464).length < 2 ^ (prefixWord ++ tailWord_5423464).sum := by decide
  have hdescent : baseEnd_5423464 < baseStart_5423464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423467 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 4]
def baseStart_5423467 : Nat := 118140960795 + 5423467 * 2 ^ 59
def prefixEnd_5423467 : Nat := 4983230072969 + 3 ^ 40 * 5423467 * 2
def baseEnd_5423467 : Nat := 2784845384798037394120435

theorem tailTrace_5423467 : CollatzResearch.WordTrace tailWord_5423467 prefixEnd_5423467 2784845384798037394120435 := by
  unfold tailWord_5423467
  simp only [CollatzResearch.WordTrace]
  refine ⟨197810092242712788265828655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131873394828475192177219103 197810092242712788265828655)
  ·
    refine ⟨296715138364069182398742983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197810092242712788265828655 296715138364069182398742983)
    ·
      refine ⟨445072707546103773598114475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296715138364069182398742983 445072707546103773598114475)
      ·
        refine ⟨667609061319155660397171713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445072707546103773598114475 667609061319155660397171713)
        ·
          refine ⟨500706795989366745297878785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667609061319155660397171713 500706795989366745297878785)
          ·
            refine ⟨375530096992025058973409089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500706795989366745297878785 375530096992025058973409089)
            ·
              refine ⟨281647572744018794230056817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375530096992025058973409089 281647572744018794230056817)
              ·
                refine ⟨211235679558014095672542613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281647572744018794230056817 211235679558014095672542613)
                ·
                  refine ⟨9901672479281910734650435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211235679558014095672542613 9901672479281910734650435)
                  ·
                    refine ⟨14852508718922866101975653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9901672479281910734650435 14852508718922866101975653)
                    ·
                      refine ⟨2784845384798037394120435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14852508718922866101975653 2784845384798037394120435)
                      ·
                        rfl

theorem cell23_5423467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 4].length) (baseStart_5423467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423467 prefixEnd_5423467 := by exact prefixLift 5423467
  have htrace : WordTrace (prefixWord ++ tailWord_5423467) baseStart_5423467 baseEnd_5423467 := by
    simpa [prefixWord, tailWord_5423467, baseEnd_5423467] using wordTrace_append hprefix tailTrace_5423467
  have hstable : (prefixWord ++ tailWord_5423467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423467).length < 2 ^ (prefixWord ++ tailWord_5423467).sum := by decide
  have hdescent : baseEnd_5423467 < baseStart_5423467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423518 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5423518 : Nat := 118140960795 + 5423518 * 2 ^ 59
def prefixEnd_5423518 : Nat := 4983230072969 + 3 ^ 40 * 5423518 * 2
def baseEnd_5423518 : Nat := 2784871572311416694582701

theorem tailTrace_5423518 : CollatzResearch.WordTrace tailWord_5423518 prefixEnd_5423518 2784871572311416694582701 := by
  unfold tailWord_5423518
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726494045691002996991901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131874634910352015983956805 24726494045691002996991901)
  ·
    refine ⟨9272435267134126123871963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24726494045691002996991901 9272435267134126123871963)
    ·
      refine ⟨13908652900701189185807945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272435267134126123871963 13908652900701189185807945)
      ·
        refine ⟨10431489675525891889355959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13908652900701189185807945 10431489675525891889355959)
        ·
          refine ⟨15647234513288837834033939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10431489675525891889355959 15647234513288837834033939)
          ·
            refine ⟨23470851769933256751050909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647234513288837834033939 23470851769933256751050909)
            ·
              refine ⟨8801569413724971281644091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23470851769933256751050909 8801569413724971281644091)
              ·
                refine ⟨13202354120587456922466137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801569413724971281644091 13202354120587456922466137)
                ·
                  refine ⟨9901765590440592691849603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13202354120587456922466137 9901765590440592691849603)
                  ·
                    refine ⟨14852648385660889037774405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9901765590440592691849603 14852648385660889037774405)
                    ·
                      refine ⟨2784871572311416694582701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14852648385660889037774405 2784871572311416694582701)
                      ·
                        rfl

theorem cell23_5423518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5423518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423518 prefixEnd_5423518 := by exact prefixLift 5423518
  have htrace : WordTrace (prefixWord ++ tailWord_5423518) baseStart_5423518 baseEnd_5423518 := by
    simpa [prefixWord, tailWord_5423518, baseEnd_5423518] using wordTrace_append hprefix tailTrace_5423518
  have hstable : (prefixWord ++ tailWord_5423518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423518).length < 2 ^ (prefixWord ++ tailWord_5423518).sum := by decide
  have hdescent : baseEnd_5423518 < baseStart_5423518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423584 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 6, 4]
def baseStart_5423584 : Nat := 118140960795 + 5423584 * 2 ^ 59
def prefixEnd_5423584 : Nat := 4983230072969 + 3 ^ 40 * 5423584 * 2
def baseEnd_5423584 : Nat := 928301820678204478785799

theorem tailTrace_5423584 : CollatzResearch.WordTrace tailWord_5423584 prefixEnd_5423584 928301820678204478785799 := by
  unfold tailWord_5423584
  simp only [CollatzResearch.WordTrace]
  refine ⟨98907179791644458623918903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131876239722192611498558537 98907179791644458623918903)
  ·
    refine ⟨148360769687466687935878355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98907179791644458623918903 148360769687466687935878355)
    ·
      refine ⟨222541154531200031903817533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148360769687466687935878355 222541154531200031903817533)
      ·
        refine ⟨83452932949200011963931575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222541154531200031903817533 83452932949200011963931575)
        ·
          refine ⟨125179399423800017945897363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83452932949200011963931575 125179399423800017945897363)
          ·
            refine ⟨187769099135700026918846045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125179399423800017945897363 187769099135700026918846045)
            ·
              refine ⟨70413412175887510094567267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187769099135700026918846045 70413412175887510094567267)
              ·
                refine ⟨105620118263831265141850901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70413412175887510094567267 105620118263831265141850901)
                ·
                  refine ⟨4950943043617090553524261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105620118263831265141850901 4950943043617090553524261)
                  ·
                    refine ⟨928301820678204478785799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4950943043617090553524261 928301820678204478785799)
                    ·
                      rfl

theorem cell23_5423584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_5423584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423584 prefixEnd_5423584 := by exact prefixLift 5423584
  have htrace : WordTrace (prefixWord ++ tailWord_5423584) baseStart_5423584 baseEnd_5423584 := by
    simpa [prefixWord, tailWord_5423584, baseEnd_5423584] using wordTrace_append hprefix tailTrace_5423584
  have hstable : (prefixWord ++ tailWord_5423584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423584).length < 2 ^ (prefixWord ++ tailWord_5423584).sum := by decide
  have hdescent : baseEnd_5423584 < baseStart_5423584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423591 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5423591 : Nat := 118140960795 + 5423591 * 2 ^ 59
def prefixEnd_5423591 : Nat := 4983230072969 + 3 ^ 40 * 5423591 * 2
def baseEnd_5423591 : Nat := 2784909056399194908969865

theorem tailTrace_5423591 : CollatzResearch.WordTrace tailWord_5423591 prefixEnd_5423591 2784909056399194908969865 := by
  unfold tailWord_5423591
  simp only [CollatzResearch.WordTrace]
  refine ⟨197814614894263557443342627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131876409929509038295561751 197814614894263557443342627)
  ·
    refine ⟨296721922341395336165013941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197814614894263557443342627 296721922341395336165013941)
    ·
      refine ⟨27817680219505812765470057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296721922341395336165013941 27817680219505812765470057)
      ·
        refine ⟨20863260164629359574102543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27817680219505812765470057 20863260164629359574102543)
        ·
          refine ⟨31294890246944039361153815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20863260164629359574102543 31294890246944039361153815)
          ·
            refine ⟨46942335370416059041730723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31294890246944039361153815 46942335370416059041730723)
            ·
              refine ⟨70413503055624088562596085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46942335370416059041730723 70413503055624088562596085)
              ·
                refine ⟨6601265911464758302743383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70413503055624088562596085 6601265911464758302743383)
                ·
                  refine ⟨9901898867197137454115075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601265911464758302743383 9901898867197137454115075)
                  ·
                    refine ⟨14852848300795706181172613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9901898867197137454115075 14852848300795706181172613)
                    ·
                      refine ⟨2784909056399194908969865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14852848300795706181172613 2784909056399194908969865)
                      ·
                        rfl

theorem cell23_5423591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5423591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423591 prefixEnd_5423591 := by exact prefixLift 5423591
  have htrace : WordTrace (prefixWord ++ tailWord_5423591) baseStart_5423591 baseEnd_5423591 := by
    simpa [prefixWord, tailWord_5423591, baseEnd_5423591] using wordTrace_append hprefix tailTrace_5423591
  have hstable : (prefixWord ++ tailWord_5423591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423591).length < 2 ^ (prefixWord ++ tailWord_5423591).sum := by decide
  have hdescent : baseEnd_5423591 < baseStart_5423591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423601 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 2, 4]
def baseStart_5423601 : Nat := 118140960795 + 5423601 * 2 ^ 59
def prefixEnd_5423601 : Nat := 4983230072969 + 3 ^ 40 * 5423601 * 2
def baseEnd_5423601 : Nat := 928304730401913289948273

theorem tailTrace_5423601 : CollatzResearch.WordTrace tailWord_5423601 prefixEnd_5423601 928304730401913289948273 := by
  unfold tailWord_5423601
  simp only [CollatzResearch.WordTrace]
  refine ⟨197814979624227329151206657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131876653082818219434137771 197814979624227329151206657)
  ·
    refine ⟨148361234718170496863404993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197814979624227329151206657 148361234718170496863404993)
    ·
      refine ⟨111270926038627872647553745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148361234718170496863404993 111270926038627872647553745)
      ·
        refine ⟨83453194528970904485665309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111270926038627872647553745 83453194528970904485665309)
        ·
          refine ⟨31294947948364089182124491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83453194528970904485665309 31294947948364089182124491)
          ·
            refine ⟨46942421922546133773186737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31294947948364089182124491 46942421922546133773186737)
            ·
              refine ⟨35206816441909600329890053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46942421922546133773186737 35206816441909600329890053)
              ·
                refine ⟨6601278082858050061854385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35206816441909600329890053 6601278082858050061854385)
                ·
                  refine ⟨4950958562143537546390789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601278082858050061854385 4950958562143537546390789)
                  ·
                    refine ⟨928304730401913289948273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4950958562143537546390789 928304730401913289948273)
                    ·
                      rfl

theorem cell23_5423601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_5423601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423601 prefixEnd_5423601 := by exact prefixLift 5423601
  have htrace : WordTrace (prefixWord ++ tailWord_5423601) baseStart_5423601 baseEnd_5423601 := by
    simpa [prefixWord, tailWord_5423601, baseEnd_5423601] using wordTrace_append hprefix tailTrace_5423601
  have hstable : (prefixWord ++ tailWord_5423601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423601).length < 2 ^ (prefixWord ++ tailWord_5423601).sum := by decide
  have hdescent : baseEnd_5423601 < baseStart_5423601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423602 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5423602 : Nat := 118140960795 + 5423602 * 2 ^ 59
def prefixEnd_5423602 : Nat := 4983230072969 + 3 ^ 40 * 5423602 * 2
def baseEnd_5423602 : Nat := 2784914704686394365932315

theorem tailTrace_5423602 : CollatzResearch.WordTrace tailWord_5423602 prefixEnd_5423602 2784914704686394365932315 := by
  unfold tailWord_5423602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49453754024305926580498265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131876677398149137547995373 49453754024305926580498265)
  ·
    refine ⟨37090315518229444935373699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49453754024305926580498265 37090315518229444935373699)
    ·
      refine ⟨55635473277344167403060549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37090315518229444935373699 55635473277344167403060549)
      ·
        refine ⟨10431651239502031388073853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55635473277344167403060549 10431651239502031388073853)
        ·
          refine ⟨3911869214813261770527695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10431651239502031388073853 3911869214813261770527695)
          ·
            refine ⟨5867803822219892655791543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911869214813261770527695 5867803822219892655791543)
            ·
              refine ⟨8801705733329838983687315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867803822219892655791543 8801705733329838983687315)
              ·
                refine ⟨13202558599994758475530973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801705733329838983687315 13202558599994758475530973)
                ·
                  refine ⟨4950959474998034428324115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13202558599994758475530973 4950959474998034428324115)
                  ·
                    refine ⟨7426439212497051642486173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4950959474998034428324115 7426439212497051642486173)
                    ·
                      refine ⟨2784914704686394365932315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426439212497051642486173 2784914704686394365932315)
                      ·
                        rfl

theorem cell23_5423602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5423602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423602 prefixEnd_5423602 := by exact prefixLift 5423602
  have htrace : WordTrace (prefixWord ++ tailWord_5423602) baseStart_5423602 baseEnd_5423602 := by
    simpa [prefixWord, tailWord_5423602, baseEnd_5423602] using wordTrace_append hprefix tailTrace_5423602
  have hstable : (prefixWord ++ tailWord_5423602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423602).length < 2 ^ (prefixWord ++ tailWord_5423602).sum := by decide
  have hdescent : baseEnd_5423602 < baseStart_5423602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423622 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5423622 : Nat := 118140960795 + 5423622 * 2 ^ 59
def prefixEnd_5423622 : Nat := 4983230072969 + 3 ^ 40 * 5423622 * 2
def baseEnd_5423622 : Nat := 928308324766494762560741

theorem tailTrace_5423622 : CollatzResearch.WordTrace tailWord_5423622 prefixEnd_5423622 928308324766494762560741 := by
  unfold tailWord_5423622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181742048660976554303785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131877163704767499825147413 6181742048660976554303785)
  ·
    refine ⟨4636306536495732415727839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6181742048660976554303785 4636306536495732415727839)
    ·
      refine ⟨6954459804743598623591759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636306536495732415727839 6954459804743598623591759)
      ·
        refine ⟨10431689707115397935387639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6954459804743598623591759 10431689707115397935387639)
        ·
          refine ⟨15647534560673096903081459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10431689707115397935387639 15647534560673096903081459)
          ·
            refine ⟨23471301841009645354622189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647534560673096903081459 23471301841009645354622189)
            ·
              refine ⟨8801738190378617007983321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23471301841009645354622189 8801738190378617007983321)
              ·
                refine ⟨6601303642783962755987491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8801738190378617007983321 6601303642783962755987491)
                ·
                  refine ⟨9901955464175944133981237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601303642783962755987491 9901955464175944133981237)
                  ·
                    refine ⟨928308324766494762560741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901955464175944133981237 928308324766494762560741)
                    ·
                      rfl

theorem cell23_5423622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5423622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423622 prefixEnd_5423622 := by exact prefixLift 5423622
  have htrace : WordTrace (prefixWord ++ tailWord_5423622) baseStart_5423622 baseEnd_5423622 := by
    simpa [prefixWord, tailWord_5423622, baseEnd_5423622] using wordTrace_append hprefix tailTrace_5423622
  have hstable : (prefixWord ++ tailWord_5423622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423622).length < 2 ^ (prefixWord ++ tailWord_5423622).sum := by decide
  have hdescent : baseEnd_5423622 < baseStart_5423622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423628 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_5423628 : Nat := 118140960795 + 5423628 * 2 ^ 59
def prefixEnd_5423628 : Nat := 4983230072969 + 3 ^ 40 * 5423628 * 2
def baseEnd_5423628 : Nat := 2784928055183411264207195

theorem tailTrace_5423628 : CollatzResearch.WordTrace tailWord_5423628 prefixEnd_5423628 2784928055183411264207195 := by
  unfold tailWord_5423628
  simp only [CollatzResearch.WordTrace]
  refine ⟨98907982197564756381219769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131877309596753008508293025 98907982197564756381219769)
  ·
    refine ⟨74180986648173567285914827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98907982197564756381219769 74180986648173567285914827)
    ·
      refine ⟨111271479972260350928872241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74180986648173567285914827 111271479972260350928872241)
      ·
        refine ⟨83453609979195263196654181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111271479972260350928872241 83453609979195263196654181)
        ·
          refine ⟨15647551871099111849372659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83453609979195263196654181 15647551871099111849372659)
          ·
            refine ⟨23471327806648667774058989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647551871099111849372659 23471327806648667774058989)
            ·
              refine ⟨8801747927493250415272121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23471327806648667774058989 8801747927493250415272121)
              ·
                refine ⟨6601310945619937811454091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8801747927493250415272121 6601310945619937811454091)
                ·
                  refine ⟨9901966418429906717181137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601310945619937811454091 9901966418429906717181137)
                  ·
                    refine ⟨7426474813822430037885853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9901966418429906717181137 7426474813822430037885853)
                    ·
                      refine ⟨2784928055183411264207195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426474813822430037885853 2784928055183411264207195)
                      ·
                        rfl

theorem cell23_5423628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_5423628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423628 prefixEnd_5423628 := by exact prefixLift 5423628
  have htrace : WordTrace (prefixWord ++ tailWord_5423628) baseStart_5423628 baseEnd_5423628 := by
    simpa [prefixWord, tailWord_5423628, baseEnd_5423628] using wordTrace_append hprefix tailTrace_5423628
  have hstable : (prefixWord ++ tailWord_5423628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423628).length < 2 ^ (prefixWord ++ tailWord_5423628).sum := by decide
  have hdescent : baseEnd_5423628 < baseStart_5423628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423645 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_5423645 : Nat := 118140960795 + 5423645 * 2 ^ 59
def prefixEnd_5423645 : Nat := 4983230072969 + 3 ^ 40 * 5423645 * 2
def baseEnd_5423645 : Nat := 2784936784354537697694617

theorem tailTrace_5423645 : CollatzResearch.WordTrace tailWord_5423645 prefixEnd_5423645 2784936784354537697694617 := by
  unfold tailWord_5423645
  simp only [CollatzResearch.WordTrace]
  refine ⟨197816584436067924665808389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131877722957378616443872259 197816584436067924665808389)
  ·
    refine ⟨37090609581762735874839073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197816584436067924665808389 37090609581762735874839073)
    ·
      refine ⟨27817957186322051906129305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37090609581762735874839073 27817957186322051906129305)
      ·
        refine ⟨20863467889741538929596979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27817957186322051906129305 20863467889741538929596979)
        ·
          refine ⟨31295201834612308394395469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20863467889741538929596979 31295201834612308394395469)
          ·
            refine ⟨11735700687979615647898301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31295201834612308394395469 11735700687979615647898301)
            ·
              refine ⟨4400887757992355867961863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11735700687979615647898301 4400887757992355867961863)
              ·
                refine ⟨6601331636988533801942795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400887757992355867961863 6601331636988533801942795)
                ·
                  refine ⟨9901997455482800702914193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601331636988533801942795 9901997455482800702914193)
                  ·
                    refine ⟨7426498091612100527185645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9901997455482800702914193 7426498091612100527185645)
                    ·
                      refine ⟨2784936784354537697694617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426498091612100527185645 2784936784354537697694617)
                      ·
                        rfl

theorem cell23_5423645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_5423645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423645 prefixEnd_5423645 := by exact prefixLift 5423645
  have htrace : WordTrace (prefixWord ++ tailWord_5423645) baseStart_5423645 baseEnd_5423645 := by
    simpa [prefixWord, tailWord_5423645, baseEnd_5423645] using wordTrace_append hprefix tailTrace_5423645
  have hstable : (prefixWord ++ tailWord_5423645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423645).length < 2 ^ (prefixWord ++ tailWord_5423645).sum := by decide
  have hdescent : baseEnd_5423645 < baseStart_5423645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423664 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_5423664 : Nat := 118140960795 + 5423664 * 2 ^ 59
def prefixEnd_5423664 : Nat := 4983230072969 + 3 ^ 40 * 5423664 * 2
def baseEnd_5423664 : Nat := 2784946540486973123357029

theorem tailTrace_5423664 : CollatzResearch.WordTrace tailWord_5423664 prefixEnd_5423664 2784946540486973123357029 := by
  unfold tailWord_5423664
  simp only [CollatzResearch.WordTrace]
  refine ⟨98908638711499545455375023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131878184948666060607166697 98908638711499545455375023)
  ·
    refine ⟨148362958067249318183062535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98908638711499545455375023 148362958067249318183062535)
    ·
      refine ⟨222544437100873977274593803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148362958067249318183062535 222544437100873977274593803)
      ·
        refine ⟨333816655651310965911890705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222544437100873977274593803 333816655651310965911890705)
        ·
          refine ⟨250362491738483224433918029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333816655651310965911890705 250362491738483224433918029)
          ·
            refine ⟨93885934401931209162719261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250362491738483224433918029 93885934401931209162719261)
            ·
              refine ⟨35207225400724203436019723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93885934401931209162719261 35207225400724203436019723)
              ·
                refine ⟨52810838101086305154029585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35207225400724203436019723 52810838101086305154029585)
                ·
                  refine ⟨39608128575814728865522189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52810838101086305154029585 39608128575814728865522189)
                  ·
                    refine ⟨14853048215930523324570821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39608128575814728865522189 14853048215930523324570821)
                    ·
                      refine ⟨2784946540486973123357029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14853048215930523324570821 2784946540486973123357029)
                      ·
                        rfl

theorem cell23_5423664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_5423664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423664 prefixEnd_5423664 := by exact prefixLift 5423664
  have htrace : WordTrace (prefixWord ++ tailWord_5423664) baseStart_5423664 baseEnd_5423664 := by
    simpa [prefixWord, tailWord_5423664, baseEnd_5423664] using wordTrace_append hprefix tailTrace_5423664
  have hstable : (prefixWord ++ tailWord_5423664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423664).length < 2 ^ (prefixWord ++ tailWord_5423664).sum := by decide
  have hdescent : baseEnd_5423664 < baseStart_5423664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423674 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_5423674 : Nat := 118140960795 + 5423674 * 2 ^ 59
def prefixEnd_5423674 : Nat := 4983230072969 + 3 ^ 40 * 5423674 * 2
def baseEnd_5423674 : Nat := 928317225097839361410661

theorem tailTrace_5423674 : CollatzResearch.WordTrace tailWord_5423674 prefixEnd_5423674 928317225097839361410661 := by
  unfold tailWord_5423674
  simp only [CollatzResearch.WordTrace]
  refine ⟨49454410538240715654653519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131878428101975241745742717 49454410538240715654653519)
  ·
    refine ⟨74181615807361073481980279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49454410538240715654653519 74181615807361073481980279)
    ·
      refine ⟨111272423711041610222970419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74181615807361073481980279 111272423711041610222970419)
      ·
        refine ⟨166908635566562415334455629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111272423711041610222970419 166908635566562415334455629)
        ·
          refine ⟨62590738337460905750420861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166908635566562415334455629 62590738337460905750420861)
          ·
            refine ⟨23471526876547839656407823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62590738337460905750420861 23471526876547839656407823)
            ·
              refine ⟨35207290314821759484611735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23471526876547839656407823 35207290314821759484611735)
              ·
                refine ⟨52810935472232639226917603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35207290314821759484611735 52810935472232639226917603)
                ·
                  refine ⟨79216403208348958840376405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52810935472232639226917603 79216403208348958840376405)
                  ·
                    refine ⟨928317225097839361410661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79216403208348958840376405 928317225097839361410661)
                    ·
                      rfl

theorem cell23_5423674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_5423674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423674 prefixEnd_5423674 := by exact prefixLift 5423674
  have htrace : WordTrace (prefixWord ++ tailWord_5423674) baseStart_5423674 baseEnd_5423674 := by
    simpa [prefixWord, tailWord_5423674, baseEnd_5423674] using wordTrace_append hprefix tailTrace_5423674
  have hstable : (prefixWord ++ tailWord_5423674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423674).length < 2 ^ (prefixWord ++ tailWord_5423674).sum := by decide
  have hdescent : baseEnd_5423674 < baseStart_5423674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423698 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_5423698 : Nat := 118140960795 + 5423698 * 2 ^ 59
def prefixEnd_5423698 : Nat := 4983230072969 + 3 ^ 40 * 5423698 * 2
def baseEnd_5423698 : Nat := 2784963998829225990331873

theorem tailTrace_5423698 : CollatzResearch.WordTrace tailWord_5423698 prefixEnd_5423698 2784963998829225990331873 := by
  unfold tailWord_5423698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49454629376218978679371937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131879011669917276478325165 49454629376218978679371937)
  ·
    refine ⟨37090972032164234009528953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49454629376218978679371937 37090972032164234009528953)
    ·
      refine ⟨27818229024123175507146715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37090972032164234009528953 27818229024123175507146715)
      ·
        refine ⟨41727343536184763260720073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27818229024123175507146715 41727343536184763260720073)
        ·
          refine ⟨31295507652138572445540055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41727343536184763260720073 31295507652138572445540055)
          ·
            refine ⟨46943261478207858668310083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31295507652138572445540055 46943261478207858668310083)
            ·
              refine ⟨70414892217311788002465125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46943261478207858668310083 70414892217311788002465125)
              ·
                refine ⟨13202792290745960250462211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70414892217311788002465125 13202792290745960250462211)
                ·
                  refine ⟨19804188436118940375693317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13202792290745960250462211 19804188436118940375693317)
                  ·
                    refine ⟨3713285331772301320442497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19804188436118940375693317 3713285331772301320442497)
                    ·
                      refine ⟨2784963998829225990331873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713285331772301320442497 2784963998829225990331873)
                      ·
                        rfl

theorem cell23_5423698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_5423698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423698 prefixEnd_5423698 := by exact prefixLift 5423698
  have htrace : WordTrace (prefixWord ++ tailWord_5423698) baseStart_5423698 baseEnd_5423698 := by
    simpa [prefixWord, tailWord_5423698, baseEnd_5423698] using wordTrace_append hprefix tailTrace_5423698
  have hstable : (prefixWord ++ tailWord_5423698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423698).length < 2 ^ (prefixWord ++ tailWord_5423698).sum := by decide
  have hdescent : baseEnd_5423698 < baseStart_5423698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423751 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 2, 5]
def baseStart_5423751 : Nat := 118140960795 + 5423751 * 2 ^ 59
def prefixEnd_5423751 : Nat := 4983230072969 + 3 ^ 40 * 5423751 * 2
def baseEnd_5423751 : Nat := 928330404434638094323043

theorem tailTrace_5423751 : CollatzResearch.WordTrace tailWord_5423751 prefixEnd_5423751 928330404434638094323043 := by
  unfold tailWord_5423751
  simp only [CollatzResearch.WordTrace]
  refine ⟨197820450573683904769167107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131880300382455936512778071 197820450573683904769167107)
  ·
    refine ⟨296730675860525857153750661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197820450573683904769167107 296730675860525857153750661)
    ·
      refine ⟨55637001723848598216328249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296730675860525857153750661 55637001723848598216328249)
      ·
        refine ⟨41727751292886448662246187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55637001723848598216328249 41727751292886448662246187)
        ·
          refine ⟨62591626939329672993369281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41727751292886448662246187 62591626939329672993369281)
          ·
            refine ⟨46943720204497254745026961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62591626939329672993369281 46943720204497254745026961)
            ·
              refine ⟨35207790153372941058770221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46943720204497254745026961 35207790153372941058770221)
              ·
                refine ⟨13202921307514852897038833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35207790153372941058770221 13202921307514852897038833)
                ·
                  refine ⟨9902190980636139672779125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13202921307514852897038833 9902190980636139672779125)
                  ·
                    refine ⟨928330404434638094323043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9902190980636139672779125 928330404434638094323043)
                    ·
                      rfl

theorem cell23_5423751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_5423751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423751 prefixEnd_5423751 := by exact prefixLift 5423751
  have htrace : WordTrace (prefixWord ++ tailWord_5423751) baseStart_5423751 baseEnd_5423751 := by
    simpa [prefixWord, tailWord_5423751, baseEnd_5423751] using wordTrace_append hprefix tailTrace_5423751
  have hstable : (prefixWord ++ tailWord_5423751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423751).length < 2 ^ (prefixWord ++ tailWord_5423751).sum := by decide
  have hdescent : baseEnd_5423751 < baseStart_5423751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423783 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5423783 : Nat := 118140960795 + 5423783 * 2 ^ 59
def prefixEnd_5423783 : Nat := 4983230072969 + 3 ^ 40 * 5423783 * 2
def baseEnd_5423783 : Nat := 2785007644684858157768983

theorem tailTrace_5423783 : CollatzResearch.WordTrace tailWord_5423783 prefixEnd_5423783 2785007644684858157768983 := by
  unfold tailWord_5423783
  simp only [CollatzResearch.WordTrace]
  refine ⟨197821617709567974234332003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131881078473045316156221335 197821617709567974234332003)
  ·
    refine ⟨296732426564351961351498005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197821617709567974234332003 296732426564351961351498005)
    ·
      refine ⟨13909332495203998188351469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 296732426564351961351498005 13909332495203998188351469)
      ·
        refine ⟨5215999685701499320631801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13909332495203998188351469 5215999685701499320631801)
        ·
          refine ⟨3911999764276124490473851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5215999685701499320631801 3911999764276124490473851)
          ·
            refine ⟨5867999646414186735710777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911999764276124490473851 5867999646414186735710777)
            ·
              refine ⟨4400999734810640051783083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5867999646414186735710777 4400999734810640051783083)
              ·
                refine ⟨6601499602215960077674625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400999734810640051783083 6601499602215960077674625)
                ·
                  refine ⟨4951124701661970058255969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601499602215960077674625 4951124701661970058255969)
                  ·
                    refine ⟨3713343526246477543691977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4951124701661970058255969 3713343526246477543691977)
                    ·
                      refine ⟨2785007644684858157768983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713343526246477543691977 2785007644684858157768983)
                      ·
                        rfl

theorem cell23_5423783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5423783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423783 prefixEnd_5423783 := by exact prefixLift 5423783
  have htrace : WordTrace (prefixWord ++ tailWord_5423783) baseStart_5423783 baseEnd_5423783 := by
    simpa [prefixWord, tailWord_5423783, baseEnd_5423783] using wordTrace_append hprefix tailTrace_5423783
  have hstable : (prefixWord ++ tailWord_5423783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423783).length < 2 ^ (prefixWord ++ tailWord_5423783).sum := by decide
  have hdescent : baseEnd_5423783 < baseStart_5423783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423808 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_5423808 : Nat := 118140960795 + 5423808 * 2 ^ 59
def prefixEnd_5423808 : Nat := 4983230072969 + 3 ^ 40 * 5423808 * 2
def baseEnd_5423808 : Nat := 2785020481701220559956367

theorem tailTrace_5423808 : CollatzResearch.WordTrace tailWord_5423808 prefixEnd_5423808 2785020481701220559956367 := by
  unfold tailWord_5423808
  simp only [CollatzResearch.WordTrace]
  refine ⟨98911264767238701751996039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131881686356318269002661385 98911264767238701751996039)
  ·
    refine ⟨148366897150858052627994059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98911264767238701751996039 148366897150858052627994059)
    ·
      refine ⟨222550345726287078941991089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148366897150858052627994059 222550345726287078941991089)
      ·
        refine ⟨166912759294715309206493317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222550345726287078941991089 166912759294715309206493317)
        ·
          refine ⟨31296142367759120476217497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166912759294715309206493317 31296142367759120476217497)
          ·
            refine ⟨23472106775819340357163123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31296142367759120476217497 23472106775819340357163123)
            ·
              refine ⟨35208160163729010535744685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23472106775819340357163123 35208160163729010535744685)
              ·
                refine ⟨13203060061398378950904257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35208160163729010535744685 13203060061398378950904257)
                ·
                  refine ⟨9902295046048784213178193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13203060061398378950904257 9902295046048784213178193)
                  ·
                    refine ⟨7426721284536588159883645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9902295046048784213178193 7426721284536588159883645)
                    ·
                      refine ⟨2785020481701220559956367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426721284536588159883645 2785020481701220559956367)
                      ·
                        rfl

theorem cell23_5423808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_5423808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423808 prefixEnd_5423808 := by exact prefixLift 5423808
  have htrace : WordTrace (prefixWord ++ tailWord_5423808) baseStart_5423808 baseEnd_5423808 := by
    simpa [prefixWord, tailWord_5423808, baseEnd_5423808] using wordTrace_append hprefix tailTrace_5423808
  have hstable : (prefixWord ++ tailWord_5423808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423808).length < 2 ^ (prefixWord ++ tailWord_5423808).sum := by decide
  have hdescent : baseEnd_5423808 < baseStart_5423808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423832 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 1, 4]
def baseStart_5423832 : Nat := 118140960795 + 5423832 * 2 ^ 59
def prefixEnd_5423832 : Nat := 4983230072969 + 3 ^ 40 * 5423832 * 2
def baseEnd_5423832 : Nat := 928344268412309488685419

theorem tailTrace_5423832 : CollatzResearch.WordTrace tailWord_5423832 prefixEnd_5423832 928344268412309488685419 := by
  unfold tailWord_5423832
  simp only [CollatzResearch.WordTrace]
  refine ⟨98911702443195227801432875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131882269924260303735243833 98911702443195227801432875)
  ·
    refine ⟨148367553664792841702149313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98911702443195227801432875 148367553664792841702149313)
    ·
      refine ⟨111275665248594631276611985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148367553664792841702149313 111275665248594631276611985)
      ·
        refine ⟨83456748936445973457458989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111275665248594631276611985 83456748936445973457458989)
        ·
          refine ⟨31296280851167240046547121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83456748936445973457458989 31296280851167240046547121)
          ·
            refine ⟨23472210638375430034910341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31296280851167240046547121 23472210638375430034910341)
            ·
              refine ⟨4401039494695393131545689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23472210638375430034910341 4401039494695393131545689)
              ·
                refine ⟨3300779621021544848659267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401039494695393131545689 3300779621021544848659267)
                ·
                  refine ⟨4951169431532317272988901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300779621021544848659267 4951169431532317272988901)
                  ·
                    refine ⟨928344268412309488685419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951169431532317272988901 928344268412309488685419)
                    ·
                      rfl

theorem cell23_5423832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_5423832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423832 prefixEnd_5423832 := by exact prefixLift 5423832
  have htrace : WordTrace (prefixWord ++ tailWord_5423832) baseStart_5423832 baseEnd_5423832 := by
    simpa [prefixWord, tailWord_5423832, baseEnd_5423832] using wordTrace_append hprefix tailTrace_5423832
  have hstable : (prefixWord ++ tailWord_5423832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423832).length < 2 ^ (prefixWord ++ tailWord_5423832).sum := by decide
  have hdescent : baseEnd_5423832 < baseStart_5423832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423855 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 3]
def baseStart_5423855 : Nat := 118140960795 + 5423855 * 2 ^ 59
def prefixEnd_5423855 : Nat := 4983230072969 + 3 ^ 40 * 5423855 * 2
def baseEnd_5423855 : Nat := 2785044615291981876068651

theorem tailTrace_5423855 : CollatzResearch.WordTrace tailWord_5423855 prefixEnd_5423855 2785044615291981876068651 := by
  unfold tailWord_5423855
  simp only [CollatzResearch.WordTrace]
  refine ⟨197824243765307130530953019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131882829176871420353968679 197824243765307130530953019)
  ·
    refine ⟨296736365647960695796429529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197824243765307130530953019 296736365647960695796429529)
    ·
      refine ⟨222552274235970521847322147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296736365647960695796429529 222552274235970521847322147)
      ·
        refine ⟨333828411353955782770983221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222552274235970521847322147 333828411353955782770983221)
        ·
          refine ⟨31296413564433354634779677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 333828411353955782770983221 31296413564433354634779677)
          ·
            refine ⟨11736155086662507988042379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31296413564433354634779677 11736155086662507988042379)
            ·
              refine ⟨17604232629993761982063569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11736155086662507988042379 17604232629993761982063569)
              ·
                refine ⟨13203174472495321486547677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17604232629993761982063569 13203174472495321486547677)
                ·
                  refine ⟨4951190427185745557455379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13203174472495321486547677 4951190427185745557455379)
                  ·
                    refine ⟨7426785640778618336183069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951190427185745557455379 7426785640778618336183069)
                    ·
                      refine ⟨2785044615291981876068651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426785640778618336183069 2785044615291981876068651)
                      ·
                        rfl

theorem cell23_5423855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_5423855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423855 prefixEnd_5423855 := by exact prefixLift 5423855
  have htrace : WordTrace (prefixWord ++ tailWord_5423855) baseStart_5423855 baseEnd_5423855 := by
    simpa [prefixWord, tailWord_5423855, baseEnd_5423855] using wordTrace_append hprefix tailTrace_5423855
  have hstable : (prefixWord ++ tailWord_5423855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423855).length < 2 ^ (prefixWord ++ tailWord_5423855).sum := by decide
  have hdescent : baseEnd_5423855 < baseStart_5423855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423858 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_5423858 : Nat := 118140960795 + 5423858 * 2 ^ 59
def prefixEnd_5423858 : Nat := 4983230072969 + 3 ^ 40 * 5423858 * 2
def baseEnd_5423858 : Nat := 928348718577981788110379

theorem tailTrace_5423858 : CollatzResearch.WordTrace tailWord_5423858 prefixEnd_5423858 928348718577981788110379 := by
  unfold tailWord_5423858
  simp only [CollatzResearch.WordTrace]
  refine ⟨49456088296074065510828057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131882902122864174695541485 49456088296074065510828057)
  ·
    refine ⟨37092066222055549133121043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49456088296074065510828057 37092066222055549133121043)
    ·
      refine ⟨55638099333083323699681565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37092066222055549133121043 55638099333083323699681565)
      ·
        refine ⟨20864287249906246387380587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55638099333083323699681565 20864287249906246387380587)
        ·
          refine ⟨31296430874859369581070881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20864287249906246387380587 31296430874859369581070881)
          ·
            refine ⟨23472323156144527185803161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31296430874859369581070881 23472323156144527185803161)
            ·
              refine ⟨17604242367108395389352371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23472323156144527185803161 17604242367108395389352371)
              ·
                refine ⟨26406363550662593084028557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17604242367108395389352371 26406363550662593084028557)
                ·
                  refine ⟨9902386331498472406510709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26406363550662593084028557 9902386331498472406510709)
                  ·
                    refine ⟨928348718577981788110379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9902386331498472406510709 928348718577981788110379)
                    ·
                      rfl

theorem cell23_5423858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_5423858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423858 prefixEnd_5423858 := by exact prefixLift 5423858
  have htrace : WordTrace (prefixWord ++ tailWord_5423858) baseStart_5423858 baseEnd_5423858 := by
    simpa [prefixWord, tailWord_5423858, baseEnd_5423858] using wordTrace_append hprefix tailTrace_5423858
  have hstable : (prefixWord ++ tailWord_5423858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423858).length < 2 ^ (prefixWord ++ tailWord_5423858).sum := by decide
  have hdescent : baseEnd_5423858 < baseStart_5423858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423891 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6]
def baseStart_5423891 : Nat := 118140960795 + 5423891 * 2 ^ 59
def prefixEnd_5423891 : Nat := 4983230072969 + 3 ^ 40 * 5423891 * 2
def baseEnd_5423891 : Nat := 2785063100595543735218485

theorem tailTrace_5423891 : CollatzResearch.WordTrace tailWord_5423891 prefixEnd_5423891 2785063100595543735218485 := by
  unfold tailWord_5423891
  simp only [CollatzResearch.WordTrace]
  refine ⟨197825556793176708679263527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131883704528784472452842351 197825556793176708679263527)
  ·
    refine ⟨296738335189765063018895291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197825556793176708679263527 296738335189765063018895291)
    ·
      refine ⟨445107502784647594528342937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296738335189765063018895291 445107502784647594528342937)
      ·
        refine ⟨333830627088485695896257203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445107502784647594528342937 333830627088485695896257203)
        ·
          refine ⟨500745940632728543844385805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333830627088485695896257203 500745940632728543844385805)
          ·
            refine ⟨187779727737273203941644677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500745940632728543844385805 187779727737273203941644677)
            ·
              refine ⟨35208698950738725739058377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187779727737273203941644677 35208698950738725739058377)
              ·
                refine ⟨26406524213054044304293783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35208698950738725739058377 26406524213054044304293783)
                ·
                  refine ⟨39609786319581066456440675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26406524213054044304293783 39609786319581066456440675)
                  ·
                    refine ⟨59414679479371599684661013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39609786319581066456440675 59414679479371599684661013)
                    ·
                      refine ⟨2785063100595543735218485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59414679479371599684661013 2785063100595543735218485)
                      ·
                        rfl

theorem cell23_5423891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_5423891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423891 prefixEnd_5423891 := by exact prefixLift 5423891
  have htrace : WordTrace (prefixWord ++ tailWord_5423891) baseStart_5423891 baseEnd_5423891 := by
    simpa [prefixWord, tailWord_5423891, baseEnd_5423891] using wordTrace_append hprefix tailTrace_5423891
  have hstable : (prefixWord ++ tailWord_5423891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423891).length < 2 ^ (prefixWord ++ tailWord_5423891).sum := by decide
  have hdescent : baseEnd_5423891 < baseStart_5423891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423898 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_5423898 : Nat := 118140960795 + 5423898 * 2 ^ 59
def prefixEnd_5423898 : Nat := 4983230072969 + 3 ^ 40 * 5423898 * 2
def baseEnd_5423898 : Nat := 2785066694960125207830953

theorem tailTrace_5423898 : CollatzResearch.WordTrace tailWord_5423898 prefixEnd_5423898 2785066694960125207830953 := by
  unfold tailWord_5423898
  simp only [CollatzResearch.WordTrace]
  refine ⟨49456453026037837218692087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131883874736100899249845565 49456453026037837218692087)
  ·
    refine ⟨74184679539056755828038131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49456453026037837218692087 74184679539056755828038131)
    ·
      refine ⟨111277019308585133742057197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74184679539056755828038131 111277019308585133742057197)
      ·
        refine ⟨41728882240719425153271449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111277019308585133742057197 41728882240719425153271449)
        ·
          refine ⟨31296661680539568864953587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41728882240719425153271449 31296661680539568864953587)
          ·
            refine ⟨46944992520809353297430381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31296661680539568864953587 46944992520809353297430381)
            ·
              refine ⟨17604372195303507486536393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46944992520809353297430381 17604372195303507486536393)
              ·
                refine ⟨13203279146477630614902295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17604372195303507486536393 13203279146477630614902295)
                ·
                  refine ⟨19804918719716445922353443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13203279146477630614902295 19804918719716445922353443)
                  ·
                    refine ⟨29707378079574668883530165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19804918719716445922353443 29707378079574668883530165)
                    ·
                      refine ⟨2785066694960125207830953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29707378079574668883530165 2785066694960125207830953)
                      ·
                        rfl

theorem cell23_5423898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_5423898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423898 prefixEnd_5423898 := by exact prefixLift 5423898
  have htrace : WordTrace (prefixWord ++ tailWord_5423898) baseStart_5423898 baseEnd_5423898 := by
    simpa [prefixWord, tailWord_5423898, baseEnd_5423898] using wordTrace_append hprefix tailTrace_5423898
  have hstable : (prefixWord ++ tailWord_5423898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423898).length < 2 ^ (prefixWord ++ tailWord_5423898).sum := by decide
  have hdescent : baseEnd_5423898 < baseStart_5423898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423912 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_5423912 : Nat := 118140960795 + 5423912 * 2 ^ 59
def prefixEnd_5423912 : Nat := 4983230072969 + 3 ^ 40 * 5423912 * 2
def baseEnd_5423912 : Nat := 2785073883689288153055889

theorem tailTrace_5423912 : CollatzResearch.WordTrace tailWord_5423912 prefixEnd_5423912 2785073883689288153055889 := by
  unfold tailWord_5423912
  simp only [CollatzResearch.WordTrace]
  refine ⟨98913161363050314632888995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131884215150733752843851993 98913161363050314632888995)
  ·
    refine ⟨148369742044575471949333493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98913161363050314632888995 148369742044575471949333493)
    ·
      refine ⟨13909663316678950495250015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148369742044575471949333493 13909663316678950495250015)
      ·
        refine ⟨20864494975018425742875023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13909663316678950495250015 20864494975018425742875023)
        ·
          refine ⟨31296742462527638614312535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20864494975018425742875023 31296742462527638614312535)
          ·
            refine ⟨46945113693791457921468803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31296742462527638614312535 46945113693791457921468803)
            ·
              refine ⟨70417670540687186882203205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46945113693791457921468803 70417670540687186882203205)
              ·
                refine ⟨13203313226378847540413101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70417670540687186882203205 13203313226378847540413101)
                ·
                  refine ⟨4951242459892067827654913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13203313226378847540413101 4951242459892067827654913)
                  ·
                    refine ⟨3713431844919050870741185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4951242459892067827654913 3713431844919050870741185)
                    ·
                      refine ⟨2785073883689288153055889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713431844919050870741185 2785073883689288153055889)
                      ·
                        rfl

theorem cell23_5423912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_5423912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423912 prefixEnd_5423912 := by exact prefixLift 5423912
  have htrace : WordTrace (prefixWord ++ tailWord_5423912) baseStart_5423912 baseEnd_5423912 := by
    simpa [prefixWord, tailWord_5423912, baseEnd_5423912] using wordTrace_append hprefix tailTrace_5423912
  have hstable : (prefixWord ++ tailWord_5423912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423912).length < 2 ^ (prefixWord ++ tailWord_5423912).sum := by decide
  have hdescent : baseEnd_5423912 < baseStart_5423912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423928 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_5423928 : Nat := 118140960795 + 5423928 * 2 ^ 59
def prefixEnd_5423928 : Nat := 4983230072969 + 3 ^ 40 * 5423928 * 2
def baseEnd_5423928 : Nat := 2785082099379760090455815

theorem tailTrace_5423928 : CollatzResearch.WordTrace tailWord_5423928 prefixEnd_5423928 2785082099379760090455815 := by
  unfold tailWord_5423928
  simp only [CollatzResearch.WordTrace]
  refine ⟨98913453147021331999180219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131884604196028442665573625 98913453147021331999180219)
  ·
    refine ⟨148370179720531997998770329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98913453147021331999180219 148370179720531997998770329)
    ·
      refine ⟨111277634790398998499077747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148370179720531997998770329 111277634790398998499077747)
      ·
        refine ⟨166916452185598497748616621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111277634790398998499077747 166916452185598497748616621)
        ·
          refine ⟨62593669569599436655731233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166916452185598497748616621 62593669569599436655731233)
          ·
            refine ⟨46945252177199577491798425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62593669569599436655731233 46945252177199577491798425)
            ·
              refine ⟨35208939132899683118848819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46945252177199577491798425 35208939132899683118848819)
              ·
                refine ⟨52813408699349524678273229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35208939132899683118848819 52813408699349524678273229)
                ·
                  refine ⟨19805028262256071754352461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52813408699349524678273229 19805028262256071754352461)
                  ·
                    refine ⟨7426885598346026907882173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19805028262256071754352461 7426885598346026907882173)
                    ·
                      refine ⟨2785082099379760090455815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426885598346026907882173 2785082099379760090455815)
                      ·
                        rfl

theorem cell23_5423928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_5423928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423928 prefixEnd_5423928 := by exact prefixLift 5423928
  have htrace : WordTrace (prefixWord ++ tailWord_5423928) baseStart_5423928 baseEnd_5423928 := by
    simpa [prefixWord, tailWord_5423928, baseEnd_5423928] using wordTrace_append hprefix tailTrace_5423928
  have hstable : (prefixWord ++ tailWord_5423928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423928).length < 2 ^ (prefixWord ++ tailWord_5423928).sum := by decide
  have hdescent : baseEnd_5423928 < baseStart_5423928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423945 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 3]
def baseStart_5423945 : Nat := 118140960795 + 5423945 * 2 ^ 59
def prefixEnd_5423945 : Nat := 4983230072969 + 3 ^ 40 * 5423945 * 2
def baseEnd_5423945 : Nat := 2785090828550886523943237

theorem tailTrace_5423945 : CollatzResearch.WordTrace tailWord_5423945 prefixEnd_5423945 2785090828550886523943237 := by
  unfold tailWord_5423945
  simp only [CollatzResearch.WordTrace]
  refine ⟨197827526334981075901729289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131885017556654050601152859 197827526334981075901729289)
  ·
    refine ⟨148370644751235806926296967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197827526334981075901729289 148370644751235806926296967)
    ·
      refine ⟨222555967126853710389445451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148370644751235806926296967 222555967126853710389445451)
      ·
        refine ⟨333833950690280565584168177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222555967126853710389445451 333833950690280565584168177)
        ·
          refine ⟨250375463017710424188126133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333833950690280565584168177 250375463017710424188126133)
          ·
            refine ⟨23472699657910352267636825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 250375463017710424188126133 23472699657910352267636825)
            ·
              refine ⟨17604524743432764200727619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23472699657910352267636825 17604524743432764200727619)
              ·
                refine ⟨26406787115149146301091429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17604524743432764200727619 26406787115149146301091429)
                ·
                  refine ⟨4951272584090464931454643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26406787115149146301091429 4951272584090464931454643)
                  ·
                    refine ⟨7426908876135697397181965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951272584090464931454643 7426908876135697397181965)
                    ·
                      refine ⟨2785090828550886523943237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426908876135697397181965 2785090828550886523943237)
                      ·
                        rfl

theorem cell23_5423945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_5423945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423945 prefixEnd_5423945 := by exact prefixLift 5423945
  have htrace : WordTrace (prefixWord ++ tailWord_5423945) baseStart_5423945 baseEnd_5423945 := by
    simpa [prefixWord, tailWord_5423945, baseEnd_5423945] using wordTrace_append hprefix tailTrace_5423945
  have hstable : (prefixWord ++ tailWord_5423945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423945).length < 2 ^ (prefixWord ++ tailWord_5423945).sum := by decide
  have hdescent : baseEnd_5423945 < baseStart_5423945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423956 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_5423956 : Nat := 118140960795 + 5423956 * 2 ^ 59
def prefixEnd_5423956 : Nat := 4983230072969 + 3 ^ 40 * 5423956 * 2
def baseEnd_5423956 : Nat := 928365492279361993635229

theorem tailTrace_5423956 : CollatzResearch.WordTrace tailWord_5423956 prefixEnd_5423956 928365492279361993635229 := by
  unfold tailWord_5423956
  simp only [CollatzResearch.WordTrace]
  refine ⟨98913963768970612390189861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131885285025294149853586481 98913963768970612390189861)
  ·
    refine ⟨18546368206681989823160599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98913963768970612390189861 18546368206681989823160599)
    ·
      refine ⟨27819552310022984734740899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18546368206681989823160599 27819552310022984734740899)
      ·
        refine ⟨41729328465034477102111349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27819552310022984734740899 41729328465034477102111349)
        ·
          refine ⟨3912124543596982228322939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41729328465034477102111349 3912124543596982228322939)
          ·
            refine ⟨5868186815395473342484409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912124543596982228322939 5868186815395473342484409)
            ·
              refine ⟨4401140111546605006863307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5868186815395473342484409 4401140111546605006863307)
              ·
                refine ⟨6601710167319907510294961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401140111546605006863307 6601710167319907510294961)
                ·
                  refine ⟨4951282625489930632721221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601710167319907510294961 4951282625489930632721221)
                  ·
                    refine ⟨928365492279361993635229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951282625489930632721221 928365492279361993635229)
                    ·
                      rfl

theorem cell23_5423956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_5423956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423956 prefixEnd_5423956 := by exact prefixLift 5423956
  have htrace : WordTrace (prefixWord ++ tailWord_5423956) baseStart_5423956 baseEnd_5423956 := by
    simpa [prefixWord, tailWord_5423956, baseEnd_5423956] using wordTrace_append hprefix tailTrace_5423956
  have hstable : (prefixWord ++ tailWord_5423956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423956).length < 2 ^ (prefixWord ++ tailWord_5423956).sum := by decide
  have hdescent : baseEnd_5423956 < baseStart_5423956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423962 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_5423962 : Nat := 118140960795 + 5423962 * 2 ^ 59
def prefixEnd_5423962 : Nat := 4983230072969 + 3 ^ 40 * 5423962 * 2
def baseEnd_5423962 : Nat := 2785099557722012957430659

theorem tailTrace_5423962 : CollatzResearch.WordTrace tailWord_5423962 prefixEnd_5423962 2785099557722012957430659 := by
  unfold tailWord_5423962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49457036593979871951274535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131885430917279658536732093 49457036593979871951274535)
  ·
    refine ⟨74185554890969807926911803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49457036593979871951274535 74185554890969807926911803)
    ·
      refine ⟨111278332336454711890367705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74185554890969807926911803 111278332336454711890367705)
      ·
        refine ⟨83458749252341033917775779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111278332336454711890367705 83458749252341033917775779)
        ·
          refine ⟨125188123878511550876663669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83458749252341033917775779 125188123878511550876663669)
          ·
            refine ⟨11736386613610457894687219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125188123878511550876663669 11736386613610457894687219)
            ·
              refine ⟨17604579920415686842030829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11736386613610457894687219 17604579920415686842030829)
              ·
                refine ⟨6601717470155882565761561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17604579920415686842030829 6601717470155882565761561)
                ·
                  refine ⟨4951288102616911924321171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601717470155882565761561 4951288102616911924321171)
                  ·
                    refine ⟨7426932153925367886481757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951288102616911924321171 7426932153925367886481757)
                    ·
                      refine ⟨2785099557722012957430659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7426932153925367886481757 2785099557722012957430659)
                      ·
                        rfl

theorem cell23_5423962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_5423962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423962 prefixEnd_5423962 := by exact prefixLift 5423962
  have htrace : WordTrace (prefixWord ++ tailWord_5423962) baseStart_5423962 baseEnd_5423962 := by
    simpa [prefixWord, tailWord_5423962, baseEnd_5423962] using wordTrace_append hprefix tailTrace_5423962
  have hstable : (prefixWord ++ tailWord_5423962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423962).length < 2 ^ (prefixWord ++ tailWord_5423962).sum := by decide
  have hdescent : baseEnd_5423962 < baseStart_5423962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423972 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_5423972 : Nat := 118140960795 + 5423972 * 2 ^ 59
def prefixEnd_5423972 : Nat := 4983230072969 + 3 ^ 40 * 5423972 * 2
def baseEnd_5423972 : Nat := 2785104692528557918305613

theorem tailTrace_5423972 : CollatzResearch.WordTrace tailWord_5423972 prefixEnd_5423972 2785104692528557918305613 := by
  unfold tailWord_5423972
  simp only [CollatzResearch.WordTrace]
  refine ⟨98914255552941629756481085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131885674070588839675308113 98914255552941629756481085)
  ·
    refine ⟨37092845832353111158680407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98914255552941629756481085 37092845832353111158680407)
    ·
      refine ⟨55639268748529666738020611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37092845832353111158680407 55639268748529666738020611)
      ·
        refine ⟨83458903122794500107030917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55639268748529666738020611 83458903122794500107030917)
        ·
          refine ⟨15648544335523968770068297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83458903122794500107030917 15648544335523968770068297)
          ·
            refine ⟨11736408251642976577551223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15648544335523968770068297 11736408251642976577551223)
            ·
              refine ⟨17604612377464464866326835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11736408251642976577551223 17604612377464464866326835)
              ·
                refine ⟨26406918566196697299490253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17604612377464464866326835 26406918566196697299490253)
                ·
                  refine ⟨9902594462323761487308845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26406918566196697299490253 9902594462323761487308845)
                  ·
                    refine ⟨3713472923371410557740817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9902594462323761487308845 3713472923371410557740817)
                    ·
                      refine ⟨2785104692528557918305613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713472923371410557740817 2785104692528557918305613)
                      ·
                        rfl

theorem cell23_5423972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_5423972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423972 prefixEnd_5423972 := by exact prefixLift 5423972
  have htrace : WordTrace (prefixWord ++ tailWord_5423972) baseStart_5423972 baseEnd_5423972 := by
    simpa [prefixWord, tailWord_5423972, baseEnd_5423972] using wordTrace_append hprefix tailTrace_5423972
  have hstable : (prefixWord ++ tailWord_5423972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423972).length < 2 ^ (prefixWord ++ tailWord_5423972).sum := by decide
  have hdescent : baseEnd_5423972 < baseStart_5423972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5423985 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 3, 4, 2]
def baseStart_5423985 : Nat := 118140960795 + 5423985 * 2 ^ 59
def prefixEnd_5423985 : Nat := 4983230072969 + 3 ^ 40 * 5423985 * 2
def baseEnd_5423985 : Nat := 2785111367777066367443053

theorem tailTrace_5423985 : CollatzResearch.WordTrace tailWord_5423985 prefixEnd_5423985 2785111367777066367443053 := by
  unfold tailWord_5423985
  simp only [CollatzResearch.WordTrace]
  refine ⟨197828985254836162733185409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131885990169890775155456939 197828985254836162733185409)
  ·
    refine ⟨148371738941127122049889057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197828985254836162733185409 148371738941127122049889057)
    ·
      refine ⟨111278804205845341537416793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148371738941127122049889057 111278804205845341537416793)
      ·
        refine ⟨83459103154384006153062595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111278804205845341537416793 83459103154384006153062595)
        ·
          refine ⟨125188654731576009229593893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83459103154384006153062595 125188654731576009229593893)
          ·
            refine ⟨23472872762170501730548855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125188654731576009229593893 23472872762170501730548855)
            ·
              refine ⟨35209309143255752595823283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23472872762170501730548855 35209309143255752595823283)
              ·
                refine ⟨52813963714883628893734925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35209309143255752595823283 52813963714883628893734925)
                ·
                  refine ⟨19805236393081360835150597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52813963714883628893734925 19805236393081360835150597)
                  ·
                    refine ⟨3713481823702755156590737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19805236393081360835150597 3713481823702755156590737)
                    ·
                      refine ⟨2785111367777066367443053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713481823702755156590737 2785111367777066367443053)
                      ·
                        rfl

theorem cell23_5423985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_5423985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5423985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5423985 prefixEnd_5423985 := by exact prefixLift 5423985
  have htrace : WordTrace (prefixWord ++ tailWord_5423985) baseStart_5423985 baseEnd_5423985 := by
    simpa [prefixWord, tailWord_5423985, baseEnd_5423985] using wordTrace_append hprefix tailTrace_5423985
  have hstable : (prefixWord ++ tailWord_5423985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5423985).length < 2 ^ (prefixWord ++ tailWord_5423985).sum := by decide
  have hdescent : baseEnd_5423985 < baseStart_5423985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5423985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424170 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5424170 : Nat := 118140960795 + 5424170 * 2 ^ 59
def prefixEnd_5424170 : Nat := 4983230072969 + 3 ^ 40 * 5424170 * 2
def baseEnd_5424170 : Nat := 928402120566049381209901

theorem tailTrace_5424170 : CollatzResearch.WordTrace tailWord_5424170 prefixEnd_5424170 928402120566049381209901 := by
  unfold tailWord_5424170
  simp only [CollatzResearch.WordTrace]
  refine ⟨49458933189791484832167491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131890488506110626219113309 49458933189791484832167491)
  ·
    refine ⟨74188399784687227248251237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49458933189791484832167491 74188399784687227248251237)
    ·
      refine ⟨13910324959628855109047107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74188399784687227248251237 13910324959628855109047107)
      ·
        refine ⟨20865487439443282663570661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13910324959628855109047107 20865487439443282663570661)
        ·
          refine ⟨3912278894895615499419499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20865487439443282663570661 3912278894895615499419499)
          ·
            refine ⟨5868418342343423249129249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912278894895615499419499 5868418342343423249129249)
            ·
              refine ⟨4401313756757567436846937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5868418342343423249129249 4401313756757567436846937)
              ·
                refine ⟨3300985317568175577635203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401313756757567436846937 3300985317568175577635203)
                ·
                  refine ⟨4951477976352263366452805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300985317568175577635203 4951477976352263366452805)
                  ·
                    refine ⟨928402120566049381209901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951477976352263366452805 928402120566049381209901)
                    ·
                      rfl

theorem cell23_5424170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5424170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424170 prefixEnd_5424170 := by exact prefixLift 5424170
  have htrace : WordTrace (prefixWord ++ tailWord_5424170) baseStart_5424170 baseEnd_5424170 := by
    simpa [prefixWord, tailWord_5424170, baseEnd_5424170] using wordTrace_append hprefix tailTrace_5424170
  have hstable : (prefixWord ++ tailWord_5424170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424170).length < 2 ^ (prefixWord ++ tailWord_5424170).sum := by decide
  have hdescent : baseEnd_5424170 < baseStart_5424170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424175 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 8, 4]
def baseStart_5424175 : Nat := 118140960795 + 5424175 * 2 ^ 59
def prefixEnd_5424175 : Nat := 4983230072969 + 3 ^ 40 * 5424175 * 2
def baseEnd_5424175 : Nat := 928402976367140208022393

theorem tailTrace_5424175 : CollatzResearch.WordTrace tailWord_5424175 prefixEnd_5424175 928402976367140208022393 := by
  unfold tailWord_5424175
  simp only [CollatzResearch.WordTrace]
  refine ⟨197835915124147825182601979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131890610082765216788401319 197835915124147825182601979)
  ·
    refine ⟨296753872686221737773902969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197835915124147825182601979 296753872686221737773902969)
    ·
      refine ⟨222565404514666303330427227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296753872686221737773902969 222565404514666303330427227)
      ·
        refine ⟨333848106771999454995640841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222565404514666303330427227 333848106771999454995640841)
        ·
          refine ⟨250386080078999591246730631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333848106771999454995640841 250386080078999591246730631)
          ·
            refine ⟨375579120118499386870095947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250386080078999591246730631 375579120118499386870095947)
            ·
              refine ⟨563368680177749080305143921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375579120118499386870095947 563368680177749080305143921)
              ·
                refine ⟨422526510133311810228857941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563368680177749080305143921 422526510133311810228857941)
                ·
                  refine ⟨4951482540624747776119429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 422526510133311810228857941 4951482540624747776119429)
                  ·
                    refine ⟨928402976367140208022393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951482540624747776119429 928402976367140208022393)
                    ·
                      rfl

theorem cell23_5424175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_5424175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424175 prefixEnd_5424175 := by exact prefixLift 5424175
  have htrace : WordTrace (prefixWord ++ tailWord_5424175) baseStart_5424175 baseEnd_5424175 := by
    simpa [prefixWord, tailWord_5424175, baseEnd_5424175] using wordTrace_append hprefix tailTrace_5424175
  have hstable : (prefixWord ++ tailWord_5424175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424175).length < 2 ^ (prefixWord ++ tailWord_5424175).sum := by decide
  have hdescent : baseEnd_5424175 < baseStart_5424175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424192 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 2, 4]
def baseStart_5424192 : Nat := 118140960795 + 5424192 * 2 ^ 59
def prefixEnd_5424192 : Nat := 4983230072969 + 3 ^ 40 * 5424192 * 2
def baseEnd_5424192 : Nat := 928405886090849019184867

theorem tailTrace_5424192 : CollatzResearch.WordTrace tailWord_5424192 prefixEnd_5424192 928405886090849019184867 := by
  unfold tailWord_5424192
  simp only [CollatzResearch.WordTrace]
  refine ⟨98918267582543118542985415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131891023443390824723980553 98918267582543118542985415)
  ·
    refine ⟨148377401373814677814478123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98918267582543118542985415 148377401373814677814478123)
    ·
      refine ⟨222566102060722016721717185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148377401373814677814478123 222566102060722016721717185)
      ·
        refine ⟨166924576545541512541287889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222566102060722016721717185 166924576545541512541287889)
        ·
          refine ⟨125193432409156134405965917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166924576545541512541287889 125193432409156134405965917)
          ·
            refine ⟨46947537153433550402237219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125193432409156134405965917 46947537153433550402237219)
            ·
              refine ⟨70421305730150325603355829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46947537153433550402237219 70421305730150325603355829)
              ·
                refine ⟨6601997412201593025314609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70421305730150325603355829 6601997412201593025314609)
                ·
                  refine ⟨4951498059151194768985957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601997412201593025314609 4951498059151194768985957)
                  ·
                    refine ⟨928405886090849019184867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951498059151194768985957 928405886090849019184867)
                    ·
                      rfl

theorem cell23_5424192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_5424192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424192 prefixEnd_5424192 := by exact prefixLift 5424192
  have htrace : WordTrace (prefixWord ++ tailWord_5424192) baseStart_5424192 baseEnd_5424192 := by
    simpa [prefixWord, tailWord_5424192, baseEnd_5424192] using wordTrace_append hprefix tailTrace_5424192
  have hstable : (prefixWord ++ tailWord_5424192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424192).length < 2 ^ (prefixWord ++ tailWord_5424192).sum := by decide
  have hdescent : baseEnd_5424192 < baseStart_5424192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424199 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_5424199 : Nat := 118140960795 + 5424199 * 2 ^ 59
def prefixEnd_5424199 : Nat := 4983230072969 + 3 ^ 40 * 5424199 * 2
def baseEnd_5424199 : Nat := 2785221252637128530167069

theorem tailTrace_5424199 : CollatzResearch.WordTrace tailWord_5424199 prefixEnd_5424199 2785221252637128530167069 := by
  unfold tailWord_5424199
  simp only [CollatzResearch.WordTrace]
  refine ⟨197836790476060877281475651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131891193650707251520983767 197836790476060877281475651)
  ·
    refine ⟨296755185714091315922213477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197836790476060877281475651 296755185714091315922213477)
    ·
      refine ⟨55641597321392121735415027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296755185714091315922213477 55641597321392121735415027)
      ·
        refine ⟨83462395982088182603122541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55641597321392121735415027 83462395982088182603122541)
        ·
          refine ⟨31298398493283068476170953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83462395982088182603122541 31298398493283068476170953)
          ·
            refine ⟨23473798869962301357128215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31298398493283068476170953 23473798869962301357128215)
            ·
              refine ⟨35210698304943452035692323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23473798869962301357128215 35210698304943452035692323)
              ·
                refine ⟨52816047457415178053538485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35210698304943452035692323 52816047457415178053538485)
                ·
                  refine ⟨4951504449132672942519233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52816047457415178053538485 4951504449132672942519233)
                  ·
                    refine ⟨3713628336849504706889425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4951504449132672942519233 3713628336849504706889425)
                    ·
                      refine ⟨2785221252637128530167069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713628336849504706889425 2785221252637128530167069)
                      ·
                        rfl

theorem cell23_5424199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_5424199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424199 prefixEnd_5424199 := by exact prefixLift 5424199
  have htrace : WordTrace (prefixWord ++ tailWord_5424199) baseStart_5424199 baseEnd_5424199 := by
    simpa [prefixWord, tailWord_5424199, baseEnd_5424199] using wordTrace_append hprefix tailTrace_5424199
  have hstable : (prefixWord ++ tailWord_5424199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424199).length < 2 ^ (prefixWord ++ tailWord_5424199).sum := by decide
  have hdescent : baseEnd_5424199 < baseStart_5424199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424202 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_5424202 : Nat := 118140960795 + 5424202 * 2 ^ 59
def prefixEnd_5424202 : Nat := 4983230072969 + 3 ^ 40 * 5424202 * 2
def baseEnd_5424202 : Nat := 2785222793079092018429555

theorem tailTrace_5424202 : CollatzResearch.WordTrace tailWord_5424202 prefixEnd_5424202 2785222793079092018429555 := by
  unfold tailWord_5424202
  simp only [CollatzResearch.WordTrace]
  refine ⟨49459224973762502198458715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131891266596700005862556573 49459224973762502198458715)
  ·
    refine ⟨74188837460643753297688073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49459224973762502198458715 74188837460643753297688073)
    ·
      refine ⟨55641628095482814973266055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74188837460643753297688073 55641628095482814973266055)
      ·
        refine ⟨83462442143224222459899083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55641628095482814973266055 83462442143224222459899083)
        ·
          refine ⟨125193663214836333689848625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83462442143224222459899083 125193663214836333689848625)
          ·
            refine ⟨93895247411127250267386469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125193663214836333689848625 93895247411127250267386469)
            ·
              refine ⟨17605358889586359425134963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93895247411127250267386469 17605358889586359425134963)
              ·
                refine ⟨26408038334379539137702445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17605358889586359425134963 26408038334379539137702445)
                ·
                  refine ⟨9903014375392327176638417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26408038334379539137702445 9903014375392327176638417)
                  ·
                    refine ⟨7427260781544245382478813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9903014375392327176638417 7427260781544245382478813)
                    ·
                      refine ⟨2785222793079092018429555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7427260781544245382478813 2785222793079092018429555)
                      ·
                        rfl

theorem cell23_5424202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_5424202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424202 prefixEnd_5424202 := by exact prefixLift 5424202
  have htrace : WordTrace (prefixWord ++ tailWord_5424202) baseStart_5424202 baseEnd_5424202 := by
    simpa [prefixWord, tailWord_5424202, baseEnd_5424202] using wordTrace_append hprefix tailTrace_5424202
  have hstable : (prefixWord ++ tailWord_5424202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424202).length < 2 ^ (prefixWord ++ tailWord_5424202).sum := by decide
  have hdescent : baseEnd_5424202 < baseStart_5424202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424212 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_5424212 : Nat := 118140960795 + 5424212 * 2 ^ 59
def prefixEnd_5424212 : Nat := 4983230072969 + 3 ^ 40 * 5424212 * 2
def baseEnd_5424212 : Nat := 2785227927885636979304509

theorem tailTrace_5424212 : CollatzResearch.WordTrace tailWord_5424212 prefixEnd_5424212 2785227927885636979304509 := by
  unfold tailWord_5424212
  simp only [CollatzResearch.WordTrace]
  refine ⟨98918632312506890250849445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131891509750009187001132593 98918632312506890250849445)
  ·
    refine ⟨18547243558595041922034271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98918632312506890250849445 18547243558595041922034271)
    ·
      refine ⟨27820865337892562883051407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18547243558595041922034271 27820865337892562883051407)
      ·
        refine ⟨41731298006838844324577111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27820865337892562883051407 41731298006838844324577111)
        ·
          refine ⟨62596947010258266486865667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41731298006838844324577111 62596947010258266486865667)
          ·
            refine ⟨93895420515387399730298501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62596947010258266486865667 93895420515387399730298501)
            ·
              refine ⟨17605391346635137449430969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93895420515387399730298501 17605391346635137449430969)
              ·
                refine ⟨13204043509976353087073227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17605391346635137449430969 13204043509976353087073227)
                ·
                  refine ⟨19806065264964529630609841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13204043509976353087073227 19806065264964529630609841)
                  ·
                    refine ⟨14854548948723397222957381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19806065264964529630609841 14854548948723397222957381)
                    ·
                      refine ⟨2785227927885636979304509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14854548948723397222957381 2785227927885636979304509)
                      ·
                        rfl

theorem cell23_5424212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_5424212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424212 prefixEnd_5424212 := by exact prefixLift 5424212
  have htrace : WordTrace (prefixWord ++ tailWord_5424212) baseStart_5424212 baseEnd_5424212 := by
    simpa [prefixWord, tailWord_5424212, baseEnd_5424212] using wordTrace_append hprefix tailTrace_5424212
  have hstable : (prefixWord ++ tailWord_5424212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424212).length < 2 ^ (prefixWord ++ tailWord_5424212).sum := by decide
  have hdescent : baseEnd_5424212 < baseStart_5424212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424226 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5424226 : Nat := 118140960795 + 5424226 * 2 ^ 59
def prefixEnd_5424226 : Nat := 4983230072969 + 3 ^ 40 * 5424226 * 2
def baseEnd_5424226 : Nat := 928411705538266641509815

theorem tailTrace_5424226 : CollatzResearch.WordTrace tailWord_5424226 prefixEnd_5424226 928411705538266641509815 := by
  unfold tailWord_5424226
  simp only [CollatzResearch.WordTrace]
  refine ⟨49459443811740765223177133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131891850164642040595139021 49459443811740765223177133)
  ·
    refine ⟨18547291429402786958691425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49459443811740765223177133 18547291429402786958691425)
    ·
      refine ⟨13910468572052090219018569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18547291429402786958691425 13910468572052090219018569)
      ·
        refine ⟨10432851429039067664263927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13910468572052090219018569 10432851429039067664263927)
        ·
          refine ⟨15649277143558601496395891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10432851429039067664263927 15649277143558601496395891)
          ·
            refine ⟨23473915715337902244593837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15649277143558601496395891 23473915715337902244593837)
            ·
              refine ⟨8802718393251713341722689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23473915715337902244593837 8802718393251713341722689)
              ·
                refine ⟨6602038794938785006292017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8802718393251713341722689 6602038794938785006292017)
                ·
                  refine ⟨4951529096204088754719013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6602038794938785006292017 4951529096204088754719013)
                  ·
                    refine ⟨928411705538266641509815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951529096204088754719013 928411705538266641509815)
                    ·
                      rfl

theorem cell23_5424226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5424226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424226 prefixEnd_5424226 := by exact prefixLift 5424226
  have htrace : WordTrace (prefixWord ++ tailWord_5424226) baseStart_5424226 baseEnd_5424226 := by
    simpa [prefixWord, tailWord_5424226, baseEnd_5424226] using wordTrace_append hprefix tailTrace_5424226
  have hstable : (prefixWord ++ tailWord_5424226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424226).length < 2 ^ (prefixWord ++ tailWord_5424226).sum := by decide
  have hdescent : baseEnd_5424226 < baseStart_5424226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424275 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_5424275 : Nat := 118140960795 + 5424275 * 2 ^ 59
def prefixEnd_5424275 : Nat := 4983230072969 + 3 ^ 40 * 5424275 * 2
def baseEnd_5424275 : Nat := 2785260277166870232816719

theorem tailTrace_5424275 : CollatzResearch.WordTrace tailWord_5424275 prefixEnd_5424275 2785260277166870232816719 := by
  unfold tailWord_5424275
  simp only [CollatzResearch.WordTrace]
  refine ⟨197839562423785542261242279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131893041615857028174161519 197839562423785542261242279)
  ·
    refine ⟨296759343635678313391863419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197839562423785542261242279 296759343635678313391863419)
    ·
      refine ⟨445139015453517470087795129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296759343635678313391863419 445139015453517470087795129)
      ·
        refine ⟨333854261590138102565846347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445139015453517470087795129 333854261590138102565846347)
        ·
          refine ⟨500781392385207153848769521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333854261590138102565846347 500781392385207153848769521)
          ·
            refine ⟨375586044288905365386577141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500781392385207153848769521 375586044288905365386577141)
            ·
              refine ⟨35211191652084878004991607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 375586044288905365386577141 35211191652084878004991607)
              ·
                refine ⟨52816787478127317007487411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35211191652084878004991607 52816787478127317007487411)
                ·
                  refine ⟨79225181217190975511231117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52816787478127317007487411 79225181217190975511231117)
                  ·
                    refine ⟨29709442956446615816711669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79225181217190975511231117 29709442956446615816711669)
                    ·
                      refine ⟨2785260277166870232816719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29709442956446615816711669 2785260277166870232816719)
                      ·
                        rfl

theorem cell23_5424275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_5424275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424275 prefixEnd_5424275 := by exact prefixLift 5424275
  have htrace : WordTrace (prefixWord ++ tailWord_5424275) baseStart_5424275 baseEnd_5424275 := by
    simpa [prefixWord, tailWord_5424275, baseEnd_5424275] using wordTrace_append hprefix tailTrace_5424275
  have hstable : (prefixWord ++ tailWord_5424275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424275).length < 2 ^ (prefixWord ++ tailWord_5424275).sum := by decide
  have hdescent : baseEnd_5424275 < baseStart_5424275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424310 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5424310 : Nat := 118140960795 + 5424310 * 2 ^ 59
def prefixEnd_5424310 : Nat := 4983230072969 + 3 ^ 40 * 5424310 * 2
def baseEnd_5424310 : Nat := 2785278248989777595879059

theorem tailTrace_5424310 : CollatzResearch.WordTrace tailWord_5424310 prefixEnd_5424310 2785278248989777595879059 := by
  unfold tailWord_5424310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12365052436166171452422899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131893892652439162159177589 12365052436166171452422899)
  ·
    refine ⟨18547578654249257178634349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12365052436166171452422899 18547578654249257178634349)
    ·
      refine ⟨6955341995343471441987881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18547578654249257178634349 6955341995343471441987881)
      ·
        refine ⟨5216506496507603581490911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6955341995343471441987881 5216506496507603581490911)
        ·
          refine ⟨7824759744761405372236367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216506496507603581490911 7824759744761405372236367)
          ·
            refine ⟨11737139617142108058354551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7824759744761405372236367 11737139617142108058354551)
            ·
              refine ⟨17605709425713162087531827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11737139617142108058354551 17605709425713162087531827)
              ·
                refine ⟨26408564138569743131297741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17605709425713162087531827 26408564138569743131297741)
                ·
                  refine ⟨9903211551963653674236653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26408564138569743131297741 9903211551963653674236653)
                  ·
                    refine ⟨3713704331986370127838745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9903211551963653674236653 3713704331986370127838745)
                    ·
                      refine ⟨2785278248989777595879059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713704331986370127838745 2785278248989777595879059)
                      ·
                        rfl

theorem cell23_5424310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5424310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424310 prefixEnd_5424310 := by exact prefixLift 5424310
  have htrace : WordTrace (prefixWord ++ tailWord_5424310) baseStart_5424310 baseEnd_5424310 := by
    simpa [prefixWord, tailWord_5424310, baseEnd_5424310] using wordTrace_append hprefix tailTrace_5424310
  have hstable : (prefixWord ++ tailWord_5424310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424310).length < 2 ^ (prefixWord ++ tailWord_5424310).sum := by decide
  have hdescent : baseEnd_5424310 < baseStart_5424310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424352 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_5424352 : Nat := 118140960795 + 5424352 * 2 ^ 59
def prefixEnd_5424352 : Nat := 4983230072969 + 3 ^ 40 * 5424352 * 2
def baseEnd_5424352 : Nat := 2785299815177266431553865

theorem tailTrace_5424352 : CollatzResearch.WordTrace tailWord_5424352 prefixEnd_5424352 2785299815177266431553865 := by
  unfold tailWord_5424352
  simp only [CollatzResearch.WordTrace]
  refine ⟨98921185422253292205897655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131894913896337722941196873 98921185422253292205897655)
  ·
    refine ⟨148381778133379938308846483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98921185422253292205897655 148381778133379938308846483)
    ·
      refine ⟨222572667200069907463269725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148381778133379938308846483 222572667200069907463269725)
      ·
        refine ⟨83464750200026215298726147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222572667200069907463269725 83464750200026215298726147)
        ·
          refine ⟨125197125300039322948089221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83464750200026215298726147 125197125300039322948089221)
          ·
            refine ⟨23474460993757373052766729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125197125300039322948089221 23474460993757373052766729)
            ·
              refine ⟨17605845745318029789575047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23474460993757373052766729 17605845745318029789575047)
              ·
                refine ⟨26408768617977044684362571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17605845745318029789575047 26408768617977044684362571)
                ·
                  refine ⟨39613152926965567026543857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26408768617977044684362571 39613152926965567026543857)
                  ·
                    refine ⟨29709864695224175269907893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39613152926965567026543857 29709864695224175269907893)
                    ·
                      refine ⟨2785299815177266431553865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29709864695224175269907893 2785299815177266431553865)
                      ·
                        rfl

theorem cell23_5424352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_5424352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424352 prefixEnd_5424352 := by exact prefixLift 5424352
  have htrace : WordTrace (prefixWord ++ tailWord_5424352) baseStart_5424352 baseEnd_5424352 := by
    simpa [prefixWord, tailWord_5424352, baseEnd_5424352] using wordTrace_append hprefix tailTrace_5424352
  have hstable : (prefixWord ++ tailWord_5424352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424352).length < 2 ^ (prefixWord ++ tailWord_5424352).sum := by decide
  have hdescent : baseEnd_5424352 < baseStart_5424352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424490 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5424490 : Nat := 118140960795 + 5424490 * 2 ^ 59
def prefixEnd_5424490 : Nat := 4983230072969 + 3 ^ 40 * 5424490 * 2
def baseEnd_5424490 : Nat := 2785370675507586891628231

theorem tailTrace_5424490 : CollatzResearch.WordTrace tailWord_5424490 prefixEnd_5424490 2785370675507586891628231 := by
  unfold tailWord_5424490
  simp only [CollatzResearch.WordTrace]
  refine ⟨49461851029501658495079731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131898269412004422653545949 49461851029501658495079731)
  ·
    refine ⟨74192776544252487742619597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49461851029501658495079731 74192776544252487742619597)
    ·
      refine ⟨27822291204094682903482349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74192776544252487742619597 27822291204094682903482349)
      ·
        refine ⟨10433359201535506088805881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27822291204094682903482349 10433359201535506088805881)
        ·
          refine ⟨7825019401151629566604411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10433359201535506088805881 7825019401151629566604411)
          ·
            refine ⟨11737529101727444349906617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825019401151629566604411 11737529101727444349906617)
            ·
              refine ⟨8803146826295583262429963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11737529101727444349906617 8803146826295583262429963)
              ·
                refine ⟨13204720239443374893644945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8803146826295583262429963 13204720239443374893644945)
                ·
                  refine ⟨9903540179582531170233709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13204720239443374893644945 9903540179582531170233709)
                  ·
                    refine ⟨3713827567343449188837641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9903540179582531170233709 3713827567343449188837641)
                    ·
                      refine ⟨2785370675507586891628231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713827567343449188837641 2785370675507586891628231)
                      ·
                        rfl

theorem cell23_5424490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5424490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424490 prefixEnd_5424490 := by exact prefixLift 5424490
  have htrace : WordTrace (prefixWord ++ tailWord_5424490) baseStart_5424490 baseEnd_5424490 := by
    simpa [prefixWord, tailWord_5424490, baseEnd_5424490] using wordTrace_append hprefix tailTrace_5424490
  have hstable : (prefixWord ++ tailWord_5424490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424490).length < 2 ^ (prefixWord ++ tailWord_5424490).sum := by decide
  have hdescent : baseEnd_5424490 < baseStart_5424490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424514 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_5424514 : Nat := 118140960795 + 5424514 * 2 ^ 59
def prefixEnd_5424514 : Nat := 4983230072969 + 3 ^ 40 * 5424514 * 2
def baseEnd_5424514 : Nat := 2785382999043294797728121

theorem tailTrace_5424514 : CollatzResearch.WordTrace tailWord_5424514 prefixEnd_5424514 2785382999043294797728121 := by
  unfold tailWord_5424514
  simp only [CollatzResearch.WordTrace]
  refine ⟨49462069867479921519798149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131898852979946457386128397 49462069867479921519798149)
  ·
    refine ⟨9274138100152485284962153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49462069867479921519798149 9274138100152485284962153)
    ·
      refine ⟨6955603575114363963721615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9274138100152485284962153 6955603575114363963721615)
      ·
        refine ⟨10433405362671545945582423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6955603575114363963721615 10433405362671545945582423)
        ·
          refine ⟨15650108044007318918373635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10433405362671545945582423 15650108044007318918373635)
          ·
            refine ⟨23475162066010978377560453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15650108044007318918373635 23475162066010978377560453)
            ·
              refine ⟨4401592887377058445792585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23475162066010978377560453 4401592887377058445792585)
              ·
                refine ⟨3301194665532793834344439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401592887377058445792585 3301194665532793834344439)
                ·
                  refine ⟨4951791998299190751516659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301194665532793834344439 4951791998299190751516659)
                  ·
                    refine ⟨7427687997448786127274989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951791998299190751516659 7427687997448786127274989)
                    ·
                      refine ⟨2785382999043294797728121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7427687997448786127274989 2785382999043294797728121)
                      ·
                        rfl

theorem cell23_5424514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_5424514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424514 prefixEnd_5424514 := by exact prefixLift 5424514
  have htrace : WordTrace (prefixWord ++ tailWord_5424514) baseStart_5424514 baseEnd_5424514 := by
    simpa [prefixWord, tailWord_5424514, baseEnd_5424514] using wordTrace_append hprefix tailTrace_5424514
  have hstable : (prefixWord ++ tailWord_5424514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424514).length < 2 ^ (prefixWord ++ tailWord_5424514).sum := by decide
  have hdescent : baseEnd_5424514 < baseStart_5424514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424557 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5424557 : Nat := 118140960795 + 5424557 * 2 ^ 59
def prefixEnd_5424557 : Nat := 4983230072969 + 3 ^ 40 * 5424557 * 2
def baseEnd_5424557 : Nat := 2785405078711438129490423

theorem tailTrace_5424557 : CollatzResearch.WordTrace tailWord_5424557 prefixEnd_5424557 2785405078711438129490423 := by
  unfold tailWord_5424557
  simp only [CollatzResearch.WordTrace]
  refine ⟨197849847808763904423007925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131899898539175936282005283 197849847808763904423007925)
  ·
    refine ⟨18548423232071616039656993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197849847808763904423007925 18548423232071616039656993)
    ·
      refine ⟨13911317424053712029742745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18548423232071616039656993 13911317424053712029742745)
      ·
        refine ⟨10433488068040284022307059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13911317424053712029742745 10433488068040284022307059)
        ·
          refine ⟨15650232102060426033460589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10433488068040284022307059 15650232102060426033460589)
          ·
            refine ⟨5868837038272659762547721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15650232102060426033460589 5868837038272659762547721)
            ·
              refine ⟨4401627778704494821910791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5868837038272659762547721 4401627778704494821910791)
              ·
                refine ⟨6602441668056742232866187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401627778704494821910791 6602441668056742232866187)
                ·
                  refine ⟨9903662502085113349299281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6602441668056742232866187 9903662502085113349299281)
                  ·
                    refine ⟨7427746876563835011974461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9903662502085113349299281 7427746876563835011974461)
                    ·
                      refine ⟨2785405078711438129490423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7427746876563835011974461 2785405078711438129490423)
                      ·
                        rfl

theorem cell23_5424557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5424557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424557 prefixEnd_5424557 := by exact prefixLift 5424557
  have htrace : WordTrace (prefixWord ++ tailWord_5424557) baseStart_5424557 baseEnd_5424557 := by
    simpa [prefixWord, tailWord_5424557, baseEnd_5424557] using wordTrace_append hprefix tailTrace_5424557
  have hstable : (prefixWord ++ tailWord_5424557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424557).length < 2 ^ (prefixWord ++ tailWord_5424557).sum := by decide
  have hdescent : baseEnd_5424557 < baseStart_5424557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424576 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 3, 4, 2]
def baseStart_5424576 : Nat := 118140960795 + 5424576 * 2 ^ 59
def prefixEnd_5424576 : Nat := 4983230072969 + 3 ^ 40 * 5424576 * 2
def baseEnd_5424576 : Nat := 2785414834843873555152835

theorem tailTrace_5424576 : CollatzResearch.WordTrace tailWord_5424576 prefixEnd_5424576 2785414834843873555152835 := by
  unfold tailWord_5424576
  simp only [CollatzResearch.WordTrace]
  refine ⟨98925270397847535333974791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131900360530463380445299721 98925270397847535333974791)
  ·
    refine ⟨148387905596771303000962187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98925270397847535333974791 148387905596771303000962187)
    ·
      refine ⟨222581858395156954501443281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148387905596771303000962187 222581858395156954501443281)
      ·
        refine ⟨166936393796367715876082461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222581858395156954501443281 166936393796367715876082461)
        ·
          refine ⟨62601147673637893453530923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166936393796367715876082461 62601147673637893453530923)
          ·
            refine ⟨93901721510456840180296385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62601147673637893453530923 93901721510456840180296385)
            ·
              refine ⟨70426291132842630135222289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93901721510456840180296385 70426291132842630135222289)
              ·
                refine ⟨52819718349631972601416717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70426291132842630135222289 52819718349631972601416717)
                ·
                  refine ⟨19807394381111989725531269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52819718349631972601416717 19807394381111989725531269)
                  ·
                    refine ⟨3713886446458498073537113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19807394381111989725531269 3713886446458498073537113)
                    ·
                      refine ⟨2785414834843873555152835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713886446458498073537113 2785414834843873555152835)
                      ·
                        rfl

theorem cell23_5424576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_5424576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424576 prefixEnd_5424576 := by exact prefixLift 5424576
  have htrace : WordTrace (prefixWord ++ tailWord_5424576) baseStart_5424576 baseEnd_5424576 := by
    simpa [prefixWord, tailWord_5424576, baseEnd_5424576] using wordTrace_append hprefix tailTrace_5424576
  have hstable : (prefixWord ++ tailWord_5424576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424576).length < 2 ^ (prefixWord ++ tailWord_5424576).sum := by decide
  have hdescent : baseEnd_5424576 < baseStart_5424576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424579 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 3]
def baseStart_5424579 : Nat := 118140960795 + 5424579 * 2 ^ 59
def prefixEnd_5424579 : Nat := 4983230072969 + 3 ^ 40 * 5424579 * 2
def baseEnd_5424579 : Nat := 2785416375285837043415321

theorem tailTrace_5424579 : CollatzResearch.WordTrace tailWord_5424579 prefixEnd_5424579 2785416375285837043415321 := by
  unfold tailWord_5424579
  simp only [CollatzResearch.WordTrace]
  refine ⟨197850650214684202180308791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131900433476456134786872527 197850650214684202180308791)
  ·
    refine ⟨296775975322026303270463187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197850650214684202180308791 296775975322026303270463187)
    ·
      refine ⟨445163962983039454905694781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296775975322026303270463187 445163962983039454905694781)
      ·
        refine ⟨166936486118639795589635543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 445163962983039454905694781 166936486118639795589635543)
        ·
          refine ⟨250404729177959693384453315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166936486118639795589635543 250404729177959693384453315)
          ·
            refine ⟨375607093766939540076679973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250404729177959693384453315 375607093766939540076679973)
            ·
              refine ⟨70426330081301163764377495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375607093766939540076679973 70426330081301163764377495)
              ·
                refine ⟨105639495121951745646566243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70426330081301163764377495 105639495121951745646566243)
                ·
                  refine ⟨158459242682927618469849365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105639495121951745646566243 158459242682927618469849365)
                  ·
                    refine ⟨7427777000762232115774189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 158459242682927618469849365 7427777000762232115774189)
                    ·
                      refine ⟨2785416375285837043415321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7427777000762232115774189 2785416375285837043415321)
                      ·
                        rfl

theorem cell23_5424579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_5424579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424579 prefixEnd_5424579 := by exact prefixLift 5424579
  have htrace : WordTrace (prefixWord ++ tailWord_5424579) baseStart_5424579 baseEnd_5424579 := by
    simpa [prefixWord, tailWord_5424579, baseEnd_5424579] using wordTrace_append hprefix tailTrace_5424579
  have hstable : (prefixWord ++ tailWord_5424579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424579).length < 2 ^ (prefixWord ++ tailWord_5424579).sum := by decide
  have hdescent : baseEnd_5424579 < baseStart_5424579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424700 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_5424700 : Nat := 118140960795 + 5424700 * 2 ^ 59
def prefixEnd_5424700 : Nat := 4983230072969 + 3 ^ 40 * 5424700 * 2
def baseEnd_5424700 : Nat := 2785478506445031070002265

theorem tailTrace_5424700 : CollatzResearch.WordTrace tailWord_5424700 prefixEnd_5424700 2785478506445031070002265 := by
  unfold tailWord_5424700
  simp only [CollatzResearch.WordTrace]
  refine ⟨98927531723622919922731777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131903375631497226563642369 98927531723622919922731777)
  ·
    refine ⟨74195648792717189942048833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98927531723622919922731777 74195648792717189942048833)
    ·
      refine ⟨55646736594537892456536625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74195648792717189942048833 55646736594537892456536625)
      ·
        refine ⟨41735052445903419342402469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55646736594537892456536625 41735052445903419342402469)
        ·
          refine ⟨7825322333606891126700463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41735052445903419342402469 7825322333606891126700463)
          ·
            refine ⟨11737983500410336690050695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825322333606891126700463 11737983500410336690050695)
            ·
              refine ⟨17606975250615505035076043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11737983500410336690050695 17606975250615505035076043)
              ·
                refine ⟨26410462875923257552614065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17606975250615505035076043 26410462875923257552614065)
                ·
                  refine ⟨19807847156942443164460549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26410462875923257552614065 19807847156942443164460549)
                  ·
                    refine ⟨3713971341926708093336353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19807847156942443164460549 3713971341926708093336353)
                    ·
                      refine ⟨2785478506445031070002265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3713971341926708093336353 2785478506445031070002265)
                      ·
                        rfl

theorem cell23_5424700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_5424700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424700 prefixEnd_5424700 := by exact prefixLift 5424700
  have htrace : WordTrace (prefixWord ++ tailWord_5424700) baseStart_5424700 baseEnd_5424700 := by
    simpa [prefixWord, tailWord_5424700, baseEnd_5424700] using wordTrace_append hprefix tailTrace_5424700
  have hstable : (prefixWord ++ tailWord_5424700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424700).length < 2 ^ (prefixWord ++ tailWord_5424700).sum := by decide
  have hdescent : baseEnd_5424700 < baseStart_5424700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424717 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5424717 : Nat := 118140960795 + 5424717 * 2 ^ 59
def prefixEnd_5424717 : Nat := 4983230072969 + 3 ^ 40 * 5424717 * 2
def baseEnd_5424717 : Nat := 2785487235616157503489687

theorem tailTrace_5424717 : CollatzResearch.WordTrace tailWord_5424717 prefixEnd_5424717 2785487235616157503489687 := by
  unfold tailWord_5424717
  simp only [CollatzResearch.WordTrace]
  refine ⟨197855683488184251748832405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131903788992122834499221603 197855683488184251748832405)
  ·
    refine ⟨9274485163508636800726519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197855683488184251748832405 9274485163508636800726519)
    ·
      refine ⟨13911727745262955201089779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9274485163508636800726519 13911727745262955201089779)
      ·
        refine ⟨20867591617894432801634669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13911727745262955201089779 20867591617894432801634669)
        ·
          refine ⟨7825346856710412300613001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20867591617894432801634669 7825346856710412300613001)
          ·
            refine ⟨5869010142532809225459751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7825346856710412300613001 5869010142532809225459751)
            ·
              refine ⟨8803515213799213838189627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869010142532809225459751 8803515213799213838189627)
              ·
                refine ⟨13205272820698820757284441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8803515213799213838189627 13205272820698820757284441)
                ·
                  refine ⟨9903954615524115567963331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13205272820698820757284441 9903954615524115567963331)
                  ·
                    refine ⟨14855931923286173351944997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9903954615524115567963331 14855931923286173351944997)
                    ·
                      refine ⟨2785487235616157503489687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14855931923286173351944997 2785487235616157503489687)
                      ·
                        rfl

theorem cell23_5424717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5424717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424717 prefixEnd_5424717 := by exact prefixLift 5424717
  have htrace : WordTrace (prefixWord ++ tailWord_5424717) baseStart_5424717 baseEnd_5424717 := by
    simpa [prefixWord, tailWord_5424717, baseEnd_5424717] using wordTrace_append hprefix tailTrace_5424717
  have hstable : (prefixWord ++ tailWord_5424717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424717).length < 2 ^ (prefixWord ++ tailWord_5424717).sum := by decide
  have hdescent : baseEnd_5424717 < baseStart_5424717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424773 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 6, 2]
def baseStart_5424773 : Nat := 118140960795 + 5424773 * 2 ^ 59
def prefixEnd_5424773 : Nat := 4983230072969 + 3 ^ 40 * 5424773 * 2
def baseEnd_5424773 : Nat := 2785515990532809284389429

theorem tailTrace_5424773 : CollatzResearch.WordTrace tailWord_5424773 prefixEnd_5424773 2785515990532809284389429 := by
  unfold tailWord_5424773
  simp only [CollatzResearch.WordTrace]
  refine ⟨197857725975981373312870973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131905150650654248875247315 197857725975981373312870973)
  ·
    refine ⟨74196647240993014992326615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197857725975981373312870973 74196647240993014992326615)
    ·
      refine ⟨111294970861489522488489923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74196647240993014992326615 111294970861489522488489923)
      ·
        refine ⟨166942456292234283732734885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111294970861489522488489923 166942456292234283732734885)
        ·
          refine ⟨31301710554793928199887791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166942456292234283732734885 31301710554793928199887791)
          ·
            refine ⟨46952565832190892299831687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31301710554793928199887791 46952565832190892299831687)
            ·
              refine ⟨70428848748286338449747531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46952565832190892299831687 70428848748286338449747531)
              ·
                refine ⟨105643273122429507674621297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70428848748286338449747531 105643273122429507674621297)
                ·
                  refine ⟨79232454841822130755965973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105643273122429507674621297 79232454841822130755965973)
                  ·
                    refine ⟨3714021320710412379185905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79232454841822130755965973 3714021320710412379185905)
                    ·
                      refine ⟨2785515990532809284389429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714021320710412379185905 2785515990532809284389429)
                      ·
                        rfl

theorem cell23_5424773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_5424773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424773 prefixEnd_5424773 := by exact prefixLift 5424773
  have htrace : WordTrace (prefixWord ++ tailWord_5424773) baseStart_5424773 baseEnd_5424773 := by
    simpa [prefixWord, tailWord_5424773, baseEnd_5424773] using wordTrace_append hprefix tailTrace_5424773
  have hstable : (prefixWord ++ tailWord_5424773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424773).length < 2 ^ (prefixWord ++ tailWord_5424773).sum := by decide
  have hdescent : baseEnd_5424773 < baseStart_5424773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424813 : List Nat := [1, 5, 2, 1, 1, 1, 4, 8]
def baseStart_5424813 : Nat := 118140960795 + 5424813 * 2 ^ 59
def prefixEnd_5424813 : Nat := 4983230072969 + 3 ^ 40 * 5424813 * 2
def baseEnd_5424813 : Nat := 103168019620703301032935

theorem tailTrace_5424813 : CollatzResearch.WordTrace tailWord_5424813 prefixEnd_5424813 103168019620703301032935 := by
  unfold tailWord_5424813
  simp only [CollatzResearch.WordTrace]
  refine ⟨197859184895836460144327093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131906123263890973429551395 197859184895836460144327093)
  ·
    refine ⟨18549298583984668138530665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197859184895836460144327093 18549298583984668138530665)
    ·
      refine ⟨13911973937988501103897999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18549298583984668138530665 13911973937988501103897999)
      ·
        refine ⟨20867960906982751655846999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13911973937988501103897999 20867960906982751655846999)
        ·
          refine ⟨31301941360474127483770499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20867960906982751655846999 31301941360474127483770499)
          ·
            refine ⟨46952912040711191225655749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31301941360474127483770499 46952912040711191225655749)
            ·
              refine ⟨8803671007633348354810453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46952912040711191225655749 8803671007633348354810453)
              ·
                refine ⟨103168019620703301032935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8803671007633348354810453 103168019620703301032935)
                ·
                  rfl

theorem cell23_5424813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 8].length) (baseStart_5424813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424813 prefixEnd_5424813 := by exact prefixLift 5424813
  have htrace : WordTrace (prefixWord ++ tailWord_5424813) baseStart_5424813 baseEnd_5424813 := by
    simpa [prefixWord, tailWord_5424813, baseEnd_5424813] using wordTrace_append hprefix tailTrace_5424813
  have hstable : (prefixWord ++ tailWord_5424813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424813).length < 2 ^ (prefixWord ++ tailWord_5424813).sum := by decide
  have hdescent : baseEnd_5424813 < baseStart_5424813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424834 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5424834 : Nat := 118140960795 + 5424834 * 2 ^ 59
def prefixEnd_5424834 : Nat := 4983230072969 + 3 ^ 40 * 5424834 * 2
def baseEnd_5424834 : Nat := 928515770950911181908883

theorem tailTrace_5424834 : CollatzResearch.WordTrace tailWord_5424834 prefixEnd_5424834 928515770950911181908883 := by
  unfold tailWord_5424834
  simp only [CollatzResearch.WordTrace]
  refine ⟨49464987707190095182710389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131906633885840253820561037 49464987707190095182710389)
  ·
    refine ⟨4637342597549071423379099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49464987707190095182710389 4637342597549071423379099)
    ·
      refine ⟨6956013896323607135068649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637342597549071423379099 6956013896323607135068649)
      ·
        refine ⟨5217010422242705351301487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6956013896323607135068649 5217010422242705351301487)
        ·
          refine ⟨7825515633364058026952231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5217010422242705351301487 7825515633364058026952231)
          ·
            refine ⟨11738273450046087040428347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825515633364058026952231 11738273450046087040428347)
            ·
              refine ⟨17607410175069130560642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11738273450046087040428347 17607410175069130560642521)
              ·
                refine ⟨13205557631301847920481891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17607410175069130560642521 13205557631301847920481891)
                ·
                  refine ⟨19808336446952771880722837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13205557631301847920481891 19808336446952771880722837)
                  ·
                    refine ⟨928515770950911181908883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19808336446952771880722837 928515770950911181908883)
                    ·
                      rfl

theorem cell23_5424834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5424834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424834 prefixEnd_5424834 := by exact prefixLift 5424834
  have htrace : WordTrace (prefixWord ++ tailWord_5424834) baseStart_5424834 baseEnd_5424834 := by
    simpa [prefixWord, tailWord_5424834, baseEnd_5424834] using wordTrace_append hprefix tailTrace_5424834
  have hstable : (prefixWord ++ tailWord_5424834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424834).length < 2 ^ (prefixWord ++ tailWord_5424834).sum := by decide
  have hdescent : baseEnd_5424834 < baseStart_5424834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424844 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5424844 : Nat := 118140960795 + 5424844 * 2 ^ 59
def prefixEnd_5424844 : Nat := 4983230072969 + 3 ^ 40 * 5424844 * 2
def baseEnd_5424844 : Nat := 2785552447659278506601603

theorem tailTrace_5424844 : CollatzResearch.WordTrace tailWord_5424844 prefixEnd_5424844 2785552447659278506601603 := by
  unfold tailWord_5424844
  simp only [CollatzResearch.WordTrace]
  refine ⟨98930157779362076219352793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131906877039149434959137057 98930157779362076219352793)
  ·
    refine ⟨74197618334521557164514595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98930157779362076219352793 74197618334521557164514595)
    ·
      refine ⟨111296427501782335746771893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74197618334521557164514595 111296427501782335746771893)
      ·
        refine ⟨10434040078292093976259865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111296427501782335746771893 10434040078292093976259865)
        ·
          refine ⟨7825530058719070482194899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10434040078292093976259865 7825530058719070482194899)
          ·
            refine ⟨11738295088078605723292349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825530058719070482194899 11738295088078605723292349)
            ·
              refine ⟨4401860658029477146234631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11738295088078605723292349 4401860658029477146234631)
              ·
                refine ⟨6602790987044215719351947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401860658029477146234631 6602790987044215719351947)
                ·
                  refine ⟨9904186480566323579027921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6602790987044215719351947 9904186480566323579027921)
                  ·
                    refine ⟨7428139860424742684270941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9904186480566323579027921 7428139860424742684270941)
                    ·
                      refine ⟨2785552447659278506601603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7428139860424742684270941 2785552447659278506601603)
                      ·
                        rfl

theorem cell23_5424844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5424844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424844 prefixEnd_5424844 := by exact prefixLift 5424844
  have htrace : WordTrace (prefixWord ++ tailWord_5424844) baseStart_5424844 baseEnd_5424844 := by
    simpa [prefixWord, tailWord_5424844, baseEnd_5424844] using wordTrace_append hprefix tailTrace_5424844
  have hstable : (prefixWord ++ tailWord_5424844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424844).length < 2 ^ (prefixWord ++ tailWord_5424844).sum := by decide
  have hdescent : baseEnd_5424844 < baseStart_5424844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424857 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 3]
def baseStart_5424857 : Nat := 118140960795 + 5424857 * 2 ^ 59
def prefixEnd_5424857 : Nat := 4983230072969 + 3 ^ 40 * 5424857 * 2
def baseEnd_5424857 : Nat := 2785559122907786955739043

theorem tailTrace_5424857 : CollatzResearch.WordTrace tailWord_5424857 prefixEnd_5424857 2785559122907786955739043 := by
  unfold tailWord_5424857
  simp only [CollatzResearch.WordTrace]
  refine ⟨197860789707677055658928825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131907193138451370439285883 197860789707677055658928825)
  ·
    refine ⟨148395592280757791744196619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197860789707677055658928825 148395592280757791744196619)
    ·
      refine ⟨222593388421136687616294929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148395592280757791744196619 222593388421136687616294929)
      ·
        refine ⟨166945041315852515712221197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222593388421136687616294929 166945041315852515712221197)
        ·
          refine ⟨62604390493444693392082949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166945041315852515712221197 62604390493444693392082949)
          ·
            refine ⟨11738323217520880011015553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62604390493444693392082949 11738323217520880011015553)
            ·
              refine ⟨8803742413140660008261665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11738323217520880011015553 8803742413140660008261665)
              ·
                refine ⟨6602806809855495006196249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8803742413140660008261665 6602806809855495006196249)
                ·
                  refine ⟨4952105107391621254647187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6602806809855495006196249 4952105107391621254647187)
                  ·
                    refine ⟨7428157661087431881970781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4952105107391621254647187 7428157661087431881970781)
                    ·
                      refine ⟨2785559122907786955739043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7428157661087431881970781 2785559122907786955739043)
                      ·
                        rfl

theorem cell23_5424857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_5424857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424857 prefixEnd_5424857 := by exact prefixLift 5424857
  have htrace : WordTrace (prefixWord ++ tailWord_5424857) baseStart_5424857 baseEnd_5424857 := by
    simpa [prefixWord, tailWord_5424857, baseEnd_5424857] using wordTrace_append hprefix tailTrace_5424857
  have hstable : (prefixWord ++ tailWord_5424857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424857).length < 2 ^ (prefixWord ++ tailWord_5424857).sum := by decide
  have hdescent : baseEnd_5424857 < baseStart_5424857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424902 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5424902 : Nat := 118140960795 + 5424902 * 2 ^ 59
def prefixEnd_5424902 : Nat := 4983230072969 + 3 ^ 40 * 5424902 * 2
def baseEnd_5424902 : Nat := 928527409845746426558779

theorem tailTrace_5424902 : CollatzResearch.WordTrace tailWord_5424902 prefixEnd_5424902 928527409845746426558779 := by
  unfold tailWord_5424902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183200968516063385759905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131908287328342685562877973 6183200968516063385759905)
  ·
    refine ⟨4637400726387047539319929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6183200968516063385759905 4637400726387047539319929)
    ·
      refine ⟨3478050544790285654489947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4637400726387047539319929 3478050544790285654489947)
      ·
        refine ⟨5217075817185428481734921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3478050544790285654489947 5217075817185428481734921)
        ·
          refine ⟨3912806862889071361301191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5217075817185428481734921 3912806862889071361301191)
          ·
            refine ⟨5869210294333607041951787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912806862889071361301191 5869210294333607041951787)
            ·
              refine ⟨8803815441500410562927681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869210294333607041951787 8803815441500410562927681)
              ·
                refine ⟨6602861581125307922195761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8803815441500410562927681 6602861581125307922195761)
                ·
                  refine ⟨4952146185843980941646821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6602861581125307922195761 4952146185843980941646821)
                  ·
                    refine ⟨928527409845746426558779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952146185843980941646821 928527409845746426558779)
                    ·
                      rfl

theorem cell23_5424902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5424902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424902 prefixEnd_5424902 := by exact prefixLift 5424902
  have htrace : WordTrace (prefixWord ++ tailWord_5424902) baseStart_5424902 baseEnd_5424902 := by
    simpa [prefixWord, tailWord_5424902, baseEnd_5424902] using wordTrace_append hprefix tailTrace_5424902
  have hstable : (prefixWord ++ tailWord_5424902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424902).length < 2 ^ (prefixWord ++ tailWord_5424902).sum := by decide
  have hdescent : baseEnd_5424902 < baseStart_5424902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424920 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 5]
def baseStart_5424920 : Nat := 118140960795 + 5424920 * 2 ^ 59
def prefixEnd_5424920 : Nat := 4983230072969 + 3 ^ 40 * 5424920 * 2
def baseEnd_5424920 : Nat := 309510163576557801027917

theorem tailTrace_5424920 : CollatzResearch.WordTrace tailWord_5424920 prefixEnd_5424920 309510163576557801027917 := by
  unfold tailWord_5424920
  simp only [CollatzResearch.WordTrace]
  refine ⟨98931543753224408709236107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131908725004299211612314809 98931543753224408709236107)
  ·
    refine ⟨148397315629836613063854161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98931543753224408709236107 148397315629836613063854161)
    ·
      refine ⟨111297986722377459797890621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148397315629836613063854161 111297986722377459797890621)
      ·
        refine ⟨41736745020891547424208983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111297986722377459797890621 41736745020891547424208983)
        ·
          refine ⟨62605117531337321136313475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41736745020891547424208983 62605117531337321136313475)
          ·
            refine ⟨93907676297005981704470213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62605117531337321136313475 93907676297005981704470213)
            ·
              refine ⟨17607689305688621569588165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93907676297005981704470213 17607689305688621569588165)
              ·
                refine ⟨3301441744816616544297781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17607689305688621569588165 3301441744816616544297781)
                ·
                  refine ⟨309510163576557801027917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301441744816616544297781 309510163576557801027917)
                  ·
                    rfl

theorem cell23_5424920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 5].length) (baseStart_5424920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424920 prefixEnd_5424920 := by exact prefixLift 5424920
  have htrace : WordTrace (prefixWord ++ tailWord_5424920) baseStart_5424920 baseEnd_5424920 := by
    simpa [prefixWord, tailWord_5424920, baseEnd_5424920] using wordTrace_append hprefix tailTrace_5424920
  have hstable : (prefixWord ++ tailWord_5424920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424920).length < 2 ^ (prefixWord ++ tailWord_5424920).sum := by decide
  have hdescent : baseEnd_5424920 < baseStart_5424920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424930 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_5424930 : Nat := 118140960795 + 5424930 * 2 ^ 59
def prefixEnd_5424930 : Nat := 4983230072969 + 3 ^ 40 * 5424930 * 2
def baseEnd_5424930 : Nat := 2785596606995565170126207

theorem tailTrace_5424930 : CollatzResearch.WordTrace tailWord_5424930 prefixEnd_5424930 2785596606995565170126207 := by
  unfold tailWord_5424930
  simp only [CollatzResearch.WordTrace]
  refine ⟨49465863059103147281584061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131908968157608392750890829 49465863059103147281584061)
  ·
    refine ⟨18549698647163680230594023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49465863059103147281584061 18549698647163680230594023)
    ·
      refine ⟨27824547970745520345891035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18549698647163680230594023 27824547970745520345891035)
      ·
        refine ⟨41736821956118280518836553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27824547970745520345891035 41736821956118280518836553)
        ·
          refine ⟨31302616467088710389127415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41736821956118280518836553 31302616467088710389127415)
          ·
            refine ⟨46953924700633065583691123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31302616467088710389127415 46953924700633065583691123)
            ·
              refine ⟨70430887050949598375536685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46953924700633065583691123 70430887050949598375536685)
              ·
                refine ⟨26411582644106099390826257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70430887050949598375536685 26411582644106099390826257)
                ·
                  refine ⟨19808686983079574543119693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26411582644106099390826257 19808686983079574543119693)
                  ·
                    refine ⟨7428257618654840453669885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19808686983079574543119693 7428257618654840453669885)
                    ·
                      refine ⟨2785596606995565170126207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7428257618654840453669885 2785596606995565170126207)
                      ·
                        rfl

theorem cell23_5424930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_5424930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424930 prefixEnd_5424930 := by exact prefixLift 5424930
  have htrace : WordTrace (prefixWord ++ tailWord_5424930) baseStart_5424930 baseEnd_5424930 := by
    simpa [prefixWord, tailWord_5424930, baseEnd_5424930] using wordTrace_append hprefix tailTrace_5424930
  have hstable : (prefixWord ++ tailWord_5424930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424930).length < 2 ^ (prefixWord ++ tailWord_5424930).sum := by decide
  have hdescent : baseEnd_5424930 < baseStart_5424930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424933 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_5424933 : Nat := 118140960795 + 5424933 * 2 ^ 59
def prefixEnd_5424933 : Nat := 4983230072969 + 3 ^ 40 * 5424933 * 2
def baseEnd_5424933 : Nat := 928532715812509552796231

theorem tailTrace_5424933 : CollatzResearch.WordTrace tailWord_5424933 prefixEnd_5424933 928532715812509552796231 := by
  unfold tailWord_5424933
  simp only [CollatzResearch.WordTrace]
  refine ⟨197863561655401720638695453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131909041103601147092463635 197863561655401720638695453)
  ·
    refine ⟨74198835620775645239510795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197863561655401720638695453 74198835620775645239510795)
    ·
      refine ⟨111298253431163467859266193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74198835620775645239510795 111298253431163467859266193)
      ·
        refine ⟨83473690073372600894449645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111298253431163467859266193 83473690073372600894449645)
        ·
          refine ⟨31302633777514725335418617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83473690073372600894449645 31302633777514725335418617)
          ·
            refine ⟨23476975333136044001563963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31302633777514725335418617 23476975333136044001563963)
            ·
              refine ⟨35215462999704066002345945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23476975333136044001563963 35215462999704066002345945)
              ·
                refine ⟨26411597249778049501759459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35215462999704066002345945 26411597249778049501759459)
                ·
                  refine ⟨39617395874667074252639189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26411597249778049501759459 39617395874667074252639189)
                  ·
                    refine ⟨928532715812509552796231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39617395874667074252639189 928532715812509552796231)
                    ·
                      rfl

theorem cell23_5424933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_5424933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424933 prefixEnd_5424933 := by exact prefixLift 5424933
  have htrace : WordTrace (prefixWord ++ tailWord_5424933) baseStart_5424933 baseEnd_5424933 := by
    simpa [prefixWord, tailWord_5424933, baseEnd_5424933] using wordTrace_append hprefix tailTrace_5424933
  have hstable : (prefixWord ++ tailWord_5424933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424933).length < 2 ^ (prefixWord ++ tailWord_5424933).sum := by decide
  have hdescent : baseEnd_5424933 < baseStart_5424933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5424970 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_5424970 : Nat := 118140960795 + 5424970 * 2 ^ 59
def prefixEnd_5424970 : Nat := 4983230072969 + 3 ^ 40 * 5424970 * 2
def baseEnd_5424970 : Nat := 2785617146221745013626023

theorem tailTrace_5424970 : CollatzResearch.WordTrace tailWord_5424970 prefixEnd_5424970 2785617146221745013626023 := by
  unfold tailWord_5424970
  simp only [CollatzResearch.WordTrace]
  refine ⟨49466227789066918989448091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131909940770845117305194909 49466227789066918989448091)
  ·
    refine ⟨74199341683600378484172137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49466227789066918989448091 74199341683600378484172137)
    ·
      refine ⟨55649506262700283863129103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74199341683600378484172137 55649506262700283863129103)
      ·
        refine ⟨83474259394050425794693655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55649506262700283863129103 83474259394050425794693655)
        ·
          refine ⟨125211389091075638692040483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83474259394050425794693655 125211389091075638692040483)
          ·
            refine ⟨187817083636613458038060725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125211389091075638692040483 187817083636613458038060725)
            ·
              refine ⟨17607851590932511691068193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187817083636613458038060725 17607851590932511691068193)
              ·
                refine ⟨13205888693199383768301145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17607851590932511691068193 13205888693199383768301145)
                ·
                  refine ⟨9904416519899537826225859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13205888693199383768301145 9904416519899537826225859)
                  ·
                    refine ⟨14856624779849306739338789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9904416519899537826225859 14856624779849306739338789)
                    ·
                      refine ⟨2785617146221745013626023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14856624779849306739338789 2785617146221745013626023)
                      ·
                        rfl

theorem cell23_5424970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_5424970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5424970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5424970 prefixEnd_5424970 := by exact prefixLift 5424970
  have htrace : WordTrace (prefixWord ++ tailWord_5424970) baseStart_5424970 baseEnd_5424970 := by
    simpa [prefixWord, tailWord_5424970, baseEnd_5424970] using wordTrace_append hprefix tailTrace_5424970
  have hstable : (prefixWord ++ tailWord_5424970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5424970).length < 2 ^ (prefixWord ++ tailWord_5424970).sum := by decide
  have hdescent : baseEnd_5424970 < baseStart_5424970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5424970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425080 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_5425080 : Nat := 118140960795 + 5425080 * 2 ^ 59
def prefixEnd_5425080 : Nat := 4983230072969 + 3 ^ 40 * 5425080 * 2
def baseEnd_5425080 : Nat := 2785673629093739583250517

theorem tailTrace_5425080 : CollatzResearch.WordTrace tailWord_5425080 prefixEnd_5425080 2785673629093739583250517 := by
  unfold tailWord_5425080
  simp only [CollatzResearch.WordTrace]
  refine ⟨98934461592934582372148347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131912615457246109829531129 98934461592934582372148347)
  ·
    refine ⟨148401692389401873558222521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98934461592934582372148347 148401692389401873558222521)
    ·
      refine ⟨111301269292051405168666891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148401692389401873558222521 111301269292051405168666891)
      ·
        refine ⟨166951903938077107753000337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111301269292051405168666891 166951903938077107753000337)
        ·
          refine ⟨125213927953557830814750253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166951903938077107753000337 125213927953557830814750253)
          ·
            refine ⟨46955222982584186555531345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125213927953557830814750253 46955222982584186555531345)
            ·
              refine ⟨35216417236938139916648509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46955222982584186555531345 35216417236938139916648509)
              ·
                refine ⟨13206156463851802468743191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35216417236938139916648509 13206156463851802468743191)
                ·
                  refine ⟨19809234695777703703114787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13206156463851802468743191 19809234695777703703114787)
                  ·
                    refine ⟨29713852043666555554672181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19809234695777703703114787 29713852043666555554672181)
                    ·
                      refine ⟨2785673629093739583250517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29713852043666555554672181 2785673629093739583250517)
                      ·
                        rfl

theorem cell23_5425080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_5425080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425080 prefixEnd_5425080 := by exact prefixLift 5425080
  have htrace : WordTrace (prefixWord ++ tailWord_5425080) baseStart_5425080 baseEnd_5425080 := by
    simpa [prefixWord, tailWord_5425080, baseEnd_5425080] using wordTrace_append hprefix tailTrace_5425080
  have hstable : (prefixWord ++ tailWord_5425080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425080).length < 2 ^ (prefixWord ++ tailWord_5425080).sum := by decide
  have hdescent : baseEnd_5425080 < baseStart_5425080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425117 : List Nat := [1, 4, 3, 1, 3, 1, 1, 9]
def baseStart_5425117 : Nat := 118140960795 + 5425117 * 2 ^ 59
def prefixEnd_5425117 : Nat := 4983230072969 + 3 ^ 40 * 5425117 * 2
def baseEnd_5425117 : Nat := 103173801032516886610661

theorem tailTrace_5425117 : CollatzResearch.WordTrace tailWord_5425117 prefixEnd_5425117 103173801032516886610661 := by
  unfold tailWord_5425117
  simp only [CollatzResearch.WordTrace]
  refine ⟨197870272686735120063393605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131913515124490080042262403 197870272686735120063393605)
  ·
    refine ⟨37100676128762835011886301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197870272686735120063393605 37100676128762835011886301)
    ·
      refine ⟨13912753548286063129457363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37100676128762835011886301 13912753548286063129457363)
      ·
        refine ⟨20869130322429094694186045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13912753548286063129457363 20869130322429094694186045)
        ·
          refine ⟨7825923870910910510319767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20869130322429094694186045 7825923870910910510319767)
          ·
            refine ⟨11738885806366365765479651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825923870910910510319767 11738885806366365765479651)
            ·
              refine ⟨17608328709549548648219477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11738885806366365765479651 17608328709549548648219477)
              ·
                refine ⟨103173801032516886610661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17608328709549548648219477 103173801032516886610661)
                ·
                  rfl

theorem cell23_5425117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 9].length) (baseStart_5425117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425117 prefixEnd_5425117 := by exact prefixLift 5425117
  have htrace : WordTrace (prefixWord ++ tailWord_5425117) baseStart_5425117 baseEnd_5425117 := by
    simpa [prefixWord, tailWord_5425117, baseEnd_5425117] using wordTrace_append hprefix tailTrace_5425117
  have hstable : (prefixWord ++ tailWord_5425117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425117).length < 2 ^ (prefixWord ++ tailWord_5425117).sum := by decide
  have hdescent : baseEnd_5425117 < baseStart_5425117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425122 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5425122 : Nat := 118140960795 + 5425122 * 2 ^ 59
def prefixEnd_5425122 : Nat := 4983230072969 + 3 ^ 40 * 5425122 * 2
def baseEnd_5425122 : Nat := 2785695195281228418925325

theorem tailTrace_5425122 : CollatzResearch.WordTrace tailWord_5425122 prefixEnd_5425122 2785695195281228418925325 := by
  unfold tailWord_5425122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49467613762929251479331405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131913636701144670611550413 49467613762929251479331405)
  ·
    refine ⟨18550355161098469304749277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49467613762929251479331405 18550355161098469304749277)
    ·
      refine ⟨6956383185411925989280979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18550355161098469304749277 6956383185411925989280979)
      ·
        refine ⟨10434574778117888983921469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956383185411925989280979 10434574778117888983921469)
        ·
          refine ⟨3912965541794208368970551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10434574778117888983921469 3912965541794208368970551)
          ·
            refine ⟨5869448312691312553455827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912965541794208368970551 5869448312691312553455827)
            ·
              refine ⟨8804172469036968830183741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869448312691312553455827 8804172469036968830183741)
              ·
                refine ⟨3301564675888863311318903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8804172469036968830183741 3301564675888863311318903)
                ·
                  refine ⟨4952347013833294966978355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301564675888863311318903 4952347013833294966978355)
                  ·
                    refine ⟨7428520520749942450467533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4952347013833294966978355 7428520520749942450467533)
                    ·
                      refine ⟨2785695195281228418925325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7428520520749942450467533 2785695195281228418925325)
                      ·
                        rfl

theorem cell23_5425122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5425122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425122 prefixEnd_5425122 := by exact prefixLift 5425122
  have htrace : WordTrace (prefixWord ++ tailWord_5425122) baseStart_5425122 baseEnd_5425122 := by
    simpa [prefixWord, tailWord_5425122, baseEnd_5425122] using wordTrace_append hprefix tailTrace_5425122
  have hstable : (prefixWord ++ tailWord_5425122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425122).length < 2 ^ (prefixWord ++ tailWord_5425122).sum := by decide
  have hdescent : baseEnd_5425122 < baseStart_5425122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425160 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_5425160 : Nat := 118140960795 + 5425160 * 2 ^ 59
def prefixEnd_5425160 : Nat := 4983230072969 + 3 ^ 40 * 5425160 * 2
def baseEnd_5425160 : Nat := 928571569182033090083383

theorem tailTrace_5425160 : CollatzResearch.WordTrace tailWord_5425160 prefixEnd_5425160 928571569182033090083383 := by
  unfold tailWord_5425160
  simp only [CollatzResearch.WordTrace]
  refine ⟨98935920512789669203604467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131914560683719558938139289 98935920512789669203604467)
  ·
    refine ⟨148403880769184503805406701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98935920512789669203604467 148403880769184503805406701)
    ·
      refine ⟨55651455288444188927027513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148403880769184503805406701 55651455288444188927027513)
      ·
        refine ⟨41738591466333141695270635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55651455288444188927027513 41738591466333141695270635)
        ·
          refine ⟨62607887199499712542905953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41738591466333141695270635 62607887199499712542905953)
          ·
            refine ⟨46955915399624784407179465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62607887199499712542905953 46955915399624784407179465)
            ·
              refine ⟨35216936549718588305384599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46955915399624784407179465 35216936549718588305384599)
              ·
                refine ⟨52825404824577882458076899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35216936549718588305384599 52825404824577882458076899)
                ·
                  refine ⟨79238107236866823687115349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52825404824577882458076899 79238107236866823687115349)
                  ·
                    refine ⟨928571569182033090083383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79238107236866823687115349 928571569182033090083383)
                    ·
                      rfl

theorem cell23_5425160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_5425160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425160 prefixEnd_5425160 := by exact prefixLift 5425160
  have htrace : WordTrace (prefixWord ++ tailWord_5425160) baseStart_5425160 baseEnd_5425160 := by
    simpa [prefixWord, tailWord_5425160, baseEnd_5425160] using wordTrace_append hprefix tailTrace_5425160
  have hstable : (prefixWord ++ tailWord_5425160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425160).length < 2 ^ (prefixWord ++ tailWord_5425160).sum := by decide
  have hdescent : baseEnd_5425160 < baseStart_5425160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425201 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 2, 2, 2]
def baseStart_5425201 : Nat := 118140960795 + 5425201 * 2 ^ 59
def prefixEnd_5425201 : Nat := 4983230072969 + 3 ^ 40 * 5425201 * 2
def baseEnd_5425201 : Nat := 2785735760252933609837461

theorem tailTrace_5425201 : CollatzResearch.WordTrace tailWord_5425201 prefixEnd_5425201 2785735760252933609837461 := by
  unfold tailWord_5425201
  simp only [CollatzResearch.WordTrace]
  refine ⟨197873336418430802409451457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131915557612287201606300971 197873336418430802409451457)
  ·
    refine ⟨148405002313823101807088593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197873336418430802409451457 148405002313823101807088593)
    ·
      refine ⟨111303751735367326355316445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148405002313823101807088593 111303751735367326355316445)
      ·
        refine ⟨41738906900762747383243667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111303751735367326355316445 41738906900762747383243667)
        ·
          refine ⟨62608360351144121074865501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41738906900762747383243667 62608360351144121074865501)
          ·
            refine ⟨23478135131679045403074563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62608360351144121074865501 23478135131679045403074563)
            ·
              refine ⟨35217202697518568104611845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23478135131679045403074563 35217202697518568104611845)
              ·
                refine ⟨6603225505784731519614721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35217202697518568104611845 6603225505784731519614721)
                ·
                  refine ⟨4952419129338548639711041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6603225505784731519614721 4952419129338548639711041)
                  ·
                    refine ⟨3714314347003911479783281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4952419129338548639711041 3714314347003911479783281)
                    ·
                      refine ⟨2785735760252933609837461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714314347003911479783281 2785735760252933609837461)
                      ·
                        rfl

theorem cell23_5425201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_5425201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425201 prefixEnd_5425201 := by exact prefixLift 5425201
  have htrace : WordTrace (prefixWord ++ tailWord_5425201) baseStart_5425201 baseEnd_5425201 := by
    simpa [prefixWord, tailWord_5425201, baseEnd_5425201] using wordTrace_append hprefix tailTrace_5425201
  have hstable : (prefixWord ++ tailWord_5425201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425201).length < 2 ^ (prefixWord ++ tailWord_5425201).sum := by decide
  have hdescent : baseEnd_5425201 < baseStart_5425201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425210 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_5425210 : Nat := 118140960795 + 5425210 * 2 ^ 59
def prefixEnd_5425210 : Nat := 4983230072969 + 3 ^ 40 * 5425210 * 2
def baseEnd_5425210 : Nat := 2785740381578824074624919

theorem tailTrace_5425210 : CollatzResearch.WordTrace tailWord_5425210 prefixEnd_5425210 2785740381578824074624919 := by
  unfold tailWord_5425210
  simp only [CollatzResearch.WordTrace]
  refine ⟨49468416168849549236632271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131915776450265464631019389 49468416168849549236632271)
  ·
    refine ⟨74202624253274323854948407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49468416168849549236632271 74202624253274323854948407)
    ·
      refine ⟨111303936379911485782422611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74202624253274323854948407 111303936379911485782422611)
      ·
        refine ⟨166955904569867228673633917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111303936379911485782422611 166955904569867228673633917)
        ·
          refine ⟨62608464213700210752612719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166955904569867228673633917 62608464213700210752612719)
          ·
            refine ⟨93912696320550316128919079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62608464213700210752612719 93912696320550316128919079)
            ·
              refine ⟨140869044480825474193378619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93912696320550316128919079 140869044480825474193378619)
              ·
                refine ⟨211303566721238211290067929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140869044480825474193378619 211303566721238211290067929)
                ·
                  refine ⟨158477675040928658467550947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211303566721238211290067929 158477675040928658467550947)
                  ·
                    refine ⟨237716512561392987701326421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158477675040928658467550947 237716512561392987701326421)
                    ·
                      refine ⟨2785740381578824074624919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 237716512561392987701326421 2785740381578824074624919)
                      ·
                        rfl

theorem cell23_5425210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_5425210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425210 prefixEnd_5425210 := by exact prefixLift 5425210
  have htrace : WordTrace (prefixWord ++ tailWord_5425210) baseStart_5425210 baseEnd_5425210 := by
    simpa [prefixWord, tailWord_5425210, baseEnd_5425210] using wordTrace_append hprefix tailTrace_5425210
  have hstable : (prefixWord ++ tailWord_5425210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425210).length < 2 ^ (prefixWord ++ tailWord_5425210).sum := by decide
  have hdescent : baseEnd_5425210 < baseStart_5425210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425237 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_5425237 : Nat := 118140960795 + 5425237 * 2 ^ 59
def prefixEnd_5425237 : Nat := 4983230072969 + 3 ^ 40 * 5425237 * 2
def baseEnd_5425237 : Nat := 928584748518831822995765

theorem tailTrace_5425237 : CollatzResearch.WordTrace tailWord_5425237 prefixEnd_5425237 928584748518831822995765 := by
  unfold tailWord_5425237
  simp only [CollatzResearch.WordTrace]
  refine ⟨197874649446300380557761965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131916432964200253705174643 197874649446300380557761965)
  ·
    refine ⟨74202993542362642709160737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197874649446300380557761965 74202993542362642709160737)
    ·
      refine ⟨55652245156771982031870553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74202993542362642709160737 55652245156771982031870553)
      ·
        refine ⟨41739183867578986523902915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55652245156771982031870553 41739183867578986523902915)
        ·
          refine ⟨62608775801368479785854373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41739183867578986523902915 62608775801368479785854373)
          ·
            refine ⟨11739145462756589959847695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62608775801368479785854373 11739145462756589959847695)
            ·
              refine ⟨17608718194134884939771543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11739145462756589959847695 17608718194134884939771543)
              ·
                refine ⟨26413077291202327409657315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17608718194134884939771543 26413077291202327409657315)
                ·
                  refine ⟨39619615936803491114485973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26413077291202327409657315 39619615936803491114485973)
                  ·
                    refine ⟨928584748518831822995765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39619615936803491114485973 928584748518831822995765)
                    ·
                      rfl

theorem cell23_5425237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_5425237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425237 prefixEnd_5425237 := by exact prefixLift 5425237
  have htrace : WordTrace (prefixWord ++ tailWord_5425237) baseStart_5425237 baseEnd_5425237 := by
    simpa [prefixWord, tailWord_5425237, baseEnd_5425237] using wordTrace_append hprefix tailTrace_5425237
  have hstable : (prefixWord ++ tailWord_5425237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425237).length < 2 ^ (prefixWord ++ tailWord_5425237).sum := by decide
  have hdescent : baseEnd_5425237 < baseStart_5425237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425257 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_5425257 : Nat := 118140960795 + 5425257 * 2 ^ 59
def prefixEnd_5425257 : Nat := 4983230072969 + 3 ^ 40 * 5425257 * 2
def baseEnd_5425257 : Nat := 2785764515169585390737203

theorem tailTrace_5425257 : CollatzResearch.WordTrace tailWord_5425257 prefixEnd_5425257 2785764515169585390737203 := by
  unfold tailWord_5425257
  simp only [CollatzResearch.WordTrace]
  refine ⟨197875378906227923973490025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131916919270818615982326683 197875378906227923973490025)
  ·
    refine ⟨148406534179670942980117519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197875378906227923973490025 148406534179670942980117519)
    ·
      refine ⟨222609801269506414470176279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148406534179670942980117519 222609801269506414470176279)
      ·
        refine ⟨333914701904259621705264419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222609801269506414470176279 333914701904259621705264419)
        ·
          refine ⟨500872052856389432557896629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333914701904259621705264419 500872052856389432557896629)
          ·
            refine ⟨46956754955286509302302809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 500872052856389432557896629 46956754955286509302302809)
            ·
              refine ⟨35217566216464881976727107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46956754955286509302302809 35217566216464881976727107)
              ·
                refine ⟨52826349324697322965090661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35217566216464881976727107 52826349324697322965090661)
                ·
                  refine ⟨9904940498380748055954499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52826349324697322965090661 9904940498380748055954499)
                  ·
                    refine ⟨14857410747571122083931749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9904940498380748055954499 14857410747571122083931749)
                    ·
                      refine ⟨2785764515169585390737203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14857410747571122083931749 2785764515169585390737203)
                      ·
                        rfl

theorem cell23_5425257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_5425257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425257 prefixEnd_5425257 := by exact prefixLift 5425257
  have htrace : WordTrace (prefixWord ++ tailWord_5425257) baseStart_5425257 baseEnd_5425257 := by
    simpa [prefixWord, tailWord_5425257, baseEnd_5425257] using wordTrace_append hprefix tailTrace_5425257
  have hstable : (prefixWord ++ tailWord_5425257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425257).length < 2 ^ (prefixWord ++ tailWord_5425257).sum := by decide
  have hdescent : baseEnd_5425257 < baseStart_5425257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425284 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_5425284 : Nat := 118140960795 + 5425284 * 2 ^ 59
def prefixEnd_5425284 : Nat := 4983230072969 + 3 ^ 40 * 5425284 * 2
def baseEnd_5425284 : Nat := 928592793049085595033193

theorem tailTrace_5425284 : CollatzResearch.WordTrace tailWord_5425284 prefixEnd_5425284 928592793049085595033193 := by
  unfold tailWord_5425284
  simp only [CollatzResearch.WordTrace]
  refine ⟨98938181838565053792361453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131917575784753405056481937 98938181838565053792361453)
  ·
    refine ⟨37101818189461895172135545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98938181838565053792361453 37101818189461895172135545)
    ·
      refine ⟨27826363642096421379101659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37101818189461895172135545 27826363642096421379101659)
      ·
        refine ⟨41739545463144632068652489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27826363642096421379101659 41739545463144632068652489)
        ·
          refine ⟨31304659097358474051489367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41739545463144632068652489 31304659097358474051489367)
          ·
            refine ⟨46956988646037711077234051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31304659097358474051489367 46956988646037711077234051)
            ·
              refine ⟨70435482969056566615851077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46956988646037711077234051 70435482969056566615851077)
              ·
                refine ⟨13206653056698106240472077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70435482969056566615851077 13206653056698106240472077)
                ·
                  refine ⟨4952494896261789840177029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13206653056698106240472077 4952494896261789840177029)
                  ·
                    refine ⟨928592793049085595033193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952494896261789840177029 928592793049085595033193)
                    ·
                      rfl

theorem cell23_5425284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_5425284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425284 prefixEnd_5425284 := by exact prefixLift 5425284
  have htrace : WordTrace (prefixWord ++ tailWord_5425284) baseStart_5425284 baseEnd_5425284 := by
    simpa [prefixWord, tailWord_5425284, baseEnd_5425284] using wordTrace_append hprefix tailTrace_5425284
  have hstable : (prefixWord ++ tailWord_5425284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425284).length < 2 ^ (prefixWord ++ tailWord_5425284).sum := by decide
  have hdescent : baseEnd_5425284 < baseStart_5425284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425311 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5425311 : Nat := 118140960795 + 5425311 * 2 ^ 59
def prefixEnd_5425311 : Nat := 4983230072969 + 3 ^ 40 * 5425311 * 2
def baseEnd_5425311 : Nat := 2785792243124928179461955

theorem tailTrace_5425311 : CollatzResearch.WordTrace tailWord_5425311 prefixEnd_5425311 2785792243124928179461955 := by
  unfold tailWord_5425311
  simp only [CollatzResearch.WordTrace]
  refine ⟨197877348448032291195955787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131918232298688194130637191 197877348448032291195955787)
  ·
    refine ⟨296816022672048436793933681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197877348448032291195955787 296816022672048436793933681)
    ·
      refine ⟨222612017004036327595450261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296816022672048436793933681 222612017004036327595450261)
      ·
        refine ⟨10434938297064202856036731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222612017004036327595450261 10434938297064202856036731)
        ·
          refine ⟨15652407445596304284055097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10434938297064202856036731 15652407445596304284055097)
          ·
            refine ⟨11739305584197228213041323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15652407445596304284055097 11739305584197228213041323)
            ·
              refine ⟨17608958376295842319561985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11739305584197228213041323 17608958376295842319561985)
              ·
                refine ⟨13206718782221881739671489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17608958376295842319561985 13206718782221881739671489)
                ·
                  refine ⟨9905039086666411304753617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13206718782221881739671489 9905039086666411304753617)
                  ·
                    refine ⟨7428779314999808478565213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9905039086666411304753617 7428779314999808478565213)
                    ·
                      refine ⟨2785792243124928179461955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7428779314999808478565213 2785792243124928179461955)
                      ·
                        rfl

theorem cell23_5425311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5425311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425311 prefixEnd_5425311 := by exact prefixLift 5425311
  have htrace : WordTrace (prefixWord ++ tailWord_5425311) baseStart_5425311 baseEnd_5425311 := by
    simpa [prefixWord, tailWord_5425311, baseEnd_5425311] using wordTrace_append hprefix tailTrace_5425311
  have hstable : (prefixWord ++ tailWord_5425311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425311).length < 2 ^ (prefixWord ++ tailWord_5425311).sum := by decide
  have hdescent : baseEnd_5425311 < baseStart_5425311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425314 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_5425314 : Nat := 118140960795 + 5425314 * 2 ^ 59
def prefixEnd_5425314 : Nat := 4983230072969 + 3 ^ 40 * 5425314 * 2
def baseEnd_5425314 : Nat := 309532642618543518636049

theorem tailTrace_5425314 : CollatzResearch.WordTrace tailWord_5425314 prefixEnd_5425314 309532642618543518636049 := by
  unfold tailWord_5425314
  simp only [CollatzResearch.WordTrace]
  refine ⟨49469364466755355677078749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131918305244680948472209997 49469364466755355677078749)
  ·
    refine ⟨18551011675033258378904531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49469364466755355677078749 18551011675033258378904531)
    ·
      refine ⟨27826517512549887568356797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18551011675033258378904531 27826517512549887568356797)
      ·
        refine ⟨10434944067206207838133799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27826517512549887568356797 10434944067206207838133799)
        ·
          refine ⟨15652416100809311757200699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10434944067206207838133799 15652416100809311757200699)
          ·
            refine ⟨23478624151213967635801049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15652416100809311757200699 23478624151213967635801049)
            ·
              refine ⟨17608968113410475726850787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23478624151213967635801049 17608968113410475726850787)
              ·
                refine ⟨26413452170115713590276181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17608968113410475726850787 26413452170115713590276181)
                ·
                  refine ⟨309532642618543518636049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26413452170115713590276181 309532642618543518636049)
                  ·
                    rfl

theorem cell23_5425314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_5425314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425314 prefixEnd_5425314 := by exact prefixLift 5425314
  have htrace : WordTrace (prefixWord ++ tailWord_5425314) baseStart_5425314 baseEnd_5425314 := by
    simpa [prefixWord, tailWord_5425314, baseEnd_5425314] using wordTrace_append hprefix tailTrace_5425314
  have hstable : (prefixWord ++ tailWord_5425314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425314).length < 2 ^ (prefixWord ++ tailWord_5425314).sum := by decide
  have hdescent : baseEnd_5425314 < baseStart_5425314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425327 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 3, 5]
def baseStart_5425327 : Nat := 118140960795 + 5425327 * 2 ^ 59
def prefixEnd_5425327 : Nat := 4983230072969 + 3 ^ 40 * 5425327 * 2
def baseEnd_5425327 : Nat := 928600152938466705620627

theorem tailTrace_5425327 : CollatzResearch.WordTrace tailWord_5425327 prefixEnd_5425327 928600152938466705620627 := by
  unfold tailWord_5425327
  simp only [CollatzResearch.WordTrace]
  refine ⟨197877932015974325928538235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131918621343982883952358823 197877932015974325928538235)
  ·
    refine ⟨296816898023961488892807353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197877932015974325928538235 296816898023961488892807353)
    ·
      refine ⟨222612673517971116669605515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296816898023961488892807353 222612673517971116669605515)
      ·
        refine ⟨333919010276956675004408273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222612673517971116669605515 333919010276956675004408273)
        ·
          refine ⟨250439257707717506253306205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333919010276956675004408273 250439257707717506253306205)
          ·
            refine ⟨93914721640394064844989827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250439257707717506253306205 93914721640394064844989827)
            ·
              refine ⟨140872082460591097267484741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93914721640394064844989827 140872082460591097267484741)
              ·
                refine ⟨26413515461360830737653389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140872082460591097267484741 26413515461360830737653389)
                ·
                  refine ⟨9905068298010311526620021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26413515461360830737653389 9905068298010311526620021)
                  ·
                    refine ⟨928600152938466705620627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9905068298010311526620021 928600152938466705620627)
                    ·
                      rfl

theorem cell23_5425327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_5425327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425327 prefixEnd_5425327 := by exact prefixLift 5425327
  have htrace : WordTrace (prefixWord ++ tailWord_5425327) baseStart_5425327 baseEnd_5425327 := by
    simpa [prefixWord, tailWord_5425327, baseEnd_5425327] using wordTrace_append hprefix tailTrace_5425327
  have hstable : (prefixWord ++ tailWord_5425327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425327).length < 2 ^ (prefixWord ++ tailWord_5425327).sum := by decide
  have hdescent : baseEnd_5425327 < baseStart_5425327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425344 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_5425344 : Nat := 118140960795 + 5425344 * 2 ^ 59
def prefixEnd_5425344 : Nat := 4983230072969 + 3 ^ 40 * 5425344 * 2
def baseEnd_5425344 : Nat := 928603062662175516783101

theorem tailTrace_5425344 : CollatzResearch.WordTrace tailWord_5425344 prefixEnd_5425344 928603062662175516783101 := by
  unfold tailWord_5425344
  simp only [CollatzResearch.WordTrace]
  refine ⟨98939276028456368915953543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131919034704608491887938057 98939276028456368915953543)
  ·
    refine ⟨148408914042684553373930315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98939276028456368915953543 148408914042684553373930315)
    ·
      refine ⟨222613371064026830060895473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148408914042684553373930315 222613371064026830060895473)
      ·
        refine ⟨166960028298020122545671605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222613371064026830060895473 166960028298020122545671605)
        ·
          refine ⟨15652502652939386488656713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166960028298020122545671605 15652502652939386488656713)
          ·
            refine ⟨11739376989704539866492535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15652502652939386488656713 11739376989704539866492535)
            ·
              refine ⟨17609065484556809799738803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11739376989704539866492535 17609065484556809799738803)
              ·
                refine ⟨26413598226835214699608205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17609065484556809799738803 26413598226835214699608205)
                ·
                  refine ⟨9905099335063205512353077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26413598226835214699608205 9905099335063205512353077)
                  ·
                    refine ⟨928603062662175516783101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9905099335063205512353077 928603062662175516783101)
                    ·
                      rfl

theorem cell23_5425344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_5425344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425344 prefixEnd_5425344 := by exact prefixLift 5425344
  have htrace : WordTrace (prefixWord ++ tailWord_5425344) baseStart_5425344 baseEnd_5425344 := by
    simpa [prefixWord, tailWord_5425344, baseEnd_5425344] using wordTrace_append hprefix tailTrace_5425344
  have hstable : (prefixWord ++ tailWord_5425344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425344).length < 2 ^ (prefixWord ++ tailWord_5425344).sum := by decide
  have hdescent : baseEnd_5425344 < baseStart_5425344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425391 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 2, 4]
def baseStart_5425391 : Nat := 118140960795 + 5425391 * 2 ^ 59
def prefixEnd_5425391 : Nat := 4983230072969 + 3 ^ 40 * 5425391 * 2
def baseEnd_5425391 : Nat := 928611107192429288820529

theorem tailTrace_5425391 : CollatzResearch.WordTrace tailWord_5425391 prefixEnd_5425391 928611107192429288820529 := by
  unfold tailWord_5425391
  simp only [CollatzResearch.WordTrace]
  refine ⟨197880266287742464858868027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131920177525161643239245351 197880266287742464858868027)
  ·
    refine ⟨296820399431613697288302041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197880266287742464858868027 296820399431613697288302041)
    ·
      refine ⟨222615299573710272966226531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296820399431613697288302041 222615299573710272966226531)
      ·
        refine ⟨333922949360565409449339797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222615299573710272966226531 333922949360565409449339797)
        ·
          refine ⟨15652638251276503567937803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 333922949360565409449339797 15652638251276503567937803)
          ·
            refine ⟨23478957376914755351906705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15652638251276503567937803 23478957376914755351906705)
            ·
              refine ⟨17609218032686066513930029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23478957376914755351906705 17609218032686066513930029)
              ·
                refine ⟨6603456762257274942723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17609218032686066513930029 6603456762257274942723761)
                ·
                  refine ⟨4952592571692956207042821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6603456762257274942723761 4952592571692956207042821)
                  ·
                    refine ⟨928611107192429288820529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952592571692956207042821 928611107192429288820529)
                    ·
                      rfl

theorem cell23_5425391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_5425391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425391 prefixEnd_5425391 := by exact prefixLift 5425391
  have htrace : WordTrace (prefixWord ++ tailWord_5425391) baseStart_5425391 baseEnd_5425391 := by
    simpa [prefixWord, tailWord_5425391, baseEnd_5425391] using wordTrace_append hprefix tailTrace_5425391
  have hstable : (prefixWord ++ tailWord_5425391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425391).length < 2 ^ (prefixWord ++ tailWord_5425391).sum := by decide
  have hdescent : baseEnd_5425391 < baseStart_5425391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425398 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5425398 : Nat := 118140960795 + 5425398 * 2 ^ 59
def prefixEnd_5425398 : Nat := 4983230072969 + 3 ^ 40 * 5425398 * 2
def baseEnd_5425398 : Nat := 2785836915941869339074055

theorem tailTrace_5425398 : CollatzResearch.WordTrace tailWord_5425398 prefixEnd_5425398 2785836915941869339074055 := by
  unfold tailWord_5425398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367532599919819065898303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131920347732478070036248565 12367532599919819065898303)
  ·
    refine ⟨18551298899879728598847455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12367532599919819065898303 18551298899879728598847455)
    ·
      refine ⟨27826948349819592898271183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18551298899879728598847455 27826948349819592898271183)
      ·
        refine ⟨41740422524729389347406775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27826948349819592898271183 41740422524729389347406775)
        ·
          refine ⟨62610633787094084021110163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41740422524729389347406775 62610633787094084021110163)
          ·
            refine ⟨93915950680641126031665245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62610633787094084021110163 93915950680641126031665245)
            ·
              refine ⟨35218481505240422261874467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93915950680641126031665245 35218481505240422261874467)
              ·
                refine ⟨52827722257860633392811701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35218481505240422261874467 52827722257860633392811701)
                ·
                  refine ⟨4952598961674434380576097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52827722257860633392811701 4952598961674434380576097)
                  ·
                    refine ⟨3714449221255825785432073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4952598961674434380576097 3714449221255825785432073)
                    ·
                      refine ⟨2785836915941869339074055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714449221255825785432073 2785836915941869339074055)
                      ·
                        rfl

theorem cell23_5425398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5425398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425398 prefixEnd_5425398 := by exact prefixLift 5425398
  have htrace : WordTrace (prefixWord ++ tailWord_5425398) baseStart_5425398 baseEnd_5425398 := by
    simpa [prefixWord, tailWord_5425398, baseEnd_5425398] using wordTrace_append hprefix tailTrace_5425398
  have hstable : (prefixWord ++ tailWord_5425398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425398).length < 2 ^ (prefixWord ++ tailWord_5425398).sum := by decide
  have hdescent : baseEnd_5425398 < baseStart_5425398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425418 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_5425418 : Nat := 118140960795 + 5425418 * 2 ^ 59
def prefixEnd_5425418 : Nat := 4983230072969 + 3 ^ 40 * 5425418 * 2
def baseEnd_5425418 : Nat := 2785847185554959260823963

theorem tailTrace_5425418 : CollatzResearch.WordTrace tailWord_5425418 prefixEnd_5425418 2785847185554959260823963 := by
  unfold tailWord_5425418
  simp only [CollatzResearch.WordTrace]
  refine ⟨49470312764661162117525227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131920834039096432313400605 49470312764661162117525227)
  ·
    refine ⟨74205469146991743176287841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49470312764661162117525227 74205469146991743176287841)
    ·
      refine ⟨55654101860243807382215881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74205469146991743176287841 55654101860243807382215881)
      ·
        refine ⟨41740576395182855536661911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55654101860243807382215881 41740576395182855536661911)
        ·
          refine ⟨62610864592774283304992867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41740576395182855536661911 62610864592774283304992867)
          ·
            refine ⟨93916296889161424957489301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62610864592774283304992867 93916296889161424957489301)
            ·
              refine ⟨4402326416679441794882311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93916296889161424957489301 4402326416679441794882311)
              ·
                refine ⟨6603489625019162692323467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402326416679441794882311 6603489625019162692323467)
                ·
                  refine ⟨9905234437528744038485201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6603489625019162692323467 9905234437528744038485201)
                  ·
                    refine ⟨7428925828146558028863901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9905234437528744038485201 7428925828146558028863901)
                    ·
                      refine ⟨2785847185554959260823963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7428925828146558028863901 2785847185554959260823963)
                      ·
                        rfl

theorem cell23_5425418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_5425418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425418 prefixEnd_5425418 := by exact prefixLift 5425418
  have htrace : WordTrace (prefixWord ++ tailWord_5425418) baseStart_5425418 baseEnd_5425418 := by
    simpa [prefixWord, tailWord_5425418, baseEnd_5425418] using wordTrace_append hprefix tailTrace_5425418
  have hstable : (prefixWord ++ tailWord_5425418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425418).length < 2 ^ (prefixWord ++ tailWord_5425418).sum := by decide
  have hdescent : baseEnd_5425418 < baseStart_5425418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425441 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_5425441 : Nat := 118140960795 + 5425441 * 2 ^ 59
def prefixEnd_5425441 : Nat := 4983230072969 + 3 ^ 40 * 5425441 * 2
def baseEnd_5425441 : Nat := 2785858995610012670836357

theorem tailTrace_5425441 : CollatzResearch.WordTrace tailWord_5425441 prefixEnd_5425441 2785858995610012670836357 := by
  unfold tailWord_5425441
  simp only [CollatzResearch.WordTrace]
  refine ⟨197882089937561323398188177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131921393291707548932125451 197882089937561323398188177)
  ·
    refine ⟨148411567453170992548641133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197882089937561323398188177 148411567453170992548641133)
    ·
      refine ⟨55654337794939122205740425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148411567453170992548641133 55654337794939122205740425)
      ·
        refine ⟨41740753346204341654305319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55654337794939122205740425 41740753346204341654305319)
        ·
          refine ⟨62611130019306512481457979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41740753346204341654305319 62611130019306512481457979)
          ·
            refine ⟨93916695028959768722186969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62611130019306512481457979 93916695028959768722186969)
            ·
              refine ⟨70437521271719826541640227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93916695028959768722186969 70437521271719826541640227)
              ·
                refine ⟨105656281907579739812460341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70437521271719826541640227 105656281907579739812460341)
                ·
                  refine ⟨9905276428835600607418157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105656281907579739812460341 9905276428835600607418157)
                  ·
                    refine ⟨3714478660813350227781809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9905276428835600607418157 3714478660813350227781809)
                    ·
                      refine ⟨2785858995610012670836357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714478660813350227781809 2785858995610012670836357)
                      ·
                        rfl

theorem cell23_5425441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_5425441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425441 prefixEnd_5425441 := by exact prefixLift 5425441
  have htrace : WordTrace (prefixWord ++ tailWord_5425441) baseStart_5425441 baseEnd_5425441 := by
    simpa [prefixWord, tailWord_5425441, baseEnd_5425441] using wordTrace_append hprefix tailTrace_5425441
  have hstable : (prefixWord ++ tailWord_5425441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425441).length < 2 ^ (prefixWord ++ tailWord_5425441).sum := by decide
  have hdescent : baseEnd_5425441 < baseStart_5425441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425471 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 3, 4, 2]
def baseStart_5425471 : Nat := 118140960795 + 5425471 * 2 ^ 59
def prefixEnd_5425471 : Nat := 4983230072969 + 3 ^ 40 * 5425471 * 2
def baseEnd_5425471 : Nat := 2785874400029647553461219

theorem tailTrace_5425471 : CollatzResearch.WordTrace tailWord_5425471 prefixEnd_5425471 2785874400029647553461219 := by
  unfold tailWord_5425471
  simp only [CollatzResearch.WordTrace]
  refine ⟨197883184127452638521780267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131922122751635092347853511 197883184127452638521780267)
  ·
    refine ⟨296824776191178957782670401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197883184127452638521780267 296824776191178957782670401)
    ·
      refine ⟨222618582143384218337002801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296824776191178957782670401 222618582143384218337002801)
      ·
        refine ⟨166963936607538163752752101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222618582143384218337002801 166963936607538163752752101)
        ·
          refine ⟨31305738113913405703641019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166963936607538163752752101 31305738113913405703641019)
          ·
            refine ⟨46958607170870108555461529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31305738113913405703641019 46958607170870108555461529)
            ·
              refine ⟨35218955378152581416596147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46958607170870108555461529 35218955378152581416596147)
              ·
                refine ⟨52828433067228872124894221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35218955378152581416596147 52828433067228872124894221)
                ·
                  refine ⟨19810662400210827046835333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52828433067228872124894221 19810662400210827046835333)
                  ·
                    refine ⟨3714499200039530071281625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19810662400210827046835333 3714499200039530071281625)
                    ·
                      refine ⟨2785874400029647553461219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714499200039530071281625 2785874400029647553461219)
                      ·
                        rfl

theorem cell23_5425471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_5425471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425471 prefixEnd_5425471 := by exact prefixLift 5425471
  have htrace : WordTrace (prefixWord ++ tailWord_5425471) baseStart_5425471 baseEnd_5425471 := by
    simpa [prefixWord, tailWord_5425471, baseEnd_5425471] using wordTrace_append hprefix tailTrace_5425471
  have hstable : (prefixWord ++ tailWord_5425471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425471).length < 2 ^ (prefixWord ++ tailWord_5425471).sum := by decide
  have hdescent : baseEnd_5425471 < baseStart_5425471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425488 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 4, 2, 2]
def baseStart_5425488 : Nat := 118140960795 + 5425488 * 2 ^ 59
def prefixEnd_5425488 : Nat := 4983230072969 + 3 ^ 40 * 5425488 * 2
def baseEnd_5425488 : Nat := 2785883129200773986948641

theorem tailTrace_5425488 : CollatzResearch.WordTrace tailWord_5425488 prefixEnd_5425488 2785883129200773986948641 := by
  unfold tailWord_5425488
  simp only [CollatzResearch.WordTrace]
  refine ⟨98941902084195525212574559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131922536112260700283432745 98941902084195525212574559)
  ·
    refine ⟨148412853126293287818861839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98941902084195525212574559 148412853126293287818861839)
    ·
      refine ⟨222619279689439931728292759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148412853126293287818861839 222619279689439931728292759)
      ·
        refine ⟨333928919534159897592439139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222619279689439931728292759 333928919534159897592439139)
        ·
          refine ⟨500893379301239846388658709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333928919534159897592439139 500893379301239846388658709)
          ·
            refine ⟨23479377154745617799468377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 500893379301239846388658709 23479377154745617799468377)
            ·
              refine ⟨17609532866059213349601283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23479377154745617799468377 17609532866059213349601283)
              ·
                refine ⟨26414299299088820024401925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17609532866059213349601283 26414299299088820024401925)
                ·
                  refine ⟨4952681118579153754575361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26414299299088820024401925 4952681118579153754575361)
                  ·
                    refine ⟨3714510838934365315931521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4952681118579153754575361 3714510838934365315931521)
                    ·
                      refine ⟨2785883129200773986948641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714510838934365315931521 2785883129200773986948641)
                      ·
                        rfl

theorem cell23_5425488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 2, 2].length) (baseStart_5425488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425488 prefixEnd_5425488 := by exact prefixLift 5425488
  have htrace : WordTrace (prefixWord ++ tailWord_5425488) baseStart_5425488 baseEnd_5425488 := by
    simpa [prefixWord, tailWord_5425488, baseEnd_5425488] using wordTrace_append hprefix tailTrace_5425488
  have hstable : (prefixWord ++ tailWord_5425488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425488).length < 2 ^ (prefixWord ++ tailWord_5425488).sum := by decide
  have hdescent : baseEnd_5425488 < baseStart_5425488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425545 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 5]
def baseStart_5425545 : Nat := 118140960795 + 5425545 * 2 ^ 59
def prefixEnd_5425545 : Nat := 4983230072969 + 3 ^ 40 * 5425545 * 2
def baseEnd_5425545 : Nat := 309545821955342251548431

theorem tailTrace_5425545 : CollatzResearch.WordTrace tailWord_5425545 prefixEnd_5425545 309545821955342251548431 := by
  unfold tailWord_5425545
  simp only [CollatzResearch.WordTrace]
  refine ⟨197885883129184549159974089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131923922086123032773316059 197885883129184549159974089)
  ·
    refine ⟨148414412346888411869980567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197885883129184549159974089 148414412346888411869980567)
    ·
      refine ⟨222621618520332617804970851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148414412346888411869980567 222621618520332617804970851)
      ·
        refine ⟨333932427780498926707456277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222621618520332617804970851 333932427780498926707456277)
        ·
          refine ⟨15653082552210887189412013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 333932427780498926707456277 15653082552210887189412013)
          ·
            refine ⟨5869905957079082696029505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15653082552210887189412013 5869905957079082696029505)
            ·
              refine ⟨4402429467809312022022129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5869905957079082696029505 4402429467809312022022129)
              ·
                refine ⟨3301822100856984016516597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4402429467809312022022129 3301822100856984016516597)
                ·
                  refine ⟨309545821955342251548431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301822100856984016516597 309545821955342251548431)
                  ·
                    rfl

theorem cell23_5425545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 5].length) (baseStart_5425545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425545 prefixEnd_5425545 := by exact prefixLift 5425545
  have htrace : WordTrace (prefixWord ++ tailWord_5425545) baseStart_5425545 baseEnd_5425545 := by
    simpa [prefixWord, tailWord_5425545, baseEnd_5425545] using wordTrace_append hprefix tailTrace_5425545
  have hstable : (prefixWord ++ tailWord_5425545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425545).length < 2 ^ (prefixWord ++ tailWord_5425545).sum := by decide
  have hdescent : baseEnd_5425545 < baseStart_5425545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425571 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 5, 4]
def baseStart_5425571 : Nat := 118140960795 + 5425571 * 2 ^ 59
def prefixEnd_5425571 : Nat := 4983230072969 + 3 ^ 40 * 5425571 * 2
def baseEnd_5425571 : Nat := 928641916031699054070253

theorem tailTrace_5425571 : CollatzResearch.WordTrace tailWord_5425571 prefixEnd_5425571 928641916031699054070253 := by
  unfold tailWord_5425571
  simp only [CollatzResearch.WordTrace]
  refine ⟨197886831427090355600420567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131924554284726903733613711 197886831427090355600420567)
  ·
    refine ⟨296830247140635533400630851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197886831427090355600420567 296830247140635533400630851)
    ·
      refine ⟨445245370710953300100946277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296830247140635533400630851 445245370710953300100946277)
      ·
        refine ⟨83483507008303743768927427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 445245370710953300100946277 83483507008303743768927427)
        ·
          refine ⟨125225260512455615653391141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83483507008303743768927427 125225260512455615653391141)
          ·
            refine ⟨23479736346085427935010839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125225260512455615653391141 23479736346085427935010839)
            ·
              refine ⟨35219604519128141902516259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23479736346085427935010839 35219604519128141902516259)
              ·
                refine ⟨52829406778692212853774389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35219604519128141902516259 52829406778692212853774389)
                ·
                  refine ⟨4952756885502394955041349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52829406778692212853774389 4952756885502394955041349)
                  ·
                    refine ⟨928641916031699054070253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952756885502394955041349 928641916031699054070253)
                    ·
                      rfl

theorem cell23_5425571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 4].length) (baseStart_5425571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425571 prefixEnd_5425571 := by exact prefixLift 5425571
  have htrace : WordTrace (prefixWord ++ tailWord_5425571) baseStart_5425571 baseEnd_5425571 := by
    simpa [prefixWord, tailWord_5425571, baseEnd_5425571] using wordTrace_append hprefix tailTrace_5425571
  have hstable : (prefixWord ++ tailWord_5425571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425571).length < 2 ^ (prefixWord ++ tailWord_5425571).sum := by decide
  have hdescent : baseEnd_5425571 < baseStart_5425571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425598 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_5425598 : Nat := 118140960795 + 5425598 * 2 ^ 59
def prefixEnd_5425598 : Nat := 4983230072969 + 3 ^ 40 * 5425598 * 2
def baseEnd_5425598 : Nat := 2785939612072768556573135

theorem tailTrace_5425598 : CollatzResearch.WordTrace tailWord_5425598 prefixEnd_5425598 2785939612072768556573135 := by
  unfold tailWord_5425598
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735977024749067401456681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131925210798661692807768965 24735977024749067401456681)
  ·
    refine ⟨18551982768561800551092511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24735977024749067401456681 18551982768561800551092511)
    ·
      refine ⟨27827974152842700826638767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18551982768561800551092511 27827974152842700826638767)
      ·
        refine ⟨41741961229264051239958151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27827974152842700826638767 41741961229264051239958151)
        ·
          refine ⟨62612941843896076859937227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41741961229264051239958151 62612941843896076859937227)
          ·
            refine ⟨93919412765844115289905841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62612941843896076859937227 93919412765844115289905841)
            ·
              refine ⟨70439559574383086467429381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93919412765844115289905841 70439559574383086467429381)
              ·
                refine ⟨13207417420196828712643009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70439559574383086467429381 13207417420196828712643009)
                ·
                  refine ⟨9905563065147621534482257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13207417420196828712643009 9905563065147621534482257)
                  ·
                    refine ⟨7429172298860716150861693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9905563065147621534482257 7429172298860716150861693)
                    ·
                      refine ⟨2785939612072768556573135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7429172298860716150861693 2785939612072768556573135)
                      ·
                        rfl

theorem cell23_5425598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_5425598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425598 prefixEnd_5425598 := by exact prefixLift 5425598
  have htrace : WordTrace (prefixWord ++ tailWord_5425598) baseStart_5425598 baseEnd_5425598 := by
    simpa [prefixWord, tailWord_5425598, baseEnd_5425598] using wordTrace_append hprefix tailTrace_5425598
  have hstable : (prefixWord ++ tailWord_5425598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425598).length < 2 ^ (prefixWord ++ tailWord_5425598).sum := by decide
  have hdescent : baseEnd_5425598 < baseStart_5425598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425685 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_5425685 : Nat := 118140960795 + 5425685 * 2 ^ 59
def prefixEnd_5425685 : Nat := 4983230072969 + 3 ^ 40 * 5425685 * 2
def baseEnd_5425685 : Nat := 2785984284889709716185235

theorem tailTrace_5425685 : CollatzResearch.WordTrace tailWord_5425685 prefixEnd_5425685 2785984284889709716185235 := by
  unfold tailWord_5425685
  simp only [CollatzResearch.WordTrace]
  refine ⟨197890989348677353070070509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131927326232451568713380339 197890989348677353070070509)
  ·
    refine ⟨74209121005754007401276441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197890989348677353070070509 74209121005754007401276441)
    ·
      refine ⟨55656840754315505550957331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74209121005754007401276441 55656840754315505550957331)
      ·
        refine ⟨83485261131473258326435997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55656840754315505550957331 83485261131473258326435997)
        ·
          refine ⟨31306972924302471872413499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83485261131473258326435997 31306972924302471872413499)
          ·
            refine ⟨46960459386453707808620249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31306972924302471872413499 46960459386453707808620249)
            ·
              refine ⟨35220344539840280856465187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46960459386453707808620249 35220344539840280856465187)
              ·
                refine ⟨52830516809760421284697781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35220344539840280856465187 52830516809760421284697781)
                ·
                  refine ⟨4952860950915039495440417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52830516809760421284697781 4952860950915039495440417)
                  ·
                    refine ⟨3714645713186279621580313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4952860950915039495440417 3714645713186279621580313)
                    ·
                      refine ⟨2785984284889709716185235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714645713186279621580313 2785984284889709716185235)
                      ·
                        rfl

theorem cell23_5425685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_5425685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425685 prefixEnd_5425685 := by exact prefixLift 5425685
  have htrace : WordTrace (prefixWord ++ tailWord_5425685) baseStart_5425685 baseEnd_5425685 := by
    simpa [prefixWord, tailWord_5425685, baseEnd_5425685] using wordTrace_append hprefix tailTrace_5425685
  have hstable : (prefixWord ++ tailWord_5425685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425685).length < 2 ^ (prefixWord ++ tailWord_5425685).sum := by decide
  have hdescent : baseEnd_5425685 < baseStart_5425685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425721 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_5425721 : Nat := 118140960795 + 5425721 * 2 ^ 59
def prefixEnd_5425721 : Nat := 4983230072969 + 3 ^ 40 * 5425721 * 2
def baseEnd_5425721 : Nat := 928667590064423858445023

theorem tailTrace_5425721 : CollatzResearch.WordTrace tailWord_5425721 prefixEnd_5425721 928667590064423858445023 := by
  unfold tailWord_5425721
  simp only [CollatzResearch.WordTrace]
  refine ⟨197892302376546931218381017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131928201584364620812254011 197892302376546931218381017)
  ·
    refine ⟨148419226782410198413785763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197892302376546931218381017 148419226782410198413785763)
    ·
      refine ⟨222628840173615297620678645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148419226782410198413785763 222628840173615297620678645)
      ·
        refine ⟨20871453766276434151938623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222628840173615297620678645 20871453766276434151938623)
        ·
          refine ⟨31307180649414651227907935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20871453766276434151938623 31307180649414651227907935)
          ·
            refine ⟨46960770974121976841861903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31307180649414651227907935 46960770974121976841861903)
            ·
              refine ⟨70441156461182965262792855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46960770974121976841861903 70441156461182965262792855)
              ·
                refine ⟨105661734691774447894189283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70441156461182965262792855 105661734691774447894189283)
                ·
                  refine ⟨158492602037661671841283925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105661734691774447894189283 158492602037661671841283925)
                  ·
                    refine ⟨928667590064423858445023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158492602037661671841283925 928667590064423858445023)
                    ·
                      rfl

theorem cell23_5425721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_5425721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425721 prefixEnd_5425721 := by exact prefixLift 5425721
  have htrace : WordTrace (prefixWord ++ tailWord_5425721) baseStart_5425721 baseEnd_5425721 := by
    simpa [prefixWord, tailWord_5425721, baseEnd_5425721] using wordTrace_append hprefix tailTrace_5425721
  have hstable : (prefixWord ++ tailWord_5425721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425721).length < 2 ^ (prefixWord ++ tailWord_5425721).sum := by decide
  have hdescent : baseEnd_5425721 < baseStart_5425721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425735 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_5425735 : Nat := 118140960795 + 5425735 * 2 ^ 59
def prefixEnd_5425735 : Nat := 4983230072969 + 3 ^ 40 * 5425735 * 2
def baseEnd_5425735 : Nat := 2786009958922434520560005

theorem tailTrace_5425735 : CollatzResearch.WordTrace tailWord_5425735 prefixEnd_5425735 2786009958922434520560005 := by
  unfold tailWord_5425735
  simp only [CollatzResearch.WordTrace]
  refine ⟨197892812998496211609390659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131928541998997474406260439 197892812998496211609390659)
  ·
    refine ⟨296839219497744317414085989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197892812998496211609390659 296839219497744317414085989)
    ·
      refine ⟨55657353655827059515141123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296839219497744317414085989 55657353655827059515141123)
      ·
        refine ⟨83486030483740589272711685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55657353655827059515141123 83486030483740589272711685)
        ·
          refine ⟨15653630715701360488633441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83486030483740589272711685 15653630715701360488633441)
          ·
            refine ⟨11740223036776020366475081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15653630715701360488633441 11740223036776020366475081)
            ·
              refine ⟨8805167277582015274856311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11740223036776020366475081 8805167277582015274856311)
              ·
                refine ⟨13207750916373022912284467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8805167277582015274856311 13207750916373022912284467)
                ·
                  refine ⟨19811626374559534368426701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13207750916373022912284467 19811626374559534368426701)
                  ·
                    refine ⟨7429359890459825388160013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19811626374559534368426701 7429359890459825388160013)
                    ·
                      refine ⟨2786009958922434520560005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7429359890459825388160013 2786009958922434520560005)
                      ·
                        rfl

theorem cell23_5425735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_5425735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425735 prefixEnd_5425735 := by exact prefixLift 5425735
  have htrace : WordTrace (prefixWord ++ tailWord_5425735) baseStart_5425735 baseEnd_5425735 := by
    simpa [prefixWord, tailWord_5425735, baseEnd_5425735] using wordTrace_append hprefix tailTrace_5425735
  have hstable : (prefixWord ++ tailWord_5425735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425735).length < 2 ^ (prefixWord ++ tailWord_5425735).sum := by decide
  have hdescent : baseEnd_5425735 < baseStart_5425735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425745 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 3, 3, 2]
def baseStart_5425745 : Nat := 118140960795 + 5425745 * 2 ^ 59
def prefixEnd_5425745 : Nat := 4983230072969 + 3 ^ 40 * 5425745 * 2
def baseEnd_5425745 : Nat := 2786015093728979481434959

theorem tailTrace_5425745 : CollatzResearch.WordTrace tailWord_5425745 prefixEnd_5425745 2786015093728979481434959 := by
  unfold tailWord_5425745
  simp only [CollatzResearch.WordTrace]
  refine ⟨197893177728459983317254689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131928785152306655544836459 197893177728459983317254689)
  ·
    refine ⟨148419883296344987487941017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197893177728459983317254689 148419883296344987487941017)
    ·
      refine ⟨111314912472258740615955763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148419883296344987487941017 111314912472258740615955763)
      ·
        refine ⟨166972368708388110923933645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111314912472258740615955763 166972368708388110923933645)
        ·
          refine ⟨62614638265645541596475117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166972368708388110923933645 62614638265645541596475117)
          ·
            refine ⟨23480489349617078098678169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62614638265645541596475117 23480489349617078098678169)
            ·
              refine ⟨17610367012212808574008627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23480489349617078098678169 17610367012212808574008627)
              ·
                refine ⟨26415550518319212861012941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17610367012212808574008627 26415550518319212861012941)
                ·
                  refine ⟨9905831444369704822879853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26415550518319212861012941 9905831444369704822879853)
                  ·
                    refine ⟨3714686791638639308579945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9905831444369704822879853 3714686791638639308579945)
                    ·
                      refine ⟨2786015093728979481434959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714686791638639308579945 2786015093728979481434959)
                      ·
                        rfl

theorem cell23_5425745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_5425745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425745 prefixEnd_5425745 := by exact prefixLift 5425745
  have htrace : WordTrace (prefixWord ++ tailWord_5425745) baseStart_5425745 baseEnd_5425745 := by
    simpa [prefixWord, tailWord_5425745, baseEnd_5425745] using wordTrace_append hprefix tailTrace_5425745
  have hstable : (prefixWord ++ tailWord_5425745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425745).length < 2 ^ (prefixWord ++ tailWord_5425745).sum := by decide
  have hdescent : baseEnd_5425745 < baseStart_5425745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425751 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 8]
def baseStart_5425751 : Nat := 118140960795 + 5425751 * 2 ^ 59
def prefixEnd_5425751 : Nat := 4983230072969 + 3 ^ 40 * 5425751 * 2
def baseEnd_5425751 : Nat := 928672724870968819319977

theorem tailTrace_5425751 : CollatzResearch.WordTrace tailWord_5425751 prefixEnd_5425751 928672724870968819319977 := by
  unfold tailWord_5425751
  simp only [CollatzResearch.WordTrace]
  refine ⟨197893396566438246341973107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131928931044292164227982071 197893396566438246341973107)
  ·
    refine ⟨296840094849657369512959661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197893396566438246341973107 296840094849657369512959661)
    ·
      refine ⟨111315035568621513567359873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296840094849657369512959661 111315035568621513567359873)
      ·
        refine ⟨83486276676466135175519905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111315035568621513567359873 83486276676466135175519905)
        ·
          refine ⟨62614707507349601381639929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83486276676466135175519905 62614707507349601381639929)
          ·
            refine ⟨46961030630512201036229947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62614707507349601381639929 46961030630512201036229947)
            ·
              refine ⟨70441545945768301554344921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46961030630512201036229947 70441545945768301554344921)
              ·
                refine ⟨52831159459326226165758691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70441545945768301554344921 52831159459326226165758691)
                ·
                  refine ⟨79246739188989339248638037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52831159459326226165758691 79246739188989339248638037)
                  ·
                    refine ⟨928672724870968819319977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79246739188989339248638037 928672724870968819319977)
                    ·
                      rfl

theorem cell23_5425751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_5425751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425751 prefixEnd_5425751 := by exact prefixLift 5425751
  have htrace : WordTrace (prefixWord ++ tailWord_5425751) baseStart_5425751 baseEnd_5425751 := by
    simpa [prefixWord, tailWord_5425751, baseEnd_5425751] using wordTrace_append hprefix tailTrace_5425751
  have hstable : (prefixWord ++ tailWord_5425751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425751).length < 2 ^ (prefixWord ++ tailWord_5425751).sum := by decide
  have hdescent : baseEnd_5425751 < baseStart_5425751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425756 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_5425756 : Nat := 118140960795 + 5425756 * 2 ^ 59
def prefixEnd_5425756 : Nat := 4983230072969 + 3 ^ 40 * 5425756 * 2
def baseEnd_5425756 : Nat := 2786020742016178938397409

theorem tailTrace_5425756 : CollatzResearch.WordTrace tailWord_5425756 prefixEnd_5425756 2786020742016178938397409 := by
  unfold tailWord_5425756
  simp only [CollatzResearch.WordTrace]
  refine ⟨98946789465710066097952561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131929052620946754797270081 98946789465710066097952561)
  ·
    refine ⟨74210092099282549573464421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98946789465710066097952561 74210092099282549573464421)
    ·
      refine ⟨13914392268615478045024579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74210092099282549573464421 13914392268615478045024579)
      ·
        refine ⟨20871588402923217067536869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13914392268615478045024579 20871588402923217067536869)
        ·
          refine ⟨3913422825548103200163163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20871588402923217067536869 3913422825548103200163163)
          ·
            refine ⟨5870134238322154800244745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913422825548103200163163 5870134238322154800244745)
            ·
              refine ⟨4402600678741616100183559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5870134238322154800244745 4402600678741616100183559)
              ·
                refine ⟨6603901018112424150275339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402600678741616100183559 6603901018112424150275339)
                ·
                  refine ⟨9905851527168636225413009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6603901018112424150275339 9905851527168636225413009)
                  ·
                    refine ⟨7429388645376477169059757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9905851527168636225413009 7429388645376477169059757)
                    ·
                      refine ⟨2786020742016178938397409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7429388645376477169059757 2786020742016178938397409)
                      ·
                        rfl

theorem cell23_5425756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_5425756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425756 prefixEnd_5425756 := by exact prefixLift 5425756
  have htrace : WordTrace (prefixWord ++ tailWord_5425756) baseStart_5425756 baseEnd_5425756 := by
    simpa [prefixWord, tailWord_5425756, baseEnd_5425756] using wordTrace_append hprefix tailTrace_5425756
  have hstable : (prefixWord ++ tailWord_5425756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425756).length < 2 ^ (prefixWord ++ tailWord_5425756).sum := by decide
  have hdescent : baseEnd_5425756 < baseStart_5425756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425788 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_5425788 : Nat := 118140960795 + 5425788 * 2 ^ 59
def prefixEnd_5425788 : Nat := 4983230072969 + 3 ^ 40 * 5425788 * 2
def baseEnd_5425788 : Nat := 2786037173397122813197261

theorem tailTrace_5425788 : CollatzResearch.WordTrace tailWord_5425788 prefixEnd_5425788 2786037173397122813197261 := by
  unfold tailWord_5425788
  simp only [CollatzResearch.WordTrace]
  refine ⟨98947373033652100830535009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131929830711536134440713345 98947373033652100830535009)
  ·
    refine ⟨74210529775239075622901257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98947373033652100830535009 74210529775239075622901257)
    ·
      refine ⟨55657897331429306717175943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74210529775239075622901257 55657897331429306717175943)
      ·
        refine ⟨83486845997143960075763915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55657897331429306717175943 83486845997143960075763915)
        ·
          refine ⟨125230268995715940113645873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83486845997143960075763915 125230268995715940113645873)
          ·
            refine ⟨93922701746786955085234405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125230268995715940113645873 93922701746786955085234405)
            ·
              refine ⟨17610506577522554078481451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93922701746786955085234405 17610506577522554078481451)
              ·
                refine ⟨26415759866283831117722177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17610506577522554078481451 26415759866283831117722177)
                ·
                  refine ⟨19811819899712873338291633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26415759866283831117722177 19811819899712873338291633)
                  ·
                    refine ⟨14858864924784655003718725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19811819899712873338291633 14858864924784655003718725)
                    ·
                      refine ⟨2786037173397122813197261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14858864924784655003718725 2786037173397122813197261)
                      ·
                        rfl

theorem cell23_5425788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_5425788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425788 prefixEnd_5425788 := by exact prefixLift 5425788
  have htrace : WordTrace (prefixWord ++ tailWord_5425788) baseStart_5425788 baseEnd_5425788 := by
    simpa [prefixWord, tailWord_5425788, baseEnd_5425788] using wordTrace_append hprefix tailTrace_5425788
  have hstable : (prefixWord ++ tailWord_5425788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425788).length < 2 ^ (prefixWord ++ tailWord_5425788).sum := by decide
  have hdescent : baseEnd_5425788 < baseStart_5425788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425792 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 1, 4, 2]
def baseStart_5425792 : Nat := 118140960795 + 5425792 * 2 ^ 59
def prefixEnd_5425792 : Nat := 4983230072969 + 3 ^ 40 * 5425792 * 2
def baseEnd_5425792 : Nat := 2786039227319740797547243

theorem tailTrace_5425792 : CollatzResearch.WordTrace tailWord_5425792 prefixEnd_5425792 2786039227319740797547243 := by
  unfold tailWord_5425792
  simp only [CollatzResearch.WordTrace]
  refine ⟨98947445979644855172107815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131929927972859806896143753 98947445979644855172107815)
  ·
    refine ⟨148421168969467282758161723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98947445979644855172107815 148421168969467282758161723)
    ·
      refine ⟨222631753454200924137242585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148421168969467282758161723 222631753454200924137242585)
      ·
        refine ⟨166973815090650693102931939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222631753454200924137242585 166973815090650693102931939)
        ·
          refine ⟨250460722635976039654397909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166973815090650693102931939 250460722635976039654397909)
          ·
            refine ⟨5870173186780688429399951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 250460722635976039654397909 5870173186780688429399951)
            ·
              refine ⟨8805259780171032644099927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870173186780688429399951 8805259780171032644099927)
              ·
                refine ⟨13207889670256548966149891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8805259780171032644099927 13207889670256548966149891)
                ·
                  refine ⟨19811834505384823449224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13207889670256548966149891 19811834505384823449224837)
                  ·
                    refine ⟨3714718969759654396729657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19811834505384823449224837 3714718969759654396729657)
                    ·
                      refine ⟨2786039227319740797547243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714718969759654396729657 2786039227319740797547243)
                      ·
                        rfl

theorem cell23_5425792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_5425792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425792 prefixEnd_5425792 := by exact prefixLift 5425792
  have htrace : WordTrace (prefixWord ++ tailWord_5425792) baseStart_5425792 baseEnd_5425792 := by
    simpa [prefixWord, tailWord_5425792, baseEnd_5425792] using wordTrace_append hprefix tailTrace_5425792
  have hstable : (prefixWord ++ tailWord_5425792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425792).length < 2 ^ (prefixWord ++ tailWord_5425792).sum := by decide
  have hdescent : baseEnd_5425792 < baseStart_5425792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425935 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 1, 5]
def baseStart_5425935 : Nat := 118140960795 + 5425935 * 2 ^ 59
def prefixEnd_5425935 : Nat := 4983230072969 + 3 ^ 40 * 5425935 * 2
def baseEnd_5425935 : Nat := 928704218351111246019695

theorem tailTrace_5425935 : CollatzResearch.WordTrace tailWord_5425935 prefixEnd_5425935 928704218351111246019695 := by
  unfold tailWord_5425935
  simp only [CollatzResearch.WordTrace]
  refine ⟨197900107597771645766671259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131933405065181097177780839 197900107597771645766671259)
  ·
    refine ⟨296850161396657468650006889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197900107597771645766671259 296850161396657468650006889)
    ·
      refine ⟨222637621047493101487505167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296850161396657468650006889 222637621047493101487505167)
      ·
        refine ⟨333956431571239652231257751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222637621047493101487505167 333956431571239652231257751)
        ·
          refine ⟨500934647356859478346886627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333956431571239652231257751 500934647356859478346886627)
          ·
            refine ⟨751401971035289217520329941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500934647356859478346886627 751401971035289217520329941)
            ·
              refine ⟨17610983696139591035632733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 751401971035289217520329941 17610983696139591035632733)
              ·
                refine ⟨6604118886052346638362275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17610983696139591035632733 6604118886052346638362275)
                ·
                  refine ⟨9906178329078519957543413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6604118886052346638362275 9906178329078519957543413)
                  ·
                    refine ⟨928704218351111246019695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9906178329078519957543413 928704218351111246019695)
                    ·
                      rfl

theorem cell23_5425935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_5425935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425935 prefixEnd_5425935 := by exact prefixLift 5425935
  have htrace : WordTrace (prefixWord ++ tailWord_5425935) baseStart_5425935 baseEnd_5425935 := by
    simpa [prefixWord, tailWord_5425935, baseEnd_5425935] using wordTrace_append hprefix tailTrace_5425935
  have hstable : (prefixWord ++ tailWord_5425935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425935).length < 2 ^ (prefixWord ++ tailWord_5425935).sum := by decide
  have hdescent : baseEnd_5425935 < baseStart_5425935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5425992 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_5425992 : Nat := 118140960795 + 5425992 * 2 ^ 59
def prefixEnd_5425992 : Nat := 4983230072969 + 3 ^ 40 * 5425992 * 2
def baseEnd_5425992 : Nat := 2786141923450640015046323

theorem tailTrace_5425992 : CollatzResearch.WordTrace tailWord_5425992 prefixEnd_5425992 2786141923450640015046323 := by
  unfold tailWord_5425992
  simp only [CollatzResearch.WordTrace]
  refine ⟨98951093279282572250748115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131934791039043429667664153 98951093279282572250748115)
  ·
    refine ⟨148426639918923858376122173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98951093279282572250748115 148426639918923858376122173)
    ·
      refine ⟨55659989969596446891045815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148426639918923858376122173 55659989969596446891045815)
      ·
        refine ⟨83489984954394670336568723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55659989969596446891045815 83489984954394670336568723)
        ·
          refine ⟨125234977431592005504853085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83489984954394670336568723 125234977431592005504853085)
          ·
            refine ⟨46963116536847002064319907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125234977431592005504853085 46963116536847002064319907)
            ·
              refine ⟨70444674805270503096479861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46963116536847002064319907 70444674805270503096479861)
              ·
                refine ⟨6604188262994109665294987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70444674805270503096479861 6604188262994109665294987)
                ·
                  refine ⟨9906282394491164497942481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6604188262994109665294987 9906282394491164497942481)
                  ·
                    refine ⟨7429711795868373373456861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9906282394491164497942481 7429711795868373373456861)
                    ·
                      refine ⟨2786141923450640015046323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7429711795868373373456861 2786141923450640015046323)
                      ·
                        rfl

theorem cell23_5425992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_5425992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5425992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5425992 prefixEnd_5425992 := by exact prefixLift 5425992
  have htrace : WordTrace (prefixWord ++ tailWord_5425992) baseStart_5425992 baseEnd_5425992 := by
    simpa [prefixWord, tailWord_5425992, baseEnd_5425992] using wordTrace_append hprefix tailTrace_5425992
  have hstable : (prefixWord ++ tailWord_5425992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5425992).length < 2 ^ (prefixWord ++ tailWord_5425992).sum := by decide
  have hdescent : baseEnd_5425992 < baseStart_5425992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5425992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426012 : List Nat := [2, 2, 4, 2, 1, 2, 2, 8]
def baseStart_5426012 : Nat := 118140960795 + 5426012 * 2 ^ 59
def prefixEnd_5426012 : Nat := 4983230072969 + 3 ^ 40 * 5426012 * 2
def baseEnd_5426012 : Nat := 103190821965323330992453

theorem tailTrace_5426012 : CollatzResearch.WordTrace tailWord_5426012 prefixEnd_5426012 103190821965323330992453 := by
  unfold tailWord_5426012
  simp only [CollatzResearch.WordTrace]
  refine ⟨98951458009246343958612145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131935277345661791944816193 98951458009246343958612145)
  ·
    refine ⟨74213593506934757968959109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98951458009246343958612145 74213593506934757968959109)
    ·
      refine ⟨13915048782550267119179833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74213593506934757968959109 13915048782550267119179833)
      ·
        refine ⟨10436286586912700339384875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13915048782550267119179833 10436286586912700339384875)
        ·
          refine ⟨15654429880369050509077313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10436286586912700339384875 15654429880369050509077313)
          ·
            refine ⟨11740822410276787881807985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15654429880369050509077313 11740822410276787881807985)
            ·
              refine ⟨8805616807707590911355989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11740822410276787881807985 8805616807707590911355989)
              ·
                refine ⟨103190821965323330992453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8805616807707590911355989 103190821965323330992453)
                ·
                  rfl

theorem cell23_5426012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 8].length) (baseStart_5426012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426012 prefixEnd_5426012 := by exact prefixLift 5426012
  have htrace : WordTrace (prefixWord ++ tailWord_5426012) baseStart_5426012 baseEnd_5426012 := by
    simpa [prefixWord, tailWord_5426012, baseEnd_5426012] using wordTrace_append hprefix tailTrace_5426012
  have hstable : (prefixWord ++ tailWord_5426012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426012).length < 2 ^ (prefixWord ++ tailWord_5426012).sum := by decide
  have hdescent : baseEnd_5426012 < baseStart_5426012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426056 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_5426056 : Nat := 118140960795 + 5426056 * 2 ^ 59
def prefixEnd_5426056 : Nat := 4983230072969 + 3 ^ 40 * 5426056 * 2
def baseEnd_5426056 : Nat := 2786174786212527764646029

theorem tailTrace_5426056 : CollatzResearch.WordTrace tailWord_5426056 prefixEnd_5426056 2786174786212527764646029 := by
  unfold tailWord_5426056
  simp only [CollatzResearch.WordTrace]
  refine ⟨98952260415166641715913011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131936347220222188954550681 98952260415166641715913011)
  ·
    refine ⟨148428390622749962573869517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98952260415166641715913011 148428390622749962573869517)
    ·
      refine ⟨55660646483531235965201069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148428390622749962573869517 55660646483531235965201069)
      ·
        refine ⟨20872742431324213486950401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55660646483531235965201069 20872742431324213486950401)
        ·
          refine ⟨15654556823493160115212801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20872742431324213486950401 15654556823493160115212801)
          ·
            refine ⟨11740917617619870086409601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15654556823493160115212801 11740917617619870086409601)
            ·
              refine ⟨8805688213214902564807201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11740917617619870086409601 8805688213214902564807201)
              ·
                refine ⟨6604266159911176923605401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8805688213214902564807201 6604266159911176923605401)
                ·
                  refine ⟨4953199619933382692704051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6604266159911176923605401 4953199619933382692704051)
                  ·
                    refine ⟨7429799429900074039056077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4953199619933382692704051 7429799429900074039056077)
                    ·
                      refine ⟨2786174786212527764646029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7429799429900074039056077 2786174786212527764646029)
                      ·
                        rfl

theorem cell23_5426056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_5426056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426056 prefixEnd_5426056 := by exact prefixLift 5426056
  have htrace : WordTrace (prefixWord ++ tailWord_5426056) baseStart_5426056 baseEnd_5426056 := by
    simpa [prefixWord, tailWord_5426056, baseEnd_5426056] using wordTrace_append hprefix tailTrace_5426056
  have hstable : (prefixWord ++ tailWord_5426056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426056).length < 2 ^ (prefixWord ++ tailWord_5426056).sum := by decide
  have hdescent : baseEnd_5426056 < baseStart_5426056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426079 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5426079 : Nat := 118140960795 + 5426079 * 2 ^ 59
def prefixEnd_5426079 : Nat := 4983230072969 + 3 ^ 40 * 5426079 * 2
def baseEnd_5426079 : Nat := 2786186596267581174658423

theorem tailTrace_5426079 : CollatzResearch.WordTrace tailWord_5426079 prefixEnd_5426079 2786186596267581174658423 := by
  unfold tailWord_5426079
  simp only [CollatzResearch.WordTrace]
  refine ⟨197905359709249958359913291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131936906472833305573275527 197905359709249958359913291)
  ·
    refine ⟨296858039563874937539869937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197905359709249958359913291 296858039563874937539869937)
    ·
      refine ⟨222643529672906203154902453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296858039563874937539869937 222643529672906203154902453)
      ·
        refine ⟨20872830906834956545772105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222643529672906203154902453 20872830906834956545772105)
        ·
          refine ⟨15654623180126217409329079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20872830906834956545772105 15654623180126217409329079)
          ·
            refine ⟨23481934770189326113993619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15654623180126217409329079 23481934770189326113993619)
            ·
              refine ⟨35222902155283989170990429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23481934770189326113993619 35222902155283989170990429)
              ·
                refine ⟨13208588308231495939121411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35222902155283989170990429 13208588308231495939121411)
                ·
                  refine ⟨19812882462347243908682117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13208588308231495939121411 19812882462347243908682117)
                  ·
                    refine ⟨3714915461690108232877897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19812882462347243908682117 3714915461690108232877897)
                    ·
                      refine ⟨2786186596267581174658423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714915461690108232877897 2786186596267581174658423)
                      ·
                        rfl

theorem cell23_5426079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5426079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426079 prefixEnd_5426079 := by exact prefixLift 5426079
  have htrace : WordTrace (prefixWord ++ tailWord_5426079) baseStart_5426079 baseEnd_5426079 := by
    simpa [prefixWord, tailWord_5426079, baseEnd_5426079] using wordTrace_append hprefix tailTrace_5426079
  have hstable : (prefixWord ++ tailWord_5426079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426079).length < 2 ^ (prefixWord ++ tailWord_5426079).sum := by decide
  have hdescent : baseEnd_5426079 < baseStart_5426079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426100 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5426100 : Nat := 118140960795 + 5426100 * 2 ^ 59
def prefixEnd_5426100 : Nat := 4983230072969 + 3 ^ 40 * 5426100 * 2
def baseEnd_5426100 : Nat := 2786197379361325592495827

theorem tailTrace_5426100 : CollatzResearch.WordTrace tailWord_5426100 prefixEnd_5426100 2786197379361325592495827 := by
  unfold tailWord_5426100
  simp only [CollatzResearch.WordTrace]
  refine ⟨98953062821086939473213877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131937417094782585964285169 98953062821086939473213877)
  ·
    refine ⟨9276849639476900575613801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98953062821086939473213877 9276849639476900575613801)
    ·
      refine ⟨6957637229607675431710351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9276849639476900575613801 6957637229607675431710351)
      ·
        refine ⟨10436455844411513147565527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6957637229607675431710351 10436455844411513147565527)
        ·
          refine ⟨15654683766617269721348291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10436455844411513147565527 15654683766617269721348291)
          ·
            refine ⟨23482025649925904582022437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15654683766617269721348291 23482025649925904582022437)
            ·
              refine ⟨4402879809361107109129207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23482025649925904582022437 4402879809361107109129207)
              ·
                refine ⟨6604319714041660663693811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402879809361107109129207 6604319714041660663693811)
                ·
                  refine ⟨9906479571062490995540717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6604319714041660663693811 9906479571062490995540717)
                  ·
                    refine ⟨3714929839148434123327769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9906479571062490995540717 3714929839148434123327769)
                    ·
                      refine ⟨2786197379361325592495827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714929839148434123327769 2786197379361325592495827)
                      ·
                        rfl

theorem cell23_5426100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5426100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426100 prefixEnd_5426100 := by exact prefixLift 5426100
  have htrace : WordTrace (prefixWord ++ tailWord_5426100) baseStart_5426100 baseEnd_5426100 := by
    simpa [prefixWord, tailWord_5426100, baseEnd_5426100] using wordTrace_append hprefix tailTrace_5426100
  have hstable : (prefixWord ++ tailWord_5426100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426100).length < 2 ^ (prefixWord ++ tailWord_5426100).sum := by decide
  have hdescent : baseEnd_5426100 < baseStart_5426100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426112 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_5426112 : Nat := 118140960795 + 5426112 * 2 ^ 59
def prefixEnd_5426112 : Nat := 4983230072969 + 3 ^ 40 * 5426112 * 2
def baseEnd_5426112 : Nat := 2786203541129179545545771

theorem tailTrace_5426112 : CollatzResearch.WordTrace tailWord_5426112 prefixEnd_5426112 2786203541129179545545771 := by
  unfold tailWord_5426112
  simp only [CollatzResearch.WordTrace]
  refine ⟨98953281659065202497932295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131937708878753603330576393 98953281659065202497932295)
  ·
    refine ⟨148429922488597803746898443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98953281659065202497932295 148429922488597803746898443)
    ·
      refine ⟨222644883732896705620347665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148429922488597803746898443 222644883732896705620347665)
      ·
        refine ⟨166983662799672529215260749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222644883732896705620347665 166983662799672529215260749)
        ·
          refine ⟨62618873549877198455722781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166983662799672529215260749 62618873549877198455722781)
          ·
            refine ⟨23482077581203949420896043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62618873549877198455722781 23482077581203949420896043)
            ·
              refine ⟨35223116371805924131344065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23482077581203949420896043 35223116371805924131344065)
              ·
                refine ⟨26417337278854443098508049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35223116371805924131344065 26417337278854443098508049)
                ·
                  refine ⟨19813002959140832323881037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26417337278854443098508049 19813002959140832323881037)
                  ·
                    refine ⟨7429876109677812121455389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19813002959140832323881037 7429876109677812121455389)
                    ·
                      refine ⟨2786203541129179545545771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7429876109677812121455389 2786203541129179545545771)
                      ·
                        rfl

theorem cell23_5426112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_5426112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426112 prefixEnd_5426112 := by exact prefixLift 5426112
  have htrace : WordTrace (prefixWord ++ tailWord_5426112) baseStart_5426112 baseEnd_5426112 := by
    simpa [prefixWord, tailWord_5426112, baseEnd_5426112] using wordTrace_append hprefix tailTrace_5426112
  have hstable : (prefixWord ++ tailWord_5426112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426112).length < 2 ^ (prefixWord ++ tailWord_5426112).sum := by decide
  have hdescent : baseEnd_5426112 < baseStart_5426112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426130 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5426130 : Nat := 118140960795 + 5426130 * 2 ^ 59
def prefixEnd_5426130 : Nat := 4983230072969 + 3 ^ 40 * 5426130 * 2
def baseEnd_5426130 : Nat := 2786212783780960475120689

theorem tailTrace_5426130 : CollatzResearch.WordTrace tailWord_5426130 prefixEnd_5426130 2786212783780960475120689 := by
  unfold tailWord_5426130
  simp only [CollatzResearch.WordTrace]
  refine ⟨49476804958016298517504961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131938146554710129380013229 49476804958016298517504961)
  ·
    refine ⟨37107603718512223888128721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49476804958016298517504961 37107603718512223888128721)
    ·
      refine ⟨27830702788884167916096541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37107603718512223888128721 27830702788884167916096541)
      ·
        refine ⟨10436513545831562968536203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27830702788884167916096541 10436513545831562968536203)
        ·
          refine ⟨15654770318747344452804305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10436513545831562968536203 15654770318747344452804305)
          ·
            refine ⟨11741077739060508339603229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15654770318747344452804305 11741077739060508339603229)
            ·
              refine ⟨4402904152147690627351211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11741077739060508339603229 4402904152147690627351211)
              ·
                refine ⟨6604356228221535941026817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402904152147690627351211 6604356228221535941026817)
                ·
                  refine ⟨4953267171166151955770113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6604356228221535941026817 4953267171166151955770113)
                  ·
                    refine ⟨3714950378374613966827585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4953267171166151955770113 3714950378374613966827585)
                    ·
                      refine ⟨2786212783780960475120689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3714950378374613966827585 2786212783780960475120689)
                      ·
                        rfl

theorem cell23_5426130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5426130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426130 prefixEnd_5426130 := by exact prefixLift 5426130
  have htrace : WordTrace (prefixWord ++ tailWord_5426130) baseStart_5426130 baseEnd_5426130 := by
    simpa [prefixWord, tailWord_5426130, baseEnd_5426130] using wordTrace_append hprefix tailTrace_5426130
  have hstable : (prefixWord ++ tailWord_5426130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426130).length < 2 ^ (prefixWord ++ tailWord_5426130).sum := by decide
  have hdescent : baseEnd_5426130 < baseStart_5426130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426132 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_5426132 : Nat := 118140960795 + 5426132 * 2 ^ 59
def prefixEnd_5426132 : Nat := 4983230072969 + 3 ^ 40 * 5426132 * 2
def baseEnd_5426132 : Nat := 928737936914089822431893

theorem tailTrace_5426132 : CollatzResearch.WordTrace tailWord_5426132 prefixEnd_5426132 928737936914089822431893 := by
  unfold tailWord_5426132
  simp only [CollatzResearch.WordTrace]
  refine ⟨98953646389028974205796325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131938195185371965607728433 98953646389028974205796325)
  ·
    refine ⟨18553808697942932663586811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98953646389028974205796325 18553808697942932663586811)
    ·
      refine ⟨27830713046914398995380217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18553808697942932663586811 27830713046914398995380217)
      ·
        refine ⟨20873034785185799246535163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27830713046914398995380217 20873034785185799246535163)
        ·
          refine ⟨31309552177778698869802745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20873034785185799246535163 31309552177778698869802745)
          ·
            refine ⟨23482164133334024152352059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31309552177778698869802745 23482164133334024152352059)
            ·
              refine ⟨35223246200001036228528089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23482164133334024152352059 35223246200001036228528089)
              ·
                refine ⟨26417434650000777171396067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35223246200001036228528089 26417434650000777171396067)
                ·
                  refine ⟨39626151975001165757094101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26417434650000777171396067 39626151975001165757094101)
                  ·
                    refine ⟨928737936914089822431893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39626151975001165757094101 928737936914089822431893)
                    ·
                      rfl

theorem cell23_5426132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_5426132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426132 prefixEnd_5426132 := by exact prefixLift 5426132
  have htrace : WordTrace (prefixWord ++ tailWord_5426132) baseStart_5426132 baseEnd_5426132 := by
    simpa [prefixWord, tailWord_5426132, baseEnd_5426132] using wordTrace_append hprefix tailTrace_5426132
  have hstable : (prefixWord ++ tailWord_5426132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426132).length < 2 ^ (prefixWord ++ tailWord_5426132).sum := by decide
  have hdescent : baseEnd_5426132 < baseStart_5426132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426145 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_5426145 : Nat := 118140960795 + 5426145 * 2 ^ 59
def prefixEnd_5426145 : Nat := 4983230072969 + 3 ^ 40 * 5426145 * 2
def baseEnd_5426145 : Nat := 928740161996925972144373

theorem tailTrace_5426145 : CollatzResearch.WordTrace tailWord_5426145 prefixEnd_5426145 928740161996925972144373 := by
  unfold tailWord_5426145
  simp only [CollatzResearch.WordTrace]
  refine ⟨197907766927010851631815889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131938511284673901087877259 197907766927010851631815889)
  ·
    refine ⟨148430825195258138723861917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197907766927010851631815889 148430825195258138723861917)
    ·
      refine ⟨55661559448221802021448219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148430825195258138723861917 55661559448221802021448219)
      ·
        refine ⟨83492339172332703032172329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55661559448221802021448219 83492339172332703032172329)
        ·
          refine ⟨62619254379249527274129247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83492339172332703032172329 62619254379249527274129247)
          ·
            refine ⟨93928881568874290911193871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62619254379249527274129247 93928881568874290911193871)
            ·
              refine ⟨140893322353311436366790807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93928881568874290911193871 140893322353311436366790807)
              ·
                refine ⟨211339983529967154550186211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140893322353311436366790807 211339983529967154550186211)
                ·
                  refine ⟨317009975294950731825279317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211339983529967154550186211 317009975294950731825279317)
                  ·
                    refine ⟨928740161996925972144373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 317009975294950731825279317 928740161996925972144373)
                    ·
                      rfl

theorem cell23_5426145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_5426145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426145 prefixEnd_5426145 := by exact prefixLift 5426145
  have htrace : WordTrace (prefixWord ++ tailWord_5426145) baseStart_5426145 baseEnd_5426145 := by
    simpa [prefixWord, tailWord_5426145, baseEnd_5426145] using wordTrace_append hprefix tailTrace_5426145
  have hstable : (prefixWord ++ tailWord_5426145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426145).length < 2 ^ (prefixWord ++ tailWord_5426145).sum := by decide
  have hdescent : baseEnd_5426145 < baseStart_5426145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426152 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_5426152 : Nat := 118140960795 + 5426152 * 2 ^ 59
def prefixEnd_5426152 : Nat := 4983230072969 + 3 ^ 40 * 5426152 * 2
def baseEnd_5426152 : Nat := 2786224080355359389045587

theorem tailTrace_5426152 : CollatzResearch.WordTrace tailWord_5426152 prefixEnd_5426152 2786224080355359389045587 := by
  unfold tailWord_5426152
  simp only [CollatzResearch.WordTrace]
  refine ⟨98954011118992745913660355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131938681491990327884880473 98954011118992745913660355)
  ·
    refine ⟨148431016678489118870490533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98954011118992745913660355 148431016678489118870490533)
    ·
      refine ⟨27830815627216709788216975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148431016678489118870490533 27830815627216709788216975)
      ·
        refine ⟨41746223440825064682325463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27830815627216709788216975 41746223440825064682325463)
        ·
          refine ⟨62619335161237597023488195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41746223440825064682325463 62619335161237597023488195)
          ·
            refine ⟨93929002741856395535232293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62619335161237597023488195 93929002741856395535232293)
            ·
              refine ⟨17611688014098074162856055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93929002741856395535232293 17611688014098074162856055)
              ·
                refine ⟨26417532021147111244284083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17611688014098074162856055 26417532021147111244284083)
                ·
                  refine ⟨39626298031720666866426125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26417532021147111244284083 39626298031720666866426125)
                  ·
                    refine ⟨14859861761895250074909797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39626298031720666866426125 14859861761895250074909797)
                    ·
                      refine ⟨2786224080355359389045587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14859861761895250074909797 2786224080355359389045587)
                      ·
                        rfl

theorem cell23_5426152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_5426152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426152 prefixEnd_5426152 := by exact prefixLift 5426152
  have htrace : WordTrace (prefixWord ++ tailWord_5426152) baseStart_5426152 baseEnd_5426152 := by
    simpa [prefixWord, tailWord_5426152, baseEnd_5426152] using wordTrace_append hprefix tailTrace_5426152
  have hstable : (prefixWord ++ tailWord_5426152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426152).length < 2 ^ (prefixWord ++ tailWord_5426152).sum := by decide
  have hdescent : baseEnd_5426152 < baseStart_5426152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426155 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_5426155 : Nat := 118140960795 + 5426155 * 2 ^ 59
def prefixEnd_5426155 : Nat := 4983230072969 + 3 ^ 40 * 5426155 * 2
def baseEnd_5426155 : Nat := 2786225620797322877308073

theorem tailTrace_5426155 : CollatzResearch.WordTrace tailWord_5426155 prefixEnd_5426155 2786225620797322877308073 := by
  unfold tailWord_5426155
  simp only [CollatzResearch.WordTrace]
  refine ⟨197908131656974623339679919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131938754437983082226453279 197908131656974623339679919)
  ·
    refine ⟨296862197485461935009519879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197908131656974623339679919 296862197485461935009519879)
    ·
      refine ⟨445293296228192902514279819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296862197485461935009519879 445293296228192902514279819)
      ·
        refine ⟨667939944342289353771419729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445293296228192902514279819 667939944342289353771419729)
        ·
          refine ⟨500954958256717015328564797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667939944342289353771419729 500954958256717015328564797)
          ·
            refine ⟨187858109346268880748211799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500954958256717015328564797 187858109346268880748211799)
            ·
              refine ⟨281787164019403321122317699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187858109346268880748211799 281787164019403321122317699)
              ·
                refine ⟨422680746029104981683476549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281787164019403321122317699 422680746029104981683476549)
                ·
                  refine ⟨79252639880457184065651853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422680746029104981683476549 79252639880457184065651853)
                  ·
                    refine ⟨29719739955171444024619445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79252639880457184065651853 29719739955171444024619445)
                    ·
                      refine ⟨2786225620797322877308073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29719739955171444024619445 2786225620797322877308073)
                      ·
                        rfl

theorem cell23_5426155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_5426155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426155 prefixEnd_5426155 := by exact prefixLift 5426155
  have htrace : WordTrace (prefixWord ++ tailWord_5426155) baseStart_5426155 baseEnd_5426155 := by
    simpa [prefixWord, tailWord_5426155, baseEnd_5426155] using wordTrace_append hprefix tailTrace_5426155
  have hstable : (prefixWord ++ tailWord_5426155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426155).length < 2 ^ (prefixWord ++ tailWord_5426155).sum := by decide
  have hdescent : baseEnd_5426155 < baseStart_5426155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426229 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_5426229 : Nat := 118140960795 + 5426229 * 2 ^ 59
def prefixEnd_5426229 : Nat := 4983230072969 + 3 ^ 40 * 5426229 * 2
def baseEnd_5426229 : Nat := 2786263618365755587782733

theorem tailTrace_5426229 : CollatzResearch.WordTrace tailWord_5426229 prefixEnd_5426229 2786263618365755587782733 := by
  unfold tailWord_5426229
  simp only [CollatzResearch.WordTrace]
  refine ⟨197910830658706533977873741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131940553772471022651915827 197910830658706533977873741)
  ·
    refine ⟨74216561497014950241702653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197910830658706533977873741 74216561497014950241702653)
    ·
      refine ⟨27831210561380606340638495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74216561497014950241702653 27831210561380606340638495)
      ·
        refine ⟨41746815842070909510957743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27831210561380606340638495 41746815842070909510957743)
        ·
          refine ⟨62620223763106364266436615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41746815842070909510957743 62620223763106364266436615)
          ·
            refine ⟨93930335644659546399654923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62620223763106364266436615 93930335644659546399654923)
            ·
              refine ⟨140895503466989319599482385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93930335644659546399654923 140895503466989319599482385)
              ·
                refine ⟨105671627600241989699611789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140895503466989319599482385 105671627600241989699611789)
                ·
                  refine ⟨39626860350090746137354421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105671627600241989699611789 39626860350090746137354421)
                  ·
                    refine ⟨3715018157821007450376977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39626860350090746137354421 3715018157821007450376977)
                    ·
                      refine ⟨2786263618365755587782733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715018157821007450376977 2786263618365755587782733)
                      ·
                        rfl

theorem cell23_5426229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_5426229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426229 prefixEnd_5426229 := by exact prefixLift 5426229
  have htrace : WordTrace (prefixWord ++ tailWord_5426229) baseStart_5426229 baseEnd_5426229 := by
    simpa [prefixWord, tailWord_5426229, baseEnd_5426229] using wordTrace_append hprefix tailTrace_5426229
  have hstable : (prefixWord ++ tailWord_5426229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426229).length < 2 ^ (prefixWord ++ tailWord_5426229).sum := by decide
  have hdescent : baseEnd_5426229 < baseStart_5426229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426230 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5426230 : Nat := 118140960795 + 5426230 * 2 ^ 59
def prefixEnd_5426230 : Nat := 4983230072969 + 3 ^ 40 * 5426230 * 2
def baseEnd_5426230 : Nat := 928754710615470027956743

theorem tailTrace_5426230 : CollatzResearch.WordTrace tailWord_5426230 prefixEnd_5426230 928754710615470027956743 := by
  unfold tailWord_5426230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369429195731431946791259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131940578087801940765773429 12369429195731431946791259)
  ·
    refine ⟨18554143793597147920186889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12369429195731431946791259 18554143793597147920186889)
    ·
      refine ⟨13915607845197860940140167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18554143793597147920186889 13915607845197860940140167)
      ·
        refine ⟨20873411767796791410210251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13915607845197860940140167 20873411767796791410210251)
        ·
          refine ⟨31310117651695187115315377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20873411767796791410210251 31310117651695187115315377)
          ·
            refine ⟨23482588238771390336486533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31310117651695187115315377 23482588238771390336486533)
            ·
              refine ⟨4402985294769635688091225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23482588238771390336486533 4402985294769635688091225)
              ·
                refine ⟨3302238971077226766068419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4402985294769635688091225 3302238971077226766068419)
                ·
                  refine ⟨4953358456615840149102629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302238971077226766068419 4953358456615840149102629)
                  ·
                    refine ⟨928754710615470027956743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953358456615840149102629 928754710615470027956743)
                    ·
                      rfl

theorem cell23_5426230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5426230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426230 prefixEnd_5426230 := by exact prefixLift 5426230
  have htrace : WordTrace (prefixWord ++ tailWord_5426230) baseStart_5426230 baseEnd_5426230 := by
    simpa [prefixWord, tailWord_5426230, baseEnd_5426230] using wordTrace_append hprefix tailTrace_5426230
  have hstable : (prefixWord ++ tailWord_5426230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426230).length < 2 ^ (prefixWord ++ tailWord_5426230).sum := by decide
  have hdescent : baseEnd_5426230 < baseStart_5426230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426253 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5426253 : Nat := 118140960795 + 5426253 * 2 ^ 59
def prefixEnd_5426253 : Nat := 4983230072969 + 3 ^ 40 * 5426253 * 2
def baseEnd_5426253 : Nat := 2786275941901463493882623

theorem tailTrace_5426253 : CollatzResearch.WordTrace tailWord_5426253 prefixEnd_5426253 2786275941901463493882623 := by
  unfold tailWord_5426253
  simp only [CollatzResearch.WordTrace]
  refine ⟨197911706010619586076747413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131941137340413057384498275 197911706010619586076747413)
  ·
    refine ⟨9277111219247793097347535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197911706010619586076747413 9277111219247793097347535)
    ·
      refine ⟨13915666828871689646021303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9277111219247793097347535 13915666828871689646021303)
      ·
        refine ⟨20873500243307534469031955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13915666828871689646021303 20873500243307534469031955)
        ·
          refine ⟨31310250364961301703547933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20873500243307534469031955 31310250364961301703547933)
          ·
            refine ⟨11741343886860488138830475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31310250364961301703547933 11741343886860488138830475)
            ·
              refine ⟨17612015830290732208245713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11741343886860488138830475 17612015830290732208245713)
              ·
                refine ⟨13209011872718049156184285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17612015830290732208245713 13209011872718049156184285)
                ·
                  refine ⟨4953379452269268433569107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13209011872718049156184285 4953379452269268433569107)
                  ·
                    refine ⟨7430069178403902650353661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4953379452269268433569107 7430069178403902650353661)
                    ·
                      refine ⟨2786275941901463493882623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7430069178403902650353661 2786275941901463493882623)
                      ·
                        rfl

theorem cell23_5426253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5426253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426253 prefixEnd_5426253 := by exact prefixLift 5426253
  have htrace : WordTrace (prefixWord ++ tailWord_5426253) baseStart_5426253 baseEnd_5426253 := by
    simpa [prefixWord, tailWord_5426253, baseEnd_5426253] using wordTrace_append hprefix tailTrace_5426253
  have hstable : (prefixWord ++ tailWord_5426253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426253).length < 2 ^ (prefixWord ++ tailWord_5426253).sum := by decide
  have hdescent : baseEnd_5426253 < baseStart_5426253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426276 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_5426276 : Nat := 118140960795 + 5426276 * 2 ^ 59
def prefixEnd_5426276 : Nat := 4983230072969 + 3 ^ 40 * 5426276 * 2
def baseEnd_5426276 : Nat := 2786287751956516903895017

theorem tailTrace_5426276 : CollatzResearch.WordTrace tailWord_5426276 prefixEnd_5426276 2786287751956516903895017 := by
  unfold tailWord_5426276
  simp only [CollatzResearch.WordTrace]
  refine ⟨98956272444768130502417341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131941696593024174003223121 98956272444768130502417341)
  ·
    refine ⟨37108602166788048938406503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98956272444768130502417341 37108602166788048938406503)
    ·
      refine ⟨55662903250182073407609755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37108602166788048938406503 55662903250182073407609755)
      ·
        refine ⟨83494354875273110111414633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55662903250182073407609755 83494354875273110111414633)
        ·
          refine ⟨62620766156454832583560975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83494354875273110111414633 62620766156454832583560975)
          ·
            refine ⟨93931149234682248875341463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62620766156454832583560975 93931149234682248875341463)
            ·
              refine ⟨140896723852023373313012195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93931149234682248875341463 140896723852023373313012195)
              ·
                refine ⟨211345085778035059969518293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140896723852023373313012195 211345085778035059969518293)
                ·
                  refine ⟨4953400447922696718035585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 211345085778035059969518293 4953400447922696718035585)
                  ·
                    refine ⟨3715050335942022538526689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4953400447922696718035585 3715050335942022538526689)
                    ·
                      refine ⟨2786287751956516903895017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715050335942022538526689 2786287751956516903895017)
                      ·
                        rfl

theorem cell23_5426276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_5426276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426276 prefixEnd_5426276 := by exact prefixLift 5426276
  have htrace : WordTrace (prefixWord ++ tailWord_5426276) baseStart_5426276 baseEnd_5426276 := by
    simpa [prefixWord, tailWord_5426276, baseEnd_5426276] using wordTrace_append hprefix tailTrace_5426276
  have hstable : (prefixWord ++ tailWord_5426276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426276).length < 2 ^ (prefixWord ++ tailWord_5426276).sum := by decide
  have hdescent : baseEnd_5426276 < baseStart_5426276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426286 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_5426286 : Nat := 118140960795 + 5426286 * 2 ^ 59
def prefixEnd_5426286 : Nat := 4983230072969 + 3 ^ 40 * 5426286 * 2
def baseEnd_5426286 : Nat := 928764295587687288256657

theorem tailTrace_5426286 : CollatzResearch.WordTrace tailWord_5426286 prefixEnd_5426286 928764295587687288256657 := by
  unfold tailWord_5426286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739113702437504089087339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131941939746333355141799141 24739113702437504089087339)
  ·
    refine ⟨37108670553656256133631009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24739113702437504089087339 37108670553656256133631009)
    ·
      refine ⟨27831502915242192100223257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37108670553656256133631009 27831502915242192100223257)
      ·
        refine ⟨20873627186431644075167443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27831502915242192100223257 20873627186431644075167443)
        ·
          refine ⟨31310440779647466112751165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20873627186431644075167443 31310440779647466112751165)
          ·
            refine ⟨11741415292367799792281687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31310440779647466112751165 11741415292367799792281687)
            ·
              refine ⟨17612122938551699688422531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11741415292367799792281687 17612122938551699688422531)
              ·
                refine ⟨26418184407827549532633797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17612122938551699688422531 26418184407827549532633797)
                ·
                  refine ⟨4953409576467665537368837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26418184407827549532633797 4953409576467665537368837)
                  ·
                    refine ⟨928764295587687288256657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953409576467665537368837 928764295587687288256657)
                    ·
                      rfl

theorem cell23_5426286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_5426286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426286 prefixEnd_5426286 := by exact prefixLift 5426286
  have htrace : WordTrace (prefixWord ++ tailWord_5426286) baseStart_5426286 baseEnd_5426286 := by
    simpa [prefixWord, tailWord_5426286, baseEnd_5426286] using wordTrace_append hprefix tailTrace_5426286
  have hstable : (prefixWord ++ tailWord_5426286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426286).length < 2 ^ (prefixWord ++ tailWord_5426286).sum := by decide
  have hdescent : baseEnd_5426286 < baseStart_5426286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426327 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 1, 2, 2]
def baseStart_5426327 : Nat := 118140960795 + 5426327 * 2 ^ 59
def prefixEnd_5426327 : Nat := 4983230072969 + 3 ^ 40 * 5426327 * 2
def baseEnd_5426327 : Nat := 2786313939469896204357283

theorem tailTrace_5426327 : CollatzResearch.WordTrace tailWord_5426327 prefixEnd_5426327 2786313939469896204357283 := by
  unfold tailWord_5426327
  simp only [CollatzResearch.WordTrace]
  refine ⟨197914405012351496714941235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131942936674900997809960823 197914405012351496714941235)
  ·
    refine ⟨296871607518527245072411853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197914405012351496714941235 296871607518527245072411853)
    ·
      refine ⟨111326852819447716902154445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296871607518527245072411853 111326852819447716902154445)
      ·
        refine ⟨41747569807292893838307917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111326852819447716902154445 41747569807292893838307917)
        ·
          refine ⟨15655338677734835189365469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41747569807292893838307917 15655338677734835189365469)
          ·
            refine ⟨5870752004150563196012051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15655338677734835189365469 5870752004150563196012051)
            ·
              refine ⟨8806128006225844794018077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870752004150563196012051 8806128006225844794018077)
              ·
                refine ⟨3302298002334691797756779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8806128006225844794018077 3302298002334691797756779)
                ·
                  refine ⟨4953447003502037696635169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302298002334691797756779 4953447003502037696635169)
                  ·
                    refine ⟨3715085252626528272476377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4953447003502037696635169 3715085252626528272476377)
                    ·
                      refine ⟨2786313939469896204357283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715085252626528272476377 2786313939469896204357283)
                      ·
                        rfl

theorem cell23_5426327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_5426327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426327 prefixEnd_5426327 := by exact prefixLift 5426327
  have htrace : WordTrace (prefixWord ++ tailWord_5426327) baseStart_5426327 baseEnd_5426327 := by
    simpa [prefixWord, tailWord_5426327, baseEnd_5426327] using wordTrace_append hprefix tailTrace_5426327
  have hstable : (prefixWord ++ tailWord_5426327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426327).length < 2 ^ (prefixWord ++ tailWord_5426327).sum := by decide
  have hdescent : baseEnd_5426327 < baseStart_5426327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426343 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5426343 : Nat := 118140960795 + 5426343 * 2 ^ 59
def prefixEnd_5426343 : Nat := 4983230072969 + 3 ^ 40 * 5426343 * 2
def baseEnd_5426343 : Nat := 2786322155160368141757209

theorem tailTrace_5426343 : CollatzResearch.WordTrace tailWord_5426343 prefixEnd_5426343 2786322155160368141757209 := by
  unfold tailWord_5426343
  simp only [CollatzResearch.WordTrace]
  refine ⟨197914988580293531447523683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131943325720195687631682455 197914988580293531447523683)
  ·
    refine ⟨296872482870440297171285525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197914988580293531447523683 296872482870440297171285525)
    ·
      refine ⟨13915897634551888929904009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 296872482870440297171285525 13915897634551888929904009)
      ·
        refine ⟨10436923225913916697428007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13915897634551888929904009 10436923225913916697428007)
        ·
          refine ⟨15655384838870875046142011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10436923225913916697428007 15655384838870875046142011)
          ·
            refine ⟨23483077258306312569213017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15655384838870875046142011 23483077258306312569213017)
            ·
              refine ⟨17612307943729734426909763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23483077258306312569213017 17612307943729734426909763)
              ·
                refine ⟨26418461915594601640364645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17612307943729734426909763 26418461915594601640364645)
                ·
                  refine ⟨4953461609173987807568371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26418461915594601640364645 4953461609173987807568371)
                  ·
                    refine ⟨7430192413760981711352557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4953461609173987807568371 7430192413760981711352557)
                    ·
                      refine ⟨2786322155160368141757209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7430192413760981711352557 2786322155160368141757209)
                      ·
                        rfl

theorem cell23_5426343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5426343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426343 prefixEnd_5426343 := by exact prefixLift 5426343
  have htrace : WordTrace (prefixWord ++ tailWord_5426343) baseStart_5426343 baseEnd_5426343 := by
    simpa [prefixWord, tailWord_5426343, baseEnd_5426343] using wordTrace_append hprefix tailTrace_5426343
  have hstable : (prefixWord ++ tailWord_5426343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426343).length < 2 ^ (prefixWord ++ tailWord_5426343).sum := by decide
  have hdescent : baseEnd_5426343 < baseStart_5426343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426400 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 2, 2, 2]
def baseStart_5426400 : Nat := 118140960795 + 5426400 * 2 ^ 59
def prefixEnd_5426400 : Nat := 4983230072969 + 3 ^ 40 * 5426400 * 2
def baseEnd_5426400 : Nat := 2786351423557674418744447

theorem tailTrace_5426400 : CollatzResearch.WordTrace tailWord_5426400 prefixEnd_5426400 2786351423557674418744447 := by
  unfold tailWord_5426400
  simp only [CollatzResearch.WordTrace]
  refine ⟨98958533770543515091174327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131944711694058020121565769 98958533770543515091174327)
  ·
    refine ⟨148437800655815272636761491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98958533770543515091174327 148437800655815272636761491)
    ·
      refine ⟨222656700983722908955142237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148437800655815272636761491 222656700983722908955142237)
      ·
        refine ⟨83496262868896090858178339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222656700983722908955142237 83496262868896090858178339)
        ·
          refine ⟨125244394303344136287267509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83496262868896090858178339 125244394303344136287267509)
          ·
            refine ⟨11741661965938512776931329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125244394303344136287267509 11741661965938512776931329)
            ·
              refine ⟨8806246474453884582698497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11741661965938512776931329 8806246474453884582698497)
              ·
                refine ⟨6604684855840413437023873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806246474453884582698497 6604684855840413437023873)
                ·
                  refine ⟨4953513641880310077767905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6604684855840413437023873 4953513641880310077767905)
                  ·
                    refine ⟨3715135231410232558325929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4953513641880310077767905 3715135231410232558325929)
                    ·
                      refine ⟨2786351423557674418744447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715135231410232558325929 2786351423557674418744447)
                      ·
                        rfl

theorem cell23_5426400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_5426400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426400 prefixEnd_5426400 := by exact prefixLift 5426400
  have htrace : WordTrace (prefixWord ++ tailWord_5426400) baseStart_5426400 baseEnd_5426400 := by
    simpa [prefixWord, tailWord_5426400, baseEnd_5426400] using wordTrace_append hprefix tailTrace_5426400
  have hstable : (prefixWord ++ tailWord_5426400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426400).length < 2 ^ (prefixWord ++ tailWord_5426400).sum := by decide
  have hdescent : baseEnd_5426400 < baseStart_5426400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426426 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2]
def baseStart_5426426 : Nat := 118140960795 + 5426426 * 2 ^ 59
def prefixEnd_5426426 : Nat := 4983230072969 + 3 ^ 40 * 5426426 * 2
def baseEnd_5426426 : Nat := 2786364774054691317019327

theorem tailTrace_5426426 : CollatzResearch.WordTrace tailWord_5426426 prefixEnd_5426426 2786364774054691317019327 := by
  unfold tailWord_5426426
  simp only [CollatzResearch.WordTrace]
  refine ⟨49479503959748209155698783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131945343892661891081863421 49479503959748209155698783)
  ·
    refine ⟨74219255939622313733548175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49479503959748209155698783 74219255939622313733548175)
    ·
      refine ⟨111328883909433470600322263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74219255939622313733548175 111328883909433470600322263)
      ·
        refine ⟨166993325864150205900483395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111328883909433470600322263 166993325864150205900483395)
        ·
          refine ⟨250489988796225308850725093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166993325864150205900483395 250489988796225308850725093)
          ·
            refine ⟨46966872899292245409510955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250489988796225308850725093 46966872899292245409510955)
            ·
              refine ⟨70450309348938368114266433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46966872899292245409510955 70450309348938368114266433)
              ·
                refine ⟨52837732011703776085699825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70450309348938368114266433 52837732011703776085699825)
                ·
                  refine ⟨39628299008777832064274869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52837732011703776085699825 39628299008777832064274869)
                  ·
                    refine ⟨3715153032072921756025769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39628299008777832064274869 3715153032072921756025769)
                    ·
                      refine ⟨2786364774054691317019327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715153032072921756025769 2786364774054691317019327)
                      ·
                        rfl

theorem cell23_5426426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_5426426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426426 prefixEnd_5426426 := by exact prefixLift 5426426
  have htrace : WordTrace (prefixWord ++ tailWord_5426426) baseStart_5426426 baseEnd_5426426 := by
    simpa [prefixWord, tailWord_5426426, baseEnd_5426426] using wordTrace_append hprefix tailTrace_5426426
  have hstable : (prefixWord ++ tailWord_5426426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426426).length < 2 ^ (prefixWord ++ tailWord_5426426).sum := by decide
  have hdescent : baseEnd_5426426 < baseStart_5426426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426436 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_5426436 : Nat := 118140960795 + 5426436 * 2 ^ 59
def prefixEnd_5426436 : Nat := 4983230072969 + 3 ^ 40 * 5426436 * 2
def baseEnd_5426436 : Nat := 928789969620412092631427

theorem tailTrace_5426436 : CollatzResearch.WordTrace tailWord_5426436 prefixEnd_5426436 928789969620412092631427 := by
  unfold tailWord_5426436
  simp only [CollatzResearch.WordTrace]
  refine ⟨98959190284478304165329581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131945587045971072220439441 98959190284478304165329581)
  ·
    refine ⟨37109696356679364061998593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98959190284478304165329581 37109696356679364061998593)
    ·
      refine ⟨27832272267509523046498945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37109696356679364061998593 27832272267509523046498945)
      ·
        refine ⟨20874204200632142284874209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27832272267509523046498945 20874204200632142284874209)
        ·
          refine ⟨15655653150474106713655657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20874204200632142284874209 15655653150474106713655657)
          ·
            refine ⟨11741739862855580035241743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15655653150474106713655657 11741739862855580035241743)
            ·
              refine ⟨17612609794283370052862615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11741739862855580035241743 17612609794283370052862615)
              ·
                refine ⟨26418914691425055079293923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17612609794283370052862615 26418914691425055079293923)
                ·
                  refine ⟨39628372037137582618940885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26418914691425055079293923 39628372037137582618940885)
                  ·
                    refine ⟨928789969620412092631427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39628372037137582618940885 928789969620412092631427)
                    ·
                      rfl

theorem cell23_5426436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_5426436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426436 prefixEnd_5426436 := by exact prefixLift 5426436
  have htrace : WordTrace (prefixWord ++ tailWord_5426436) baseStart_5426436 baseEnd_5426436 := by
    simpa [prefixWord, tailWord_5426436, baseEnd_5426436] using wordTrace_append hprefix tailTrace_5426436
  have hstable : (prefixWord ++ tailWord_5426436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426436).length < 2 ^ (prefixWord ++ tailWord_5426436).sum := by decide
  have hdescent : baseEnd_5426436 < baseStart_5426436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426517 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_5426517 : Nat := 118140960795 + 5426517 * 2 ^ 59
def prefixEnd_5426517 : Nat := 4983230072969 + 3 ^ 40 * 5426517 * 2
def baseEnd_5426517 : Nat := 928803833598083486993803

theorem tailTrace_5426517 : CollatzResearch.WordTrace tailWord_5426517 prefixEnd_5426517 928803833598083486993803 := by
  unfold tailWord_5426517
  simp only [CollatzResearch.WordTrace]
  refine ⟨197921334881663159164357805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131947556587775439442905203 197921334881663159164357805)
  ·
    refine ⟨74220500580623684686634177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197921334881663159164357805 74220500580623684686634177)
    ·
      refine ⟨55665375435467763514975633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74220500580623684686634177 55665375435467763514975633)
      ·
        refine ⟨41749031576600822636231725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55665375435467763514975633 41749031576600822636231725)
        ·
          refine ⟨15655886841225308488586897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41749031576600822636231725 15655886841225308488586897)
          ·
            refine ⟨11741915130918981366440173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15655886841225308488586897 11741915130918981366440173)
            ·
              refine ⟨4403218174094618012415065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11741915130918981366440173 4403218174094618012415065)
              ·
                refine ⟨3302413630570963509311299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4403218174094618012415065 3302413630570963509311299)
                ·
                  refine ⟨4953620445856445263966949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302413630570963509311299 4953620445856445263966949)
                  ·
                    refine ⟨928803833598083486993803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953620445856445263966949 928803833598083486993803)
                    ·
                      rfl

theorem cell23_5426517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_5426517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426517 prefixEnd_5426517 := by exact prefixLift 5426517
  have htrace : WordTrace (prefixWord ++ tailWord_5426517) baseStart_5426517 baseEnd_5426517 := by
    simpa [prefixWord, tailWord_5426517, baseEnd_5426517] using wordTrace_append hprefix tailTrace_5426517
  have hstable : (prefixWord ++ tailWord_5426517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426517).length < 2 ^ (prefixWord ++ tailWord_5426517).sum := by decide
  have hdescent : baseEnd_5426517 < baseStart_5426517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426533 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 4, 3, 2]
def baseStart_5426533 : Nat := 118140960795 + 5426533 * 2 ^ 59
def prefixEnd_5426533 : Nat := 4983230072969 + 3 ^ 40 * 5426533 * 2
def baseEnd_5426533 : Nat := 2786419716484722398381335

theorem tailTrace_5426533 : CollatzResearch.WordTrace tailWord_5426533 prefixEnd_5426533 2786419716484722398381335 := by
  unfold tailWord_5426533
  simp only [CollatzResearch.WordTrace]
  refine ⟨197921918449605193896940253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131947945633070129264626835 197921918449605193896940253)
  ·
    refine ⟨74220719418601947711352595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197921918449605193896940253 74220719418601947711352595)
    ·
      refine ⟨111331079127902921567028893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74220719418601947711352595 111331079127902921567028893)
      ·
        refine ⟨41749154672963595587635835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111331079127902921567028893 41749154672963595587635835)
        ·
          refine ⟨62623732009445393381453753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41749154672963595587635835 62623732009445393381453753)
          ·
            refine ⟨46967799007084045036090315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62623732009445393381453753 46967799007084045036090315)
            ·
              refine ⟨70451698510626067554135473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46967799007084045036090315 70451698510626067554135473)
              ·
                refine ⟨52838773882969550665601605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70451698510626067554135473 52838773882969550665601605)
                ·
                  refine ⟨9907270103056790749800301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52838773882969550665601605 9907270103056790749800301)
                  ·
                    refine ⟨3715226288646296531175113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9907270103056790749800301 3715226288646296531175113)
                    ·
                      refine ⟨2786419716484722398381335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715226288646296531175113 2786419716484722398381335)
                      ·
                        rfl

theorem cell23_5426533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_5426533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426533 prefixEnd_5426533 := by exact prefixLift 5426533
  have htrace : WordTrace (prefixWord ++ tailWord_5426533) baseStart_5426533 baseEnd_5426533 := by
    simpa [prefixWord, tailWord_5426533, baseEnd_5426533] using wordTrace_append hprefix tailTrace_5426533
  have hstable : (prefixWord ++ tailWord_5426533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426533).length < 2 ^ (prefixWord ++ tailWord_5426533).sum := by decide
  have hdescent : baseEnd_5426533 < baseStart_5426533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426556 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_5426556 : Nat := 118140960795 + 5426556 * 2 ^ 59
def prefixEnd_5426556 : Nat := 4983230072969 + 3 ^ 40 * 5426556 * 2
def baseEnd_5426556 : Nat := 928810508846591936131243

theorem tailTrace_5426556 : CollatzResearch.WordTrace tailWord_5426556 prefixEnd_5426556 928810508846591936131243 := by
  unfold tailWord_5426556
  simp only [CollatzResearch.WordTrace]
  refine ⟨98961378664260934412513761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131948504885681245883351681 98961378664260934412513761)
  ·
    refine ⟨74221033998195700809385321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98961378664260934412513761 74221033998195700809385321)
    ·
      refine ⟨55665775498646775607038991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74221033998195700809385321 55665775498646775607038991)
      ·
        refine ⟨83498663247970163410558487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55665775498646775607038991 83498663247970163410558487)
        ·
          refine ⟨125247994871955245115837731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83498663247970163410558487 125247994871955245115837731)
          ·
            refine ⟨187871992307932867673756597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125247994871955245115837731 187871992307932867673756597)
            ·
              refine ⟨17612999278868706344414681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187871992307932867673756597 17612999278868706344414681)
              ·
                refine ⟨13209749459151529758311011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17612999278868706344414681 13209749459151529758311011)
                ·
                  refine ⟨19814624188727294637466517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13209749459151529758311011 19814624188727294637466517)
                  ·
                    refine ⟨928810508846591936131243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19814624188727294637466517 928810508846591936131243)
                    ·
                      rfl

theorem cell23_5426556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_5426556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426556 prefixEnd_5426556 := by exact prefixLift 5426556
  have htrace : WordTrace (prefixWord ++ tailWord_5426556) baseStart_5426556 baseEnd_5426556 := by
    simpa [prefixWord, tailWord_5426556, baseEnd_5426556] using wordTrace_append hprefix tailTrace_5426556
  have hstable : (prefixWord ++ tailWord_5426556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426556).length < 2 ^ (prefixWord ++ tailWord_5426556).sum := by decide
  have hdescent : baseEnd_5426556 < baseStart_5426556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426569 : List Nat := [1, 2, 1, 1, 18]
def baseStart_5426569 : Nat := 118140960795 + 5426569 * 2 ^ 59
def prefixEnd_5426569 : Nat := 4983230072969 + 3 ^ 40 * 5426569 * 2
def baseEnd_5426569 : Nat := 3822274625223983892361

theorem tailTrace_5426569 : CollatzResearch.WordTrace tailWord_5426569 prefixEnd_5426569 3822274625223983892361 := by
  unfold tailWord_5426569
  simp only [CollatzResearch.WordTrace]
  refine ⟨197923231477474772045250761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131948820984983181363500507 197923231477474772045250761)
  ·
    refine ⟨148442423608106079033938071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197923231477474772045250761 148442423608106079033938071)
    ·
      refine ⟨222663635412159118550907107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148442423608106079033938071 222663635412159118550907107)
      ·
        refine ⟨333995453118238677826360661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222663635412159118550907107 333995453118238677826360661)
        ·
          refine ⟨3822274625223983892361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 18 333995453118238677826360661 3822274625223983892361)
          ·
            rfl

theorem cell23_5426569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 18].length) (baseStart_5426569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426569 prefixEnd_5426569 := by exact prefixLift 5426569
  have htrace : WordTrace (prefixWord ++ tailWord_5426569) baseStart_5426569 baseEnd_5426569 := by
    simpa [prefixWord, tailWord_5426569, baseEnd_5426569] using wordTrace_append hprefix tailTrace_5426569
  have hstable : (prefixWord ++ tailWord_5426569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426569).length < 2 ^ (prefixWord ++ tailWord_5426569).sum := by decide
  have hdescent : baseEnd_5426569 < baseStart_5426569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426574 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5426574 : Nat := 118140960795 + 5426574 * 2 ^ 59
def prefixEnd_5426574 : Nat := 4983230072969 + 3 ^ 40 * 5426574 * 2
def baseEnd_5426574 : Nat := 2786440769191556737968647

theorem tailTrace_5426574 : CollatzResearch.WordTrace tailWord_5426574 prefixEnd_5426574 2786440769191556737968647 := by
  unfold tailWord_5426574
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740426730307082237397847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131948942561637771932788517 24740426730307082237397847)
  ·
    refine ⟨37110640095460623356096771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24740426730307082237397847 37110640095460623356096771)
    ·
      refine ⟨55665960143190935034145157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37110640095460623356096771 55665960143190935034145157)
      ·
        refine ⟨10437367526848300318902217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55665960143190935034145157 10437367526848300318902217)
        ·
          refine ⟨7828025645136225239176663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10437367526848300318902217 7828025645136225239176663)
          ·
            refine ⟨11742038467704337858764995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828025645136225239176663 11742038467704337858764995)
            ·
              refine ⟨17613057701556506788147493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11742038467704337858764995 17613057701556506788147493)
              ·
                refine ⟨3302448319041845022777655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17613057701556506788147493 3302448319041845022777655)
                ·
                  refine ⟨4953672478562767534166483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302448319041845022777655 4953672478562767534166483)
                  ·
                    refine ⟨7430508717844151301249725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4953672478562767534166483 7430508717844151301249725)
                    ·
                      refine ⟨2786440769191556737968647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7430508717844151301249725 2786440769191556737968647)
                      ·
                        rfl

theorem cell23_5426574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5426574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426574 prefixEnd_5426574 := by exact prefixLift 5426574
  have htrace : WordTrace (prefixWord ++ tailWord_5426574) baseStart_5426574 baseEnd_5426574 := by
    simpa [prefixWord, tailWord_5426574, baseEnd_5426574] using wordTrace_append hprefix tailTrace_5426574
  have hstable : (prefixWord ++ tailWord_5426574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426574).length < 2 ^ (prefixWord ++ tailWord_5426574).sum := by decide
  have hdescent : baseEnd_5426574 < baseStart_5426574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426657 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_5426657 : Nat := 118140960795 + 5426657 * 2 ^ 59
def prefixEnd_5426657 : Nat := 4983230072969 + 3 ^ 40 * 5426657 * 2
def baseEnd_5426657 : Nat := 2786483388085879913230765

theorem tailTrace_5426657 : CollatzResearch.WordTrace tailWord_5426657 prefixEnd_5426657 2786483388085879913230765 := by
  unfold tailWord_5426657
  simp only [CollatzResearch.WordTrace]
  refine ⟨197926441101155963074454225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131950960734103975382969483 197926441101155963074454225)
  ·
    refine ⟨148444830825866972305840669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197926441101155963074454225 148444830825866972305840669)
    ·
      refine ⟨55666811559700114614690251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148444830825866972305840669 55666811559700114614690251)
      ·
        refine ⟨83500217339550171922035377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55666811559700114614690251 83500217339550171922035377)
        ·
          refine ⟨62625163004662628941526533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83500217339550171922035377 62625163004662628941526533)
          ·
            refine ⟨11742218063374242926536225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62625163004662628941526533 11742218063374242926536225)
            ·
              refine ⟨8806663547530682194902169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11742218063374242926536225 8806663547530682194902169)
              ·
                refine ⟨6604997660648011646176627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806663547530682194902169 6604997660648011646176627)
                ·
                  refine ⟨9907496490972017469264941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6604997660648011646176627 9907496490972017469264941)
                  ·
                    refine ⟨3715311184114506550974353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9907496490972017469264941 3715311184114506550974353)
                    ·
                      refine ⟨2786483388085879913230765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715311184114506550974353 2786483388085879913230765)
                      ·
                        rfl

theorem cell23_5426657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_5426657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426657 prefixEnd_5426657 := by exact prefixLift 5426657
  have htrace : WordTrace (prefixWord ++ tailWord_5426657) baseStart_5426657 baseEnd_5426657 := by
    simpa [prefixWord, tailWord_5426657, baseEnd_5426657] using wordTrace_append hprefix tailTrace_5426657
  have hstable : (prefixWord ++ tailWord_5426657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426657).length < 2 ^ (prefixWord ++ tailWord_5426657).sum := by decide
  have hdescent : baseEnd_5426657 < baseStart_5426657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426670 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_5426670 : Nat := 118140960795 + 5426670 * 2 ^ 59
def prefixEnd_5426670 : Nat := 4983230072969 + 3 ^ 40 * 5426670 * 2
def baseEnd_5426670 : Nat := 2786490063334388362368205

theorem tailTrace_5426670 : CollatzResearch.WordTrace tailWord_5426670 prefixEnd_5426670 2786490063334388362368205 := by
  unfold tailWord_5426670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740864406263608286834683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131951276833405910863118309 24740864406263608286834683)
  ·
    refine ⟨37111296609395412430252025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24740864406263608286834683 37111296609395412430252025)
    ·
      refine ⟨27833472457046559322689019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37111296609395412430252025 27833472457046559322689019)
      ·
        refine ⟨41750208685569838984033529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27833472457046559322689019 41750208685569838984033529)
        ·
          refine ⟨31312656514177379238025147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41750208685569838984033529 31312656514177379238025147)
          ·
            refine ⟨46968984771266068857037721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31312656514177379238025147 46968984771266068857037721)
            ·
              refine ⟨35226738578449551642778291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46968984771266068857037721 35226738578449551642778291)
              ·
                refine ⟨52840107867674327464167437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35226738578449551642778291 52840107867674327464167437)
                ·
                  refine ⟨19815040450377872799062789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52840107867674327464167437 19815040450377872799062789)
                  ·
                    refine ⟨3715320084445851149824273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19815040450377872799062789 3715320084445851149824273)
                    ·
                      refine ⟨2786490063334388362368205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715320084445851149824273 2786490063334388362368205)
                      ·
                        rfl

theorem cell23_5426670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_5426670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426670 prefixEnd_5426670 := by exact prefixLift 5426670
  have htrace : WordTrace (prefixWord ++ tailWord_5426670) baseStart_5426670 baseEnd_5426670 := by
    simpa [prefixWord, tailWord_5426670, baseEnd_5426670] using wordTrace_append hprefix tailTrace_5426670
  have hstable : (prefixWord ++ tailWord_5426670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426670).length < 2 ^ (prefixWord ++ tailWord_5426670).sum := by decide
  have hdescent : baseEnd_5426670 < baseStart_5426670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426673 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_5426673 : Nat := 118140960795 + 5426673 * 2 ^ 59
def prefixEnd_5426673 : Nat := 4983230072969 + 3 ^ 40 * 5426673 * 2
def baseEnd_5426673 : Nat := 2786491603776351850630691

theorem tailTrace_5426673 : CollatzResearch.WordTrace tailWord_5426673 prefixEnd_5426673 2786491603776351850630691 := by
  unfold tailWord_5426673
  simp only [CollatzResearch.WordTrace]
  refine ⟨197927024669097997807036673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131951349779398665204691115 197927024669097997807036673)
  ·
    refine ⟨148445268501823498355277505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197927024669097997807036673 148445268501823498355277505)
    ·
      refine ⟨111333951376367623766458129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148445268501823498355277505 111333951376367623766458129)
      ·
        refine ⟨83500463532275717824843597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111333951376367623766458129 83500463532275717824843597)
        ·
          refine ⟨31312673824603394184316349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83500463532275717824843597 31312673824603394184316349)
          ·
            refine ⟨11742252684226272819118631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31312673824603394184316349 11742252684226272819118631)
            ·
              refine ⟨17613379026339409228677947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11742252684226272819118631 17613379026339409228677947)
              ·
                refine ⟨26420068539509113843016921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17613379026339409228677947 26420068539509113843016921)
                ·
                  refine ⟨19815051404631835382262691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26420068539509113843016921 19815051404631835382262691)
                  ·
                    refine ⟨29722577106947753073394037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19815051404631835382262691 29722577106947753073394037)
                    ·
                      refine ⟨2786491603776351850630691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29722577106947753073394037 2786491603776351850630691)
                      ·
                        rfl

theorem cell23_5426673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_5426673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426673 prefixEnd_5426673 := by exact prefixLift 5426673
  have htrace : WordTrace (prefixWord ++ tailWord_5426673) baseStart_5426673 baseEnd_5426673 := by
    simpa [prefixWord, tailWord_5426673, baseEnd_5426673] using wordTrace_append hprefix tailTrace_5426673
  have hstable : (prefixWord ++ tailWord_5426673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426673).length < 2 ^ (prefixWord ++ tailWord_5426673).sum := by decide
  have hdescent : baseEnd_5426673 < baseStart_5426673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426708 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5426708 : Nat := 118140960795 + 5426708 * 2 ^ 59
def prefixEnd_5426708 : Nat := 4983230072969 + 3 ^ 40 * 5426708 * 2
def baseEnd_5426708 : Nat := 2786509575599259213693031

theorem tailTrace_5426708 : CollatzResearch.WordTrace tailWord_5426708 prefixEnd_5426708 2786509575599259213693031 := by
  unfold tailWord_5426708
  simp only [CollatzResearch.WordTrace]
  refine ⟨98964150611985599392280389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131952200815980799189707185 98964150611985599392280389)
  ·
    refine ⟨18555778239747299886052573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98964150611985599392280389 18555778239747299886052573)
    ·
      refine ⟨6958416839905237457269715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18555778239747299886052573 6958416839905237457269715)
      ·
        refine ⟨10437625259857856185904573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6958416839905237457269715 10437625259857856185904573)
        ·
          refine ⟨3914109472446696069714215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10437625259857856185904573 3914109472446696069714215)
          ·
            refine ⟨5871164208670044104571323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914109472446696069714215 5871164208670044104571323)
            ·
              refine ⟨8806746313005066156856985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871164208670044104571323 8806746313005066156856985)
              ·
                refine ⟨6605059734753799617642739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806746313005066156856985 6605059734753799617642739)
                ·
                  refine ⟨9907589602130699426464109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6605059734753799617642739 9907589602130699426464109)
                  ·
                    refine ⟨3715346100799012284924041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9907589602130699426464109 3715346100799012284924041)
                    ·
                      refine ⟨2786509575599259213693031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715346100799012284924041 2786509575599259213693031)
                      ·
                        rfl

theorem cell23_5426708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5426708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426708 prefixEnd_5426708 := by exact prefixLift 5426708
  have htrace : WordTrace (prefixWord ++ tailWord_5426708) baseStart_5426708 baseEnd_5426708 := by
    simpa [prefixWord, tailWord_5426708, baseEnd_5426708] using wordTrace_append hprefix tailTrace_5426708
  have hstable : (prefixWord ++ tailWord_5426708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426708).length < 2 ^ (prefixWord ++ tailWord_5426708).sum := by decide
  have hdescent : baseEnd_5426708 < baseStart_5426708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426763 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 3]
def baseStart_5426763 : Nat := 118140960795 + 5426763 * 2 ^ 59
def prefixEnd_5426763 : Nat := 4983230072969 + 3 ^ 40 * 5426763 * 2
def baseEnd_5426763 : Nat := 2786537817035256498505277

theorem tailTrace_5426763 : CollatzResearch.WordTrace tailWord_5426763 prefixEnd_5426763 2786537817035256498505277 := by
  unfold tailWord_5426763
  simp only [CollatzResearch.WordTrace]
  refine ⟨197930307238771943177812943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131953538159181295451875295 197930307238771943177812943)
  ·
    refine ⟨296895460858157914766719415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197930307238771943177812943 296895460858157914766719415)
    ·
      refine ⟨445343191287236872150079123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296895460858157914766719415 445343191287236872150079123)
      ·
        refine ⟨668014786930855308225118685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445343191287236872150079123 668014786930855308225118685)
        ·
          refine ⟨250505545099070740584419507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 668014786930855308225118685 250505545099070740584419507)
          ·
            refine ⟨375758317648606110876629261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250505545099070740584419507 375758317648606110876629261)
            ·
              refine ⟨140909369118227291578735973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375758317648606110876629261 140909369118227291578735973)
              ·
                refine ⟨26420506709667617171012995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140909369118227291578735973 26420506709667617171012995)
                ·
                  refine ⟨39630760064501425756519493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26420506709667617171012995 39630760064501425756519493)
                  ·
                    refine ⟨7430767512094017329347405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39630760064501425756519493 7430767512094017329347405)
                    ·
                      refine ⟨2786537817035256498505277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7430767512094017329347405 2786537817035256498505277)
                      ·
                        rfl

theorem cell23_5426763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 3].length) (baseStart_5426763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426763 prefixEnd_5426763 := by exact prefixLift 5426763
  have htrace : WordTrace (prefixWord ++ tailWord_5426763) baseStart_5426763 baseEnd_5426763 := by
    simpa [prefixWord, tailWord_5426763, baseEnd_5426763] using wordTrace_append hprefix tailTrace_5426763
  have hstable : (prefixWord ++ tailWord_5426763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426763).length < 2 ^ (prefixWord ++ tailWord_5426763).sum := by decide
  have hdescent : baseEnd_5426763 < baseStart_5426763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426770 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_5426770 : Nat := 118140960795 + 5426770 * 2 ^ 59
def prefixEnd_5426770 : Nat := 4983230072969 + 3 ^ 40 * 5426770 * 2
def baseEnd_5426770 : Nat := 928847137133279323705915

theorem tailTrace_5426770 : CollatzResearch.WordTrace tailWord_5426770 prefixEnd_5426770 928847137133279323705915 := by
  unfold tailWord_5426770
  simp only [CollatzResearch.WordTrace]
  refine ⟨49482640637436645843329441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131953708366497722248878509 49482640637436645843329441)
  ·
    refine ⟨37111980478077484382497081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49482640637436645843329441 37111980478077484382497081)
    ·
      refine ⟨27833985358558113286872811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37111980478077484382497081 27833985358558113286872811)
      ·
        refine ⟨41750978037837169930309217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27833985358558113286872811 41750978037837169930309217)
        ·
          refine ⟨31313233528377877447731913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41750978037837169930309217 31313233528377877447731913)
          ·
            refine ⟨23484925146283408085798935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31313233528377877447731913 23484925146283408085798935)
            ·
              refine ⟨35227387719425112128698403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23484925146283408085798935 35227387719425112128698403)
              ·
                refine ⟨52841081579137668193047605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35227387719425112128698403 52841081579137668193047605)
                ·
                  refine ⟨4953851398044156393098213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52841081579137668193047605 4953851398044156393098213)
                  ·
                    refine ⟨928847137133279323705915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953851398044156393098213 928847137133279323705915)
                    ·
                      rfl

theorem cell23_5426770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_5426770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426770 prefixEnd_5426770 := by exact prefixLift 5426770
  have htrace : WordTrace (prefixWord ++ tailWord_5426770) baseStart_5426770 baseEnd_5426770 := by
    simpa [prefixWord, tailWord_5426770, baseEnd_5426770] using wordTrace_append hprefix tailTrace_5426770
  have hstable : (prefixWord ++ tailWord_5426770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426770).length < 2 ^ (prefixWord ++ tailWord_5426770).sum := by decide
  have hdescent : baseEnd_5426770 < baseStart_5426770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426774 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5426774 : Nat := 118140960795 + 5426774 * 2 ^ 59
def prefixEnd_5426774 : Nat := 4983230072969 + 3 ^ 40 * 5426774 * 2
def baseEnd_5426774 : Nat := 928847821774151985155909

theorem tailTrace_5426774 : CollatzResearch.WordTrace tailWord_5426774 prefixEnd_5426774 928847821774151985155909 := by
  unfold tailWord_5426774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12370669277608255753528961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131953805627821394704308917 12370669277608255753528961)
  ·
    refine ⟨9278001958206191815146721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12370669277608255753528961 9278001958206191815146721)
    ·
      refine ⟨6958501468654643861360041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9278001958206191815146721 6958501468654643861360041)
      ·
        refine ⟨5218876101490982896020031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6958501468654643861360041 5218876101490982896020031)
        ·
          refine ⟨7828314152236474344030047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218876101490982896020031 7828314152236474344030047)
          ·
            refine ⟨11742471228354711516045071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828314152236474344030047 11742471228354711516045071)
            ·
              refine ⟨17613706842532067274067607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11742471228354711516045071 17613706842532067274067607)
              ·
                refine ⟨26420560263798100911101411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17613706842532067274067607 26420560263798100911101411)
                ·
                  refine ⟨39630840395697151366652117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26420560263798100911101411 39630840395697151366652117)
                  ·
                    refine ⟨928847821774151985155909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39630840395697151366652117 928847821774151985155909)
                    ·
                      rfl

theorem cell23_5426774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5426774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426774 prefixEnd_5426774 := by exact prefixLift 5426774
  have htrace : WordTrace (prefixWord ++ tailWord_5426774) baseStart_5426774 baseEnd_5426774 := by
    simpa [prefixWord, tailWord_5426774, baseEnd_5426774] using wordTrace_append hprefix tailTrace_5426774
  have hstable : (prefixWord ++ tailWord_5426774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426774).length < 2 ^ (prefixWord ++ tailWord_5426774).sum := by decide
  have hdescent : baseEnd_5426774 < baseStart_5426774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426787 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 1, 4]
def baseStart_5426787 : Nat := 118140960795 + 5426787 * 2 ^ 59
def prefixEnd_5426787 : Nat := 4983230072969 + 3 ^ 40 * 5426787 * 2
def baseEnd_5426787 : Nat := 928850046856988134868389

theorem tailTrace_5426787 : CollatzResearch.WordTrace tailWord_5426787 prefixEnd_5426787 928850046856988134868389 := by
  unfold tailWord_5426787
  simp only [CollatzResearch.WordTrace]
  refine ⟨197931182590684995276686615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131954121727123330184457743 197931182590684995276686615)
  ·
    refine ⟨296896773886027492915029923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197931182590684995276686615 296896773886027492915029923)
    ·
      refine ⟨445345160829041239372544885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296896773886027492915029923 445345160829041239372544885)
      ·
        refine ⟨41751108827722616191176083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 445345160829041239372544885 41751108827722616191176083)
        ·
          refine ⟨62626663241583924286764125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41751108827722616191176083 62626663241583924286764125)
          ·
            refine ⟨23484998715593971607536547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62626663241583924286764125 23484998715593971607536547)
            ·
              refine ⟨35227498073390957411304821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23484998715593971607536547 35227498073390957411304821)
              ·
                refine ⟨3302577944380402257309827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35227498073390957411304821 3302577944380402257309827)
                ·
                  refine ⟨4953866916570603385964741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302577944380402257309827 4953866916570603385964741)
                  ·
                    refine ⟨928850046856988134868389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953866916570603385964741 928850046856988134868389)
                    ·
                      rfl

theorem cell23_5426787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 4].length) (baseStart_5426787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426787 prefixEnd_5426787 := by exact prefixLift 5426787
  have htrace : WordTrace (prefixWord ++ tailWord_5426787) baseStart_5426787 baseEnd_5426787 := by
    simpa [prefixWord, tailWord_5426787, baseEnd_5426787] using wordTrace_append hprefix tailTrace_5426787
  have hstable : (prefixWord ++ tailWord_5426787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426787).length < 2 ^ (prefixWord ++ tailWord_5426787).sum := by decide
  have hdescent : baseEnd_5426787 < baseStart_5426787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426800 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 6]
def baseStart_5426800 : Nat := 118140960795 + 5426800 * 2 ^ 59
def prefixEnd_5426800 : Nat := 4983230072969 + 3 ^ 40 * 5426800 * 2
def baseEnd_5426800 : Nat := 309617423979941428193623

theorem tailTrace_5426800 : CollatzResearch.WordTrace tailWord_5426800 prefixEnd_5426800 309617423979941428193623 := by
  unfold tailWord_5426800
  simp only [CollatzResearch.WordTrace]
  refine ⟨98965828369818949248454927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131954437826425265664606569 98965828369818949248454927)
  ·
    refine ⟨148448742554728423872682391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98965828369818949248454927 148448742554728423872682391)
    ·
      refine ⟨222673113832092635809023587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148448742554728423872682391 222673113832092635809023587)
      ·
        refine ⟨334009670748138953713535381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222673113832092635809023587 334009670748138953713535381)
        ·
          refine ⟨15656703316319013455321971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 334009670748138953713535381 15656703316319013455321971)
          ·
            refine ⟨23485054974478520182982957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15656703316319013455321971 23485054974478520182982957)
            ·
              refine ⟨8806895615429445068618609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23485054974478520182982957 8806895615429445068618609)
              ·
                refine ⟨6605171711572083801463957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806895615429445068618609 6605171711572083801463957)
                ·
                  refine ⟨309617423979941428193623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6605171711572083801463957 309617423979941428193623)
                  ·
                    rfl

theorem cell23_5426800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_5426800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426800 prefixEnd_5426800 := by exact prefixLift 5426800
  have htrace : WordTrace (prefixWord ++ tailWord_5426800) baseStart_5426800 baseEnd_5426800 := by
    simpa [prefixWord, tailWord_5426800, baseEnd_5426800] using wordTrace_append hprefix tailTrace_5426800
  have hstable : (prefixWord ++ tailWord_5426800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426800).length < 2 ^ (prefixWord ++ tailWord_5426800).sum := by decide
  have hdescent : baseEnd_5426800 < baseStart_5426800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426817 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 6]
def baseStart_5426817 : Nat := 118140960795 + 5426817 * 2 ^ 59
def prefixEnd_5426817 : Nat := 4983230072969 + 3 ^ 40 * 5426817 * 2
def baseEnd_5426817 : Nat := 309618393887844365247781

theorem tailTrace_5426817 : CollatzResearch.WordTrace tailWord_5426817 prefixEnd_5426817 309618393887844365247781 := by
  unfold tailWord_5426817
  simp only [CollatzResearch.WordTrace]
  refine ⟨197932276780576310400278705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131954851187050873600185803 197932276780576310400278705)
  ·
    refine ⟨148449207585432232800209029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197932276780576310400278705 148449207585432232800209029)
    ·
      refine ⟨27834226422268543650039193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148449207585432232800209029 27834226422268543650039193)
      ·
        refine ⟨20875669816701407737529395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27834226422268543650039193 20875669816701407737529395)
        ·
          refine ⟨31313504725052111606294093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20875669816701407737529395 31313504725052111606294093)
          ·
            refine ⟨11742564271894541852360285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31313504725052111606294093 11742564271894541852360285)
            ·
              refine ⟨4403461601960453194635107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11742564271894541852360285 4403461601960453194635107)
              ·
                refine ⟨6605192402940679791952661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403461601960453194635107 6605192402940679791952661)
                ·
                  refine ⟨309618393887844365247781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6605192402940679791952661 309618393887844365247781)
                  ·
                    rfl

theorem cell23_5426817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 6].length) (baseStart_5426817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426817 prefixEnd_5426817 := by exact prefixLift 5426817
  have htrace : WordTrace (prefixWord ++ tailWord_5426817) baseStart_5426817 baseEnd_5426817 := by
    simpa [prefixWord, tailWord_5426817, baseEnd_5426817] using wordTrace_append hprefix tailTrace_5426817
  have hstable : (prefixWord ++ tailWord_5426817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426817).length < 2 ^ (prefixWord ++ tailWord_5426817).sum := by decide
  have hdescent : baseEnd_5426817 < baseStart_5426817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426863 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_5426863 : Nat := 118140960795 + 5426863 * 2 ^ 59
def prefixEnd_5426863 : Nat := 4983230072969 + 3 ^ 40 * 5426863 * 2
def baseEnd_5426863 : Nat := 2786589165100706107254817

theorem tailTrace_5426863 : CollatzResearch.WordTrace tailWord_5426863 prefixEnd_5426863 2786589165100706107254817 := by
  unfold tailWord_5426863
  simp only [CollatzResearch.WordTrace]
  refine ⟨197933954538409660256453243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131955969692273106837635495 197933954538409660256453243)
  ·
    refine ⟨296900931807614490384679865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197933954538409660256453243 296900931807614490384679865)
    ·
      refine ⟨222675698855710867788509899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296900931807614490384679865 222675698855710867788509899)
      ·
        refine ⟨334013548283566301682764849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222675698855710867788509899 334013548283566301682764849)
        ·
          refine ⟨250510161212674726262073637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334013548283566301682764849 250510161212674726262073637)
          ·
            refine ⟨46970655227376511174138807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250510161212674726262073637 46970655227376511174138807)
            ·
              refine ⟨70455982841064766761208211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46970655227376511174138807 70455982841064766761208211)
              ·
                refine ⟨105683974261597150141812317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70455982841064766761208211 105683974261597150141812317)
                ·
                  refine ⟨39631490348098931303179619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105683974261597150141812317 39631490348098931303179619)
                  ·
                    refine ⟨59447235522148396954769429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39631490348098931303179619 59447235522148396954769429)
                    ·
                      refine ⟨2786589165100706107254817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59447235522148396954769429 2786589165100706107254817)
                      ·
                        rfl

theorem cell23_5426863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_5426863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426863 prefixEnd_5426863 := by exact prefixLift 5426863
  have htrace : WordTrace (prefixWord ++ tailWord_5426863) baseStart_5426863 baseEnd_5426863 := by
    simpa [prefixWord, tailWord_5426863, baseEnd_5426863] using wordTrace_append hprefix tailTrace_5426863
  have hstable : (prefixWord ++ tailWord_5426863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426863).length < 2 ^ (prefixWord ++ tailWord_5426863).sum := by decide
  have hdescent : baseEnd_5426863 < baseStart_5426863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426873 : List Nat := [1, 2, 1, 4, 1, 1, 3, 10]
def baseStart_5426873 : Nat := 118140960795 + 5426873 * 2 ^ 59
def prefixEnd_5426873 : Nat := 4983230072969 + 3 ^ 40 * 5426873 * 2
def baseEnd_5426873 : Nat := 103207196292861150671473

theorem tailTrace_5426873 : CollatzResearch.WordTrace tailWord_5426873 prefixEnd_5426873 103207196292861150671473 := by
  unfold tailWord_5426873
  simp only [CollatzResearch.WordTrace]
  refine ⟨197934319268373431964317273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131956212845582287976211515 197934319268373431964317273)
  ·
    refine ⟨148450739451280073973237955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197934319268373431964317273 148450739451280073973237955)
    ·
      refine ⟨222676109176920110959856933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148450739451280073973237955 222676109176920110959856933)
      ·
        refine ⟨41751770470672520804973175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222676109176920110959856933 41751770470672520804973175)
        ·
          refine ⟨62627655706008781207459763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41751770470672520804973175 62627655706008781207459763)
          ·
            refine ⟨93941483559013171811189645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62627655706008781207459763 93941483559013171811189645)
            ·
              refine ⟨35228056334629939429196117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93941483559013171811189645 35228056334629939429196117)
              ·
                refine ⟨103207196292861150671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35228056334629939429196117 103207196292861150671473)
                ·
                  rfl

theorem cell23_5426873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 10].length) (baseStart_5426873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426873 prefixEnd_5426873 := by exact prefixLift 5426873
  have htrace : WordTrace (prefixWord ++ tailWord_5426873) baseStart_5426873 baseEnd_5426873 := by
    simpa [prefixWord, tailWord_5426873, baseEnd_5426873] using wordTrace_append hprefix tailTrace_5426873
  have hstable : (prefixWord ++ tailWord_5426873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426873).length < 2 ^ (prefixWord ++ tailWord_5426873).sum := by decide
  have hdescent : baseEnd_5426873 < baseStart_5426873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426877 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_5426877 : Nat := 118140960795 + 5426877 * 2 ^ 59
def prefixEnd_5426877 : Nat := 4983230072969 + 3 ^ 40 * 5426877 * 2
def baseEnd_5426877 : Nat := 928865451276623017493251

theorem tailTrace_5426877 : CollatzResearch.WordTrace tailWord_5426877 prefixEnd_5426877 928865451276623017493251 := by
  unfold tailWord_5426877
  simp only [CollatzResearch.WordTrace]
  refine ⟨197934465160358940647462885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131956310106905960431641923 197934465160358940647462885)
  ·
    refine ⟨37112712217567301371399291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197934465160358940647462885 37112712217567301371399291)
    ·
      refine ⟨55669068326350952057098937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37112712217567301371399291 55669068326350952057098937)
      ·
        refine ⟨41751801244763214042824203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55669068326350952057098937 41751801244763214042824203)
        ·
          refine ⟨62627701867144821064236305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41751801244763214042824203 62627701867144821064236305)
          ·
            refine ⟨46970776400358615798177229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62627701867144821064236305 46970776400358615798177229)
            ·
              refine ⟨17614041150134480924316461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46970776400358615798177229 17614041150134480924316461)
              ·
                refine ⟨6605265431300430346618673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17614041150134480924316461 6605265431300430346618673)
                ·
                  refine ⟨4953949073475322759964005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6605265431300430346618673 4953949073475322759964005)
                  ·
                    refine ⟨928865451276623017493251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953949073475322759964005 928865451276623017493251)
                    ·
                      rfl

theorem cell23_5426877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_5426877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426877 prefixEnd_5426877 := by exact prefixLift 5426877
  have htrace : WordTrace (prefixWord ++ tailWord_5426877) baseStart_5426877 baseEnd_5426877 := by
    simpa [prefixWord, tailWord_5426877, baseEnd_5426877] using wordTrace_append hprefix tailTrace_5426877
  have hstable : (prefixWord ++ tailWord_5426877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426877).length < 2 ^ (prefixWord ++ tailWord_5426877).sum := by decide
  have hdescent : baseEnd_5426877 < baseStart_5426877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426880 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_5426880 : Nat := 118140960795 + 5426880 * 2 ^ 59
def prefixEnd_5426880 : Nat := 4983230072969 + 3 ^ 40 * 5426880 * 2
def baseEnd_5426880 : Nat := 2786597894271832540742239

theorem tailTrace_5426880 : CollatzResearch.WordTrace tailWord_5426880 prefixEnd_5426880 2786597894271832540742239 := by
  unfold tailWord_5426880
  simp only [CollatzResearch.WordTrace]
  refine ⟨98967287289674036079911047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131956383052898714773214729 98967287289674036079911047)
  ·
    refine ⟨148450930934511054119866571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98967287289674036079911047 148450930934511054119866571)
    ·
      refine ⟨222676396401766581179799857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148450930934511054119866571 222676396401766581179799857)
      ·
        refine ⟨167007297301324935884849893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222676396401766581179799857 167007297301324935884849893)
        ·
          refine ⟨31313868243998425478409355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167007297301324935884849893 31313868243998425478409355)
          ·
            refine ⟨46970802365997638217614033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31313868243998425478409355 46970802365997638217614033)
            ·
              refine ⟨35228101774498228663210525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46970802365997638217614033 35228101774498228663210525)
              ·
                refine ⟨13210538165436835748703947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35228101774498228663210525 13210538165436835748703947)
                ·
                  refine ⟨19815807248155253623055921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13210538165436835748703947 19815807248155253623055921)
                  ·
                    refine ⟨14861855436116440217291941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19815807248155253623055921 14861855436116440217291941)
                    ·
                      refine ⟨2786597894271832540742239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14861855436116440217291941 2786597894271832540742239)
                      ·
                        rfl

theorem cell23_5426880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_5426880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426880 prefixEnd_5426880 := by exact prefixLift 5426880
  have htrace : WordTrace (prefixWord ++ tailWord_5426880) baseStart_5426880 baseEnd_5426880 := by
    simpa [prefixWord, tailWord_5426880, baseEnd_5426880] using wordTrace_append hprefix tailTrace_5426880
  have hstable : (prefixWord ++ tailWord_5426880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426880).length < 2 ^ (prefixWord ++ tailWord_5426880).sum := by decide
  have hdescent : baseEnd_5426880 < baseStart_5426880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426884 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_5426884 : Nat := 118140960795 + 5426884 * 2 ^ 59
def prefixEnd_5426884 : Nat := 4983230072969 + 3 ^ 40 * 5426884 * 2
def baseEnd_5426884 : Nat := 2786599948194450525092221

theorem tailTrace_5426884 : CollatzResearch.WordTrace tailWord_5426884 prefixEnd_5426884 2786599948194450525092221 := by
  unfold tailWord_5426884
  simp only [CollatzResearch.WordTrace]
  refine ⟨98967360235666790421483853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131956480314222387228645137 98967360235666790421483853)
  ·
    refine ⟨37112760088375046408056445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98967360235666790421483853 37112760088375046408056445)
    ·
      refine ⟨13917285033140642403021167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37112760088375046408056445 13917285033140642403021167)
      ·
        refine ⟨20875927549710963604531751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13917285033140642403021167 20875927549710963604531751)
        ·
          refine ⟨31313891324566445406797627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20875927549710963604531751 31313891324566445406797627)
          ·
            refine ⟨46970836986849668110196441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31313891324566445406797627 46970836986849668110196441)
            ·
              refine ⟨35228127740137251082647331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46970836986849668110196441 35228127740137251082647331)
              ·
                refine ⟨52842191610205876623970997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35228127740137251082647331 52842191610205876623970997)
                ·
                  refine ⟨4953955463456800933497281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52842191610205876623970997 4953955463456800933497281)
                  ·
                    refine ⟨3715466597592600700122961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4953955463456800933497281 3715466597592600700122961)
                    ·
                      refine ⟨2786599948194450525092221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715466597592600700122961 2786599948194450525092221)
                      ·
                        rfl

theorem cell23_5426884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_5426884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426884 prefixEnd_5426884 := by exact prefixLift 5426884
  have htrace : WordTrace (prefixWord ++ tailWord_5426884) baseStart_5426884 baseEnd_5426884 := by
    simpa [prefixWord, tailWord_5426884, baseEnd_5426884] using wordTrace_append hprefix tailTrace_5426884
  have hstable : (prefixWord ++ tailWord_5426884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426884).length < 2 ^ (prefixWord ++ tailWord_5426884).sum := by decide
  have hdescent : baseEnd_5426884 < baseStart_5426884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426904 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 1, 2, 3]
def baseStart_5426904 : Nat := 118140960795 + 5426904 * 2 ^ 59
def prefixEnd_5426904 : Nat := 4983230072969 + 3 ^ 40 * 5426904 * 2
def baseEnd_5426904 : Nat := 2786610217807540446842129

theorem tailTrace_5426904 : CollatzResearch.WordTrace tailWord_5426904 prefixEnd_5426904 2786610217807540446842129 := by
  unfold tailWord_5426904
  simp only [CollatzResearch.WordTrace]
  refine ⟨98967724965630562129347883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131956966620840749505797177 98967724965630562129347883)
  ·
    refine ⟨148451587448445843194021825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98967724965630562129347883 148451587448445843194021825)
    ·
      refine ⟨111338690586334382395516369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148451587448445843194021825 111338690586334382395516369)
      ·
        refine ⟨83504017939750786796637277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111338690586334382395516369 83504017939750786796637277)
        ·
          refine ⟨31314006727406545048738979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83504017939750786796637277 31314006727406545048738979)
          ·
            refine ⟨46971010091109817573108469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31314006727406545048738979 46971010091109817573108469)
            ·
              refine ⟨4403532196041545397478919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46971010091109817573108469 4403532196041545397478919)
              ·
                refine ⟨6605298294062318096218379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403532196041545397478919 6605298294062318096218379)
                ·
                  refine ⟨9907947441093477144327569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6605298294062318096218379 9907947441093477144327569)
                  ·
                    refine ⟨7430960580820107858245677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9907947441093477144327569 7430960580820107858245677)
                    ·
                      refine ⟨2786610217807540446842129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7430960580820107858245677 2786610217807540446842129)
                      ·
                        rfl

theorem cell23_5426904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_5426904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426904 prefixEnd_5426904 := by exact prefixLift 5426904
  have htrace : WordTrace (prefixWord ++ tailWord_5426904) baseStart_5426904 baseEnd_5426904 := by
    simpa [prefixWord, tailWord_5426904, baseEnd_5426904] using wordTrace_append hprefix tailTrace_5426904
  have hstable : (prefixWord ++ tailWord_5426904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426904).length < 2 ^ (prefixWord ++ tailWord_5426904).sum := by decide
  have hdescent : baseEnd_5426904 < baseStart_5426904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426920 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_5426920 : Nat := 118140960795 + 5426920 * 2 ^ 59
def prefixEnd_5426920 : Nat := 4983230072969 + 3 ^ 40 * 5426920 * 2
def baseEnd_5426920 : Nat := 928872811166004128080685

theorem tailTrace_5426920 : CollatzResearch.WordTrace tailWord_5426920 prefixEnd_5426920 928872811166004128080685 := by
  unfold tailWord_5426920
  simp only [CollatzResearch.WordTrace]
  refine ⟨98968016749601579495639107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131957355666135439327518809 98968016749601579495639107)
  ·
    refine ⟨148452025124402369243458661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98968016749601579495639107 148452025124402369243458661)
    ·
      refine ⟨27834754710825444233148499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148452025124402369243458661 27834754710825444233148499)
      ·
        refine ⟨41752132066238166349722749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27834754710825444233148499 41752132066238166349722749)
        ·
          refine ⟨15657049524839312381146031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41752132066238166349722749 15657049524839312381146031)
          ·
            refine ⟨23485574287258968571719047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15657049524839312381146031 23485574287258968571719047)
            ·
              refine ⟨35228361430888452857578571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23485574287258968571719047 35228361430888452857578571)
              ·
                refine ⟨52842542146332679286367857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35228361430888452857578571 52842542146332679286367857)
                ·
                  refine ⟨39631906609749509464775893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52842542146332679286367857 39631906609749509464775893)
                  ·
                    refine ⟨928872811166004128080685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39631906609749509464775893 928872811166004128080685)
                    ·
                      rfl

theorem cell23_5426920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_5426920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426920 prefixEnd_5426920 := by exact prefixLift 5426920
  have htrace : WordTrace (prefixWord ++ tailWord_5426920) baseStart_5426920 baseEnd_5426920 := by
    simpa [prefixWord, tailWord_5426920, baseEnd_5426920] using wordTrace_append hprefix tailTrace_5426920
  have hstable : (prefixWord ++ tailWord_5426920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426920).length < 2 ^ (prefixWord ++ tailWord_5426920).sum := by decide
  have hdescent : baseEnd_5426920 < baseStart_5426920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426927 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 5, 3, 2]
def baseStart_5426927 : Nat := 118140960795 + 5426927 * 2 ^ 59
def prefixEnd_5426927 : Nat := 4983230072969 + 3 ^ 40 * 5426927 * 2
def baseEnd_5426927 : Nat := 2786622027862593856854523

theorem tailTrace_5426927 : CollatzResearch.WordTrace tailWord_5426927 prefixEnd_5426927 2786622027862593856854523 := by
  unfold tailWord_5426927
  simp only [CollatzResearch.WordTrace]
  refine ⟨197936288810177799186783035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131957525873451866124522023 197936288810177799186783035)
  ·
    refine ⟨296904433215266698780174553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197936288810177799186783035 296904433215266698780174553)
    ·
      refine ⟨222678324911450024085130915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296904433215266698780174553 222678324911450024085130915)
      ·
        refine ⟨334017487367175036127696373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222678324911450024085130915 334017487367175036127696373)
        ·
          refine ⟨31314139440672659636971535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334017487367175036127696373 31314139440672659636971535)
          ·
            refine ⟨46971209161008989455457303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31314139440672659636971535 46971209161008989455457303)
            ·
              refine ⟨70456813741513484183185955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46971209161008989455457303 70456813741513484183185955)
              ·
                refine ⟨105685220612270226274778933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70456813741513484183185955 105685220612270226274778933)
                ·
                  refine ⟨9907989432400333713260525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105685220612270226274778933 9907989432400333713260525)
                  ·
                    refine ⟨3715496037150125142472697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9907989432400333713260525 3715496037150125142472697)
                    ·
                      refine ⟨2786622027862593856854523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715496037150125142472697 2786622027862593856854523)
                      ·
                        rfl

theorem cell23_5426927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3, 2].length) (baseStart_5426927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426927 prefixEnd_5426927 := by exact prefixLift 5426927
  have htrace : WordTrace (prefixWord ++ tailWord_5426927) baseStart_5426927 baseEnd_5426927 := by
    simpa [prefixWord, tailWord_5426927, baseEnd_5426927] using wordTrace_append hprefix tailTrace_5426927
  have hstable : (prefixWord ++ tailWord_5426927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426927).length < 2 ^ (prefixWord ++ tailWord_5426927).sum := by decide
  have hdescent : baseEnd_5426927 < baseStart_5426927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426934 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5426934 : Nat := 118140960795 + 5426934 * 2 ^ 59
def prefixEnd_5426934 : Nat := 4983230072969 + 3 ^ 40 * 5426934 * 2
def baseEnd_5426934 : Nat := 2786625622227175329466991

theorem tailTrace_5426934 : CollatzResearch.WordTrace tailWord_5426934 prefixEnd_5426934 2786625622227175329466991 := by
  unfold tailWord_5426934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371034007572027461392991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131957696080768292921525237 12371034007572027461392991)
  ·
    refine ⟨18556551011358041192089487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12371034007572027461392991 18556551011358041192089487)
    ·
      refine ⟨27834826517037061788134231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18556551011358041192089487 27834826517037061788134231)
      ·
        refine ⟨41752239775555592682201347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27834826517037061788134231 41752239775555592682201347)
        ·
          refine ⟨62628359663333389023302021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41752239775555592682201347 62628359663333389023302021)
          ·
            refine ⟨11742817436875010441869129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62628359663333389023302021 11742817436875010441869129)
            ·
              refine ⟨8807113077656257831401847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11742817436875010441869129 8807113077656257831401847)
              ·
                refine ⟨13210669616484386747102771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8807113077656257831401847 13210669616484386747102771)
                ·
                  refine ⟨19816004424726580120654157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13210669616484386747102771 19816004424726580120654157)
                  ·
                    refine ⟨7431001659272467545245309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19816004424726580120654157 7431001659272467545245309)
                    ·
                      refine ⟨2786625622227175329466991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7431001659272467545245309 2786625622227175329466991)
                      ·
                        rfl

theorem cell23_5426934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5426934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426934 prefixEnd_5426934 := by exact prefixLift 5426934
  have htrace : WordTrace (prefixWord ++ tailWord_5426934) baseStart_5426934 baseEnd_5426934 := by
    simpa [prefixWord, tailWord_5426934, baseEnd_5426934] using wordTrace_append hprefix tailTrace_5426934
  have hstable : (prefixWord ++ tailWord_5426934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426934).length < 2 ^ (prefixWord ++ tailWord_5426934).sum := by decide
  have hdescent : baseEnd_5426934 < baseStart_5426934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5426940 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_5426940 : Nat := 118140960795 + 5426940 * 2 ^ 59
def prefixEnd_5426940 : Nat := 4983230072969 + 3 ^ 40 * 5426940 * 2
def baseEnd_5426940 : Nat := 2786628703111102305991963

theorem tailTrace_5426940 : CollatzResearch.WordTrace tailWord_5426940 prefixEnd_5426940 2786628703111102305991963 := by
  unfold tailWord_5426940
  simp only [CollatzResearch.WordTrace]
  refine ⟨98968381479565351203503137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131957841972753801604670849 98968381479565351203503137)
  ·
    refine ⟨74226286109674013402627353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98968381479565351203503137 74226286109674013402627353)
    ·
      refine ⟨55669714582255510051970515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74226286109674013402627353 55669714582255510051970515)
      ·
        refine ⟨83504571873383265077955773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55669714582255510051970515 83504571873383265077955773)
        ·
          refine ⟨31314214452518724404233415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83504571873383265077955773 31314214452518724404233415)
          ·
            refine ⟨46971321678778086606350123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31314214452518724404233415 46971321678778086606350123)
            ·
              refine ⟨70456982518167129909525185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46971321678778086606350123 70456982518167129909525185)
              ·
                refine ⟨52842736888625347432143889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70456982518167129909525185 52842736888625347432143889)
                ·
                  refine ⟨39632052666469010574107917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52842736888625347432143889 39632052666469010574107917)
                  ·
                    refine ⟨14862019749925878965290469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39632052666469010574107917 14862019749925878965290469)
                    ·
                      refine ⟨2786628703111102305991963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14862019749925878965290469 2786628703111102305991963)
                      ·
                        rfl

theorem cell23_5426940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_5426940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5426940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5426940 prefixEnd_5426940 := by exact prefixLift 5426940
  have htrace : WordTrace (prefixWord ++ tailWord_5426940) baseStart_5426940 baseEnd_5426940 := by
    simpa [prefixWord, tailWord_5426940, baseEnd_5426940] using wordTrace_append hprefix tailTrace_5426940
  have hstable : (prefixWord ++ tailWord_5426940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5426940).length < 2 ^ (prefixWord ++ tailWord_5426940).sum := by decide
  have hdescent : baseEnd_5426940 < baseStart_5426940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5426940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427031 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 5]
def baseStart_5427031 : Nat := 118140960795 + 5427031 * 2 ^ 59
def prefixEnd_5427031 : Nat := 4983230072969 + 3 ^ 40 * 5427031 * 2
def baseEnd_5427031 : Nat := 309630603316740161106005

theorem tailTrace_5427031 : CollatzResearch.WordTrace tailWord_5427031 prefixEnd_5427031 309630603316740161106005 := by
  unfold tailWord_5427031
  simp only [CollatzResearch.WordTrace]
  refine ⟨197940082001801024948568947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131960054667867349965712631 197940082001801024948568947)
  ·
    refine ⟨296910123002701537422853421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197940082001801024948568947 296910123002701537422853421)
    ·
      refine ⟨111341296126013076533570033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296910123002701537422853421 111341296126013076533570033)
      ·
        refine ⟨83505972094509807400177525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111341296126013076533570033 83505972094509807400177525)
        ·
          refine ⟨7828684883860294443766643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83505972094509807400177525 7828684883860294443766643)
          ·
            refine ⟨11743027325790441665649965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828684883860294443766643 11743027325790441665649965)
            ·
              refine ⟨4403635247171415624618737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11743027325790441665649965 4403635247171415624618737)
              ·
                refine ⟨3302726435378561718464053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4403635247171415624618737 3302726435378561718464053)
                ·
                  refine ⟨309630603316740161106005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3302726435378561718464053 309630603316740161106005)
                  ·
                    rfl

theorem cell23_5427031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 5].length) (baseStart_5427031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427031 prefixEnd_5427031 := by exact prefixLift 5427031
  have htrace : WordTrace (prefixWord ++ tailWord_5427031) baseStart_5427031 baseEnd_5427031 := by
    simpa [prefixWord, tailWord_5427031, baseEnd_5427031] using wordTrace_append hprefix tailTrace_5427031
  have hstable : (prefixWord ++ tailWord_5427031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427031).length < 2 ^ (prefixWord ++ tailWord_5427031).sum := by decide
  have hdescent : baseEnd_5427031 < baseStart_5427031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427047 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5427047 : Nat := 118140960795 + 5427047 * 2 ^ 59
def prefixEnd_5427047 : Nat := 4983230072969 + 3 ^ 40 * 5427047 * 2
def baseEnd_5427047 : Nat := 2786683645541133387353971

theorem tailTrace_5427047 : CollatzResearch.WordTrace tailWord_5427047 prefixEnd_5427047 2786683645541133387353971 := by
  unfold tailWord_5427047
  simp only [CollatzResearch.WordTrace]
  refine ⟨197940665569743059681151395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131960443713162039787434263 197940665569743059681151395)
  ·
    refine ⟨296910998354614589521727093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197940665569743059681151395 296910998354614589521727093)
    ·
      refine ⟨27835406095745117767661915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296910998354614589521727093 27835406095745117767661915)
      ·
        refine ⟨41753109143617676651492873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27835406095745117767661915 41753109143617676651492873)
        ·
          refine ⟨31314831857713257488619655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41753109143617676651492873 31314831857713257488619655)
          ·
            refine ⟨46972247786569886232929483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31314831857713257488619655 46972247786569886232929483)
            ·
              refine ⟨70458371679854829349394225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46972247786569886232929483 70458371679854829349394225)
              ·
                refine ⟨52843778759891122012045669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70458371679854829349394225 52843778759891122012045669)
                ·
                  refine ⟨9908208517479585377258563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52843778759891122012045669 9908208517479585377258563)
                  ·
                    refine ⟨14862312776219378065887845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9908208517479585377258563 14862312776219378065887845)
                    ·
                      refine ⟨2786683645541133387353971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14862312776219378065887845 2786683645541133387353971)
                      ·
                        rfl

theorem cell23_5427047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5427047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427047 prefixEnd_5427047 := by exact prefixLift 5427047
  have htrace : WordTrace (prefixWord ++ tailWord_5427047) baseStart_5427047 baseEnd_5427047 := by
    simpa [prefixWord, tailWord_5427047, baseEnd_5427047] using wordTrace_append hprefix tailTrace_5427047
  have hstable : (prefixWord ++ tailWord_5427047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427047).length < 2 ^ (prefixWord ++ tailWord_5427047).sum := by decide
  have hdescent : baseEnd_5427047 < baseStart_5427047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427057 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 5, 4]
def baseStart_5427057 : Nat := 118140960795 + 5427057 * 2 ^ 59
def prefixEnd_5427057 : Nat := 4983230072969 + 3 ^ 40 * 5427057 * 2
def baseEnd_5427057 : Nat := 928896260115892782742975

theorem tailTrace_5427057 : CollatzResearch.WordTrace tailWord_5427057 prefixEnd_5427057 928896260115892782742975 := by
  unfold tailWord_5427057
  simp only [CollatzResearch.WordTrace]
  refine ⟨197941030299706831389015425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131960686866471220926010283 197941030299706831389015425)
  ·
    refine ⟨148455772724780123541761569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197941030299706831389015425 148455772724780123541761569)
    ·
      refine ⟨111341829543585092656321177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148455772724780123541761569 111341829543585092656321177)
      ·
        refine ⟨83506372157688819492240883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111341829543585092656321177 83506372157688819492240883)
        ·
          refine ⟨125259558236533229238361325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83506372157688819492240883 125259558236533229238361325)
          ·
            refine ⟨46972334338699960964385497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125259558236533229238361325 46972334338699960964385497)
            ·
              refine ⟨35229250754024970723289123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46972334338699960964385497 35229250754024970723289123)
              ·
                refine ⟨52843876131037456084933685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35229250754024970723289123 52843876131037456084933685)
                ·
                  refine ⟨4954113387284761507962533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52843876131037456084933685 4954113387284761507962533)
                  ·
                    refine ⟨928896260115892782742975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954113387284761507962533 928896260115892782742975)
                    ·
                      rfl

theorem cell23_5427057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_5427057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427057 prefixEnd_5427057 := by exact prefixLift 5427057
  have htrace : WordTrace (prefixWord ++ tailWord_5427057) baseStart_5427057 baseEnd_5427057 := by
    simpa [prefixWord, tailWord_5427057, baseEnd_5427057] using wordTrace_append hprefix tailTrace_5427057
  have hstable : (prefixWord ++ tailWord_5427057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427057).length < 2 ^ (prefixWord ++ tailWord_5427057).sum := by decide
  have hdescent : baseEnd_5427057 < baseStart_5427057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427131 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 1, 1, 3]
def baseStart_5427131 : Nat := 118140960795 + 5427131 * 2 ^ 59
def prefixEnd_5427131 : Nat := 4983230072969 + 3 ^ 40 * 5427131 * 2
def baseEnd_5427131 : Nat := 2786726777916111058703585

theorem tailTrace_5427131 : CollatzResearch.WordTrace tailWord_5427131 prefixEnd_5427131 2786726777916111058703585 := by
  unfold tailWord_5427131
  simp only [CollatzResearch.WordTrace]
  refine ⟨197943729301438742027209247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131962486200959161351472831 197943729301438742027209247)
  ·
    refine ⟨296915593952158113040813871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197943729301438742027209247 296915593952158113040813871)
    ·
      refine ⟨445373390928237169561220807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296915593952158113040813871 445373390928237169561220807)
      ·
        refine ⟨668060086392355754341831211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445373390928237169561220807 668060086392355754341831211)
        ·
          refine ⟨1002090129588533631512746817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668060086392355754341831211 1002090129588533631512746817)
          ·
            refine ⟨751567597191400223634560113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002090129588533631512746817 751567597191400223634560113)
            ·
              refine ⟨563675697893550167725920085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751567597191400223634560113 563675697893550167725920085)
              ·
                refine ⟨3302787292345020514019063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 563675697893550167725920085 3302787292345020514019063)
                ·
                  refine ⟨4954180938517530771028595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302787292345020514019063 4954180938517530771028595)
                  ·
                    refine ⟨7431271407776296156542893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954180938517530771028595 7431271407776296156542893)
                    ·
                      refine ⟨2786726777916111058703585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7431271407776296156542893 2786726777916111058703585)
                      ·
                        rfl

theorem cell23_5427131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 1, 3].length) (baseStart_5427131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427131 prefixEnd_5427131 := by exact prefixLift 5427131
  have htrace : WordTrace (prefixWord ++ tailWord_5427131) baseStart_5427131 baseEnd_5427131 := by
    simpa [prefixWord, tailWord_5427131, baseEnd_5427131] using wordTrace_append hprefix tailTrace_5427131
  have hstable : (prefixWord ++ tailWord_5427131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427131).length < 2 ^ (prefixWord ++ tailWord_5427131).sum := by decide
  have hdescent : baseEnd_5427131 < baseStart_5427131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427148 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5427148 : Nat := 118140960795 + 5427148 * 2 ^ 59
def prefixEnd_5427148 : Nat := 4983230072969 + 3 ^ 40 * 5427148 * 2
def baseEnd_5427148 : Nat := 2786735507087237492191007

theorem tailTrace_5427148 : CollatzResearch.WordTrace tailWord_5427148 prefixEnd_5427148 2786735507087237492191007 := by
  unfold tailWord_5427148
  simp only [CollatzResearch.WordTrace]
  refine ⟨98972174671188576965289049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131962899561584769287052065 98972174671188576965289049)
  ·
    refine ⟨74229131003391432723966787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98972174671188576965289049 74229131003391432723966787)
    ·
      refine ⟨111343696505087149085950181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74229131003391432723966787 111343696505087149085950181)
      ·
        refine ⟨20876943094703840453615659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111343696505087149085950181 20876943094703840453615659)
        ·
          refine ⟨31315414642055760680423489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20876943094703840453615659 31315414642055760680423489)
          ·
            refine ⟨23486560981541820510317617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31315414642055760680423489 23486560981541820510317617)
            ·
              refine ⟨17614920736156365382738213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23486560981541820510317617 17614920736156365382738213)
              ·
                refine ⟨3302797638029318509263415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17614920736156365382738213 3302797638029318509263415)
                ·
                  refine ⟨4954196457043977763895123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302797638029318509263415 4954196457043977763895123)
                  ·
                    refine ⟨7431294685565966645842685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954196457043977763895123 7431294685565966645842685)
                    ·
                      refine ⟨2786735507087237492191007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7431294685565966645842685 2786735507087237492191007)
                      ·
                        rfl

theorem cell23_5427148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5427148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427148 prefixEnd_5427148 := by exact prefixLift 5427148
  have htrace : WordTrace (prefixWord ++ tailWord_5427148) baseStart_5427148 baseEnd_5427148 := by
    simpa [prefixWord, tailWord_5427148, baseEnd_5427148] using wordTrace_append hprefix tailTrace_5427148
  have hstable : (prefixWord ++ tailWord_5427148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427148).length < 2 ^ (prefixWord ++ tailWord_5427148).sum := by decide
  have hdescent : baseEnd_5427148 < baseStart_5427148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427171 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 4]
def baseStart_5427171 : Nat := 118140960795 + 5427171 * 2 ^ 59
def prefixEnd_5427171 : Nat := 4983230072969 + 3 ^ 40 * 5427171 * 2
def baseEnd_5427171 : Nat := 2786747317142290902203401

theorem tailTrace_5427171 : CollatzResearch.WordTrace tailWord_5427171 prefixEnd_5427171 2786747317142290902203401 := by
  unfold tailWord_5427171
  simp only [CollatzResearch.WordTrace]
  refine ⟨197945188221293828858665367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131963458814195885905776911 197945188221293828858665367)
  ·
    refine ⟨296917782331940743287998051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197945188221293828858665367 296917782331940743287998051)
    ·
      refine ⟨445376673497911114931997077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296917782331940743287998051 445376673497911114931997077)
      ·
        refine ⟨20877031570214583512437363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 445376673497911114931997077 20877031570214583512437363)
        ·
          refine ⟨31315547355321875268656045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20877031570214583512437363 31315547355321875268656045)
          ·
            refine ⟨11743330258245703225746017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31315547355321875268656045 11743330258245703225746017)
            ·
              refine ⟨8807497693684277419309513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11743330258245703225746017 8807497693684277419309513)
              ·
                refine ⟨6605623270263208064482135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8807497693684277419309513 6605623270263208064482135)
                ·
                  refine ⟨9908434905394812096723203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6605623270263208064482135 9908434905394812096723203)
                  ·
                    refine ⟨14862652358092218145084805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9908434905394812096723203 14862652358092218145084805)
                    ·
                      refine ⟨2786747317142290902203401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14862652358092218145084805 2786747317142290902203401)
                      ·
                        rfl

theorem cell23_5427171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_5427171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427171 prefixEnd_5427171 := by exact prefixLift 5427171
  have htrace : WordTrace (prefixWord ++ tailWord_5427171) baseStart_5427171 baseEnd_5427171 := by
    simpa [prefixWord, tailWord_5427171, baseEnd_5427171] using wordTrace_append hprefix tailTrace_5427171
  have hstable : (prefixWord ++ tailWord_5427171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427171).length < 2 ^ (prefixWord ++ tailWord_5427171).sum := by decide
  have hdescent : baseEnd_5427171 < baseStart_5427171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427227 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4]
def baseStart_5427227 : Nat := 118140960795 + 5427227 * 2 ^ 59
def prefixEnd_5427227 : Nat := 4983230072969 + 3 ^ 40 * 5427227 * 2
def baseEnd_5427227 : Nat := 2786776072058942683103143

theorem tailTrace_5427227 : CollatzResearch.WordTrace tailWord_5427227 prefixEnd_5427227 2786776072058942683103143 := by
  unfold tailWord_5427227
  simp only [CollatzResearch.WordTrace]
  refine ⟨197947230709090950422703935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131964820472727300281802623 197947230709090950422703935)
  ·
    refine ⟨296920846063636425634055903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197947230709090950422703935 296920846063636425634055903)
    ·
      refine ⟨445381269095454638451083855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296920846063636425634055903 445381269095454638451083855)
      ·
        refine ⟨668071903643181957676625783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445381269095454638451083855 668071903643181957676625783)
        ·
          refine ⟨1002107855464772936514938675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668071903643181957676625783 1002107855464772936514938675)
          ·
            refine ⟨1503161783197159404772408013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002107855464772936514938675 1503161783197159404772408013)
            ·
              refine ⟨563685668698934776789653005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1503161783197159404772408013 563685668698934776789653005)
              ·
                refine ⟨211382125762100541296119877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563685668698934776789653005 211382125762100541296119877)
                ·
                  refine ⟨39634148580393851493022477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211382125762100541296119877 39634148580393851493022477)
                  ·
                    refine ⟨14862805717647694309883429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39634148580393851493022477 14862805717647694309883429)
                    ·
                      refine ⟨2786776072058942683103143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14862805717647694309883429 2786776072058942683103143)
                      ·
                        rfl

theorem cell23_5427227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_5427227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427227 prefixEnd_5427227 := by exact prefixLift 5427227
  have htrace : WordTrace (prefixWord ++ tailWord_5427227) baseStart_5427227 baseEnd_5427227 := by
    simpa [prefixWord, tailWord_5427227, baseEnd_5427227] using wordTrace_append hprefix tailTrace_5427227
  have hstable : (prefixWord ++ tailWord_5427227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427227).length < 2 ^ (prefixWord ++ tailWord_5427227).sum := by decide
  have hdescent : baseEnd_5427227 < baseStart_5427227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427231 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 3, 3, 2]
def baseStart_5427231 : Nat := 118140960795 + 5427231 * 2 ^ 59
def prefixEnd_5427231 : Nat := 4983230072969 + 3 ^ 40 * 5427231 * 2
def baseEnd_5427231 : Nat := 2786778125981560667453125

theorem tailTrace_5427231 : CollatzResearch.WordTrace tailWord_5427231 prefixEnd_5427231 2786778125981560667453125 := by
  unfold tailWord_5427231
  simp only [CollatzResearch.WordTrace]
  refine ⟨197947376601076459105849547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131964917734050972737233031 197947376601076459105849547)
  ·
    refine ⟨296921064901614688658774321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197947376601076459105849547 296921064901614688658774321)
    ·
      refine ⟨222690798676211016494080741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296921064901614688658774321 222690798676211016494080741)
      ·
        refine ⟨41754524751789565592640139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222690798676211016494080741 41754524751789565592640139)
        ·
          refine ⟨62631787127684348388960209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41754524751789565592640139 62631787127684348388960209)
          ·
            refine ⟨46973840345763261291720157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62631787127684348388960209 46973840345763261291720157)
            ·
              refine ⟨17615190129661222984395059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46973840345763261291720157 17615190129661222984395059)
              ·
                refine ⟨26422785194491834476592589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17615190129661222984395059 26422785194491834476592589)
                ·
                  refine ⟨9908544447934437928722221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26422785194491834476592589 9908544447934437928722221)
                  ·
                    refine ⟨3715704167975414223270833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9908544447934437928722221 3715704167975414223270833)
                    ·
                      refine ⟨2786778125981560667453125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715704167975414223270833 2786778125981560667453125)
                      ·
                        rfl

theorem cell23_5427231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_5427231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427231 prefixEnd_5427231 := by exact prefixLift 5427231
  have htrace : WordTrace (prefixWord ++ tailWord_5427231) baseStart_5427231 baseEnd_5427231 := by
    simpa [prefixWord, tailWord_5427231, baseEnd_5427231] using wordTrace_append hprefix tailTrace_5427231
  have hstable : (prefixWord ++ tailWord_5427231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427231).length < 2 ^ (prefixWord ++ tailWord_5427231).sum := by decide
  have hdescent : baseEnd_5427231 < baseStart_5427231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427247 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_5427247 : Nat := 118140960795 + 5427247 * 2 ^ 59
def prefixEnd_5427247 : Nat := 4983230072969 + 3 ^ 40 * 5427247 * 2
def baseEnd_5427247 : Nat := 2786786341672032604853051

theorem tailTrace_5427247 : CollatzResearch.WordTrace tailWord_5427247 prefixEnd_5427247 2786786341672032604853051 := by
  unfold tailWord_5427247
  simp only [CollatzResearch.WordTrace]
  refine ⟨197947960169018493838431995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131965306779345662558954663 197947960169018493838431995)
  ·
    refine ⟨296921940253527740757647993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197947960169018493838431995 296921940253527740757647993)
    ·
      refine ⟨222691455190145805568235995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296921940253527740757647993 222691455190145805568235995)
      ·
        refine ⟨334037182785218708352353993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222691455190145805568235995 334037182785218708352353993)
        ·
          refine ⟨250527887088914031264265495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334037182785218708352353993 250527887088914031264265495)
          ·
            refine ⟨375791830633371046896398243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250527887088914031264265495 375791830633371046896398243)
            ·
              refine ⟨563687745950056570344597365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375791830633371046896398243 563687745950056570344597365)
              ·
                refine ⟨52845726182817803469806003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 563687745950056570344597365 52845726182817803469806003)
                ·
                  refine ⟨79268589274226705204709005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52845726182817803469806003 79268589274226705204709005)
                  ·
                    refine ⟨29725720977835014451765877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79268589274226705204709005 29725720977835014451765877)
                    ·
                      refine ⟨2786786341672032604853051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29725720977835014451765877 2786786341672032604853051)
                      ·
                        rfl

theorem cell23_5427247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_5427247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427247 prefixEnd_5427247 := by exact prefixLift 5427247
  have htrace : WordTrace (prefixWord ++ tailWord_5427247) baseStart_5427247 baseEnd_5427247 := by
    simpa [prefixWord, tailWord_5427247, baseEnd_5427247] using wordTrace_append hprefix tailTrace_5427247
  have hstable : (prefixWord ++ tailWord_5427247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427247).length < 2 ^ (prefixWord ++ tailWord_5427247).sum := by decide
  have hdescent : baseEnd_5427247 < baseStart_5427247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427261 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_5427261 : Nat := 118140960795 + 5427261 * 2 ^ 59
def prefixEnd_5427261 : Nat := 4983230072969 + 3 ^ 40 * 5427261 * 2
def baseEnd_5427261 : Nat := 2786793530401195550077987

theorem tailTrace_5427261 : CollatzResearch.WordTrace tailWord_5427261 prefixEnd_5427261 2786793530401195550077987 := by
  unfold tailWord_5427261
  simp only [CollatzResearch.WordTrace]
  refine ⟨197948470790967774229441637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131965647193978516152961091 197948470790967774229441637)
  ·
    refine ⟨37115338273306457668020307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197948470790967774229441637 37115338273306457668020307)
    ·
      refine ⟨55673007409959686502030461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37115338273306457668020307 55673007409959686502030461)
      ·
        refine ⟨20877377778734882438261423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55673007409959686502030461 20877377778734882438261423)
        ·
          refine ⟨31316066668102323657392135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20877377778734882438261423 31316066668102323657392135)
          ·
            refine ⟨46974100002153485486088203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31316066668102323657392135 46974100002153485486088203)
            ·
              refine ⟨70461150003230228229132305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46974100002153485486088203 70461150003230228229132305)
              ·
                refine ⟨52845862502422671171849229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70461150003230228229132305 52845862502422671171849229)
                ·
                  refine ⟨19817198438408501689443461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52845862502422671171849229 19817198438408501689443461)
                  ·
                    refine ⟨3715724707201594066770649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19817198438408501689443461 3715724707201594066770649)
                    ·
                      refine ⟨2786793530401195550077987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715724707201594066770649 2786793530401195550077987)
                      ·
                        rfl

theorem cell23_5427261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_5427261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427261 prefixEnd_5427261 := by exact prefixLift 5427261
  have htrace : WordTrace (prefixWord ++ tailWord_5427261) baseStart_5427261 baseEnd_5427261 := by
    simpa [prefixWord, tailWord_5427261, baseEnd_5427261] using wordTrace_append hprefix tailTrace_5427261
  have hstable : (prefixWord ++ tailWord_5427261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427261).length < 2 ^ (prefixWord ++ tailWord_5427261).sum := by decide
  have hdescent : baseEnd_5427261 < baseStart_5427261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427264 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_5427264 : Nat := 118140960795 + 5427264 * 2 ^ 59
def prefixEnd_5427264 : Nat := 4983230072969 + 3 ^ 40 * 5427264 * 2
def baseEnd_5427264 : Nat := 2786795070843159038340473

theorem tailTrace_5427264 : CollatzResearch.WordTrace tailWord_5427264 prefixEnd_5427264 2786795070843159038340473 := by
  unfold tailWord_5427264
  simp only [CollatzResearch.WordTrace]
  refine ⟨98974290104978452870900423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131965720139971270494533897 98974290104978452870900423)
  ·
    refine ⟨148461435157467679306350635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98974290104978452870900423 148461435157467679306350635)
    ·
      refine ⟨222692152736201518959525953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148461435157467679306350635 222692152736201518959525953)
      ·
        refine ⟨167019114552151139219644465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222692152736201518959525953 167019114552151139219644465)
        ·
          refine ⟨125264335914113354414733349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167019114552151139219644465 125264335914113354414733349)
          ·
            refine ⟨23487062983896253952762503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125264335914113354414733349 23487062983896253952762503)
            ·
              refine ⟨35230594475844380929143755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23487062983896253952762503 35230594475844380929143755)
              ·
                refine ⟨52845891713766571393715633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35230594475844380929143755 52845891713766571393715633)
                ·
                  refine ⟨39634418785324928545286725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52845891713766571393715633 39634418785324928545286725)
                  ·
                    refine ⟨7431453522248424102241261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39634418785324928545286725 7431453522248424102241261)
                    ·
                      refine ⟨2786795070843159038340473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7431453522248424102241261 2786795070843159038340473)
                      ·
                        rfl

theorem cell23_5427264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_5427264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427264 prefixEnd_5427264 := by exact prefixLift 5427264
  have htrace : WordTrace (prefixWord ++ tailWord_5427264) baseStart_5427264 baseEnd_5427264 := by
    simpa [prefixWord, tailWord_5427264, baseEnd_5427264] using wordTrace_append hprefix tailTrace_5427264
  have hstable : (prefixWord ++ tailWord_5427264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427264).length < 2 ^ (prefixWord ++ tailWord_5427264).sum := by decide
  have hdescent : baseEnd_5427264 < baseStart_5427264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427278 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_5427278 : Nat := 118140960795 + 5427278 * 2 ^ 59
def prefixEnd_5427278 : Nat := 4983230072969 + 3 ^ 40 * 5427278 * 2
def baseEnd_5427278 : Nat := 2786802259572321983565409

theorem tailTrace_5427278 : CollatzResearch.WordTrace tailWord_5427278 prefixEnd_5427278 2786802259572321983565409 := by
  unfold tailWord_5427278
  simp only [CollatzResearch.WordTrace]
  refine ⟨24743636353988273266601311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131966060554604124088540325 24743636353988273266601311)
  ·
    refine ⟨37115454530982409899901967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24743636353988273266601311 37115454530982409899901967)
    ·
      refine ⟨55673181796473614849852951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37115454530982409899901967 55673181796473614849852951)
      ·
        refine ⟨83509772694710422274779427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55673181796473614849852951 83509772694710422274779427)
        ·
          refine ⟨125264659042065633412169141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83509772694710422274779427 125264659042065633412169141)
          ·
            refine ⟨11743561785193653132390857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125264659042065633412169141 11743561785193653132390857)
            ·
              refine ⟨8807671338895239849293143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11743561785193653132390857 8807671338895239849293143)
              ·
                refine ⟨13211507008342859773939715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8807671338895239849293143 13211507008342859773939715)
                ·
                  refine ⟨19817260512514289660909573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13211507008342859773939715 19817260512514289660909573)
                  ·
                    refine ⟨3715736346096429311420545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19817260512514289660909573 3715736346096429311420545)
                    ·
                      refine ⟨2786802259572321983565409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715736346096429311420545 2786802259572321983565409)
                      ·
                        rfl

theorem cell23_5427278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_5427278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427278 prefixEnd_5427278 := by exact prefixLift 5427278
  have htrace : WordTrace (prefixWord ++ tailWord_5427278) baseStart_5427278 baseEnd_5427278 := by
    simpa [prefixWord, tailWord_5427278, baseEnd_5427278] using wordTrace_append hprefix tailTrace_5427278
  have hstable : (prefixWord ++ tailWord_5427278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427278).length < 2 ^ (prefixWord ++ tailWord_5427278).sum := by decide
  have hdescent : baseEnd_5427278 < baseStart_5427278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427301 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 5]
def baseStart_5427301 : Nat := 118140960795 + 5427301 * 2 ^ 59
def prefixEnd_5427301 : Nat := 4983230072969 + 3 ^ 40 * 5427301 * 2
def baseEnd_5427301 : Nat := 309646007736375043730867

theorem tailTrace_5427301 : CollatzResearch.WordTrace tailWord_5427301 prefixEnd_5427301 309646007736375043730867 := by
  unfold tailWord_5427301
  simp only [CollatzResearch.WordTrace]
  refine ⟨197949929710822861060897757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131966619807215240707265171 197949929710822861060897757)
  ·
    refine ⟨74231223641558572897836659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197949929710822861060897757 74231223641558572897836659)
    ·
      refine ⟨111346835462337859346754989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74231223641558572897836659 111346835462337859346754989)
      ·
        refine ⟨41755063298376697255033121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111346835462337859346754989 41755063298376697255033121)
        ·
          refine ⟨31316297473782522941274841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41755063298376697255033121 31316297473782522941274841)
          ·
            refine ⟨23487223105336892205956131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31316297473782522941274841 23487223105336892205956131)
            ·
              refine ⟨35230834658005338308934197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23487223105336892205956131 35230834658005338308934197)
              ·
                refine ⟨3302890749188000466462581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35230834658005338308934197 3302890749188000466462581)
                ·
                  refine ⟨309646007736375043730867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3302890749188000466462581 309646007736375043730867)
                  ·
                    rfl

theorem cell23_5427301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_5427301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427301 prefixEnd_5427301 := by exact prefixLift 5427301
  have htrace : WordTrace (prefixWord ++ tailWord_5427301) baseStart_5427301 baseEnd_5427301 := by
    simpa [prefixWord, tailWord_5427301, baseEnd_5427301] using wordTrace_append hprefix tailTrace_5427301
  have hstable : (prefixWord ++ tailWord_5427301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427301).length < 2 ^ (prefixWord ++ tailWord_5427301).sum := by decide
  have hdescent : baseEnd_5427301 < baseStart_5427301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427318 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_5427318 : Nat := 118140960795 + 5427318 * 2 ^ 59
def prefixEnd_5427318 : Nat := 4983230072969 + 3 ^ 40 * 5427318 * 2
def baseEnd_5427318 : Nat := 309646977644277980785025

theorem tailTrace_5427318 : CollatzResearch.WordTrace tailWord_5427318 prefixEnd_5427318 309646977644277980785025 := by
  unfold tailWord_5427318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371909359485079560266663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131967033167840848642844405 12371909359485079560266663)
  ·
    refine ⟨18557864039227619340399995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12371909359485079560266663 18557864039227619340399995)
    ·
      refine ⟨27836796058841429010599993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18557864039227619340399995 27836796058841429010599993)
      ·
        refine ⟨20877597044131071757949995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27836796058841429010599993 20877597044131071757949995)
        ·
          refine ⟨31316395566196607636924993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20877597044131071757949995 31316395566196607636924993)
          ·
            refine ⟨23487296674647455727693745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31316395566196607636924993 23487296674647455727693745)
            ·
              refine ⟨17615472505985591795770309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23487296674647455727693745 17615472505985591795770309)
              ·
                refine ⟨3302901094872298461706933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17615472505985591795770309 3302901094872298461706933)
                ·
                  refine ⟨309646977644277980785025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3302901094872298461706933 309646977644277980785025)
                  ·
                    rfl

theorem cell23_5427318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_5427318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427318 prefixEnd_5427318 := by exact prefixLift 5427318
  have htrace : WordTrace (prefixWord ++ tailWord_5427318) baseStart_5427318 baseEnd_5427318 := by
    simpa [prefixWord, tailWord_5427318, baseEnd_5427318] using wordTrace_append hprefix tailTrace_5427318
  have hstable : (prefixWord ++ tailWord_5427318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427318).length < 2 ^ (prefixWord ++ tailWord_5427318).sum := by decide
  have hdescent : baseEnd_5427318 < baseStart_5427318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427380 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5427380 : Nat := 118140960795 + 5427380 * 2 ^ 59
def prefixEnd_5427380 : Nat := 4983230072969 + 3 ^ 40 * 5427380 * 2
def baseEnd_5427380 : Nat := 2786854634599080584489941

theorem tailTrace_5427380 : CollatzResearch.WordTrace tailWord_5427380 prefixEnd_5427380 2786854634599080584489941 := by
  unfold tailWord_5427380
  simp only [CollatzResearch.WordTrace]
  refine ⟨98976405538768328776511797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131968540718357771702015729 98976405538768328776511797)
  ·
    refine ⟨9279038019259530822797981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98976405538768328776511797 9279038019259530822797981)
    ·
      refine ⟨3479639257222324058549243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9279038019259530822797981 3479639257222324058549243)
      ·
        refine ⟨5219458885833486087823865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479639257222324058549243 5219458885833486087823865)
        ·
          refine ⟨3914594164375114565867899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219458885833486087823865 3914594164375114565867899)
          ·
            refine ⟨5871891246562671848801849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914594164375114565867899 5871891246562671848801849)
            ·
              refine ⟨4403918434922003886601387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871891246562671848801849 4403918434922003886601387)
              ·
                refine ⟨6605877652383005829902081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403918434922003886601387 6605877652383005829902081)
                ·
                  refine ⟨4954408239287254372426561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6605877652383005829902081 4954408239287254372426561)
                  ·
                    refine ⟨3715806179465440779319921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4954408239287254372426561 3715806179465440779319921)
                    ·
                      refine ⟨2786854634599080584489941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715806179465440779319921 2786854634599080584489941)
                      ·
                        rfl

theorem cell23_5427380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5427380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427380 prefixEnd_5427380 := by exact prefixLift 5427380
  have htrace : WordTrace (prefixWord ++ tailWord_5427380) baseStart_5427380 baseEnd_5427380 := by
    simpa [prefixWord, tailWord_5427380, baseEnd_5427380] using wordTrace_append hprefix tailTrace_5427380
  have hstable : (prefixWord ++ tailWord_5427380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427380).length < 2 ^ (prefixWord ++ tailWord_5427380).sum := by decide
  have hdescent : baseEnd_5427380 < baseStart_5427380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427435 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 1, 1, 3]
def baseStart_5427435 : Nat := 118140960795 + 5427435 * 2 ^ 59
def prefixEnd_5427435 : Nat := 4983230072969 + 3 ^ 40 * 5427435 * 2
def baseEnd_5427435 : Nat := 2786882876035077869302187

theorem tailTrace_5427435 : CollatzResearch.WordTrace tailWord_5427435 prefixEnd_5427435 2786882876035077869302187 := by
  unfold tailWord_5427435
  simp only [CollatzResearch.WordTrace]
  refine ⟨197954817092337401946275759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131969878061558267964183839 197954817092337401946275759)
  ·
    refine ⟨296932225638506102919413639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197954817092337401946275759 296932225638506102919413639)
    ·
      refine ⟨445398338457759154379120459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296932225638506102919413639 445398338457759154379120459)
      ·
        refine ⟨668097507686638731568680689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445398338457759154379120459 668097507686638731568680689)
        ·
          refine ⟨501073130764979048676510517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668097507686638731568680689 501073130764979048676510517)
          ·
            refine ⟨46975606009216785813422861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 501073130764979048676510517 46975606009216785813422861)
            ·
              refine ⟨17615852253456294680033573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46975606009216785813422861 17615852253456294680033573)
              ·
                refine ⟨3302972297523055252506295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17615852253456294680033573 3302972297523055252506295)
                ·
                  refine ⟨4954458446284582878759443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302972297523055252506295 4954458446284582878759443)
                  ·
                    refine ⟨7431687669426874318139165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954458446284582878759443 7431687669426874318139165)
                    ·
                      refine ⟨2786882876035077869302187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7431687669426874318139165 2786882876035077869302187)
                      ·
                        rfl

theorem cell23_5427435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 1, 3].length) (baseStart_5427435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427435 prefixEnd_5427435 := by exact prefixLift 5427435
  have htrace : WordTrace (prefixWord ++ tailWord_5427435) baseStart_5427435 baseEnd_5427435 := by
    simpa [prefixWord, tailWord_5427435, baseEnd_5427435] using wordTrace_append hprefix tailTrace_5427435
  have hstable : (prefixWord ++ tailWord_5427435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427435).length < 2 ^ (prefixWord ++ tailWord_5427435).sum := by decide
  have hdescent : baseEnd_5427435 < baseStart_5427435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427441 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_5427441 : Nat := 118140960795 + 5427441 * 2 ^ 59
def prefixEnd_5427441 : Nat := 4983230072969 + 3 ^ 40 * 5427441 * 2
def baseEnd_5427441 : Nat := 2786885956919004845827159

theorem tailTrace_5427441 : CollatzResearch.WordTrace tailWord_5427441 prefixEnd_5427441 2786885956919004845827159 := by
  unfold tailWord_5427441
  simp only [CollatzResearch.WordTrace]
  refine ⟨197955035930315664970994177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131970023953543776647329451 197955035930315664970994177)
  ·
    refine ⟨148466276947736748728245633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197955035930315664970994177 148466276947736748728245633)
    ·
      refine ⟨111349707710802561546184225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148466276947736748728245633 111349707710802561546184225)
      ·
        refine ⟨83512280783101921159638169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111349707710802561546184225 83512280783101921159638169)
        ·
          refine ⟨62634210587326440869728627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83512280783101921159638169 62634210587326440869728627)
          ·
            refine ⟨93951315880989661304592941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62634210587326440869728627 93951315880989661304592941)
            ·
              refine ⟨35231743455371122989222353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93951315880989661304592941 35231743455371122989222353)
              ·
                refine ⟨26423807591528342241916765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35231743455371122989222353 26423807591528342241916765)
                ·
                  refine ⟨9908927846823128340718787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26423807591528342241916765 9908927846823128340718787)
                  ·
                    refine ⟨14863391770234692511078181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9908927846823128340718787 14863391770234692511078181)
                    ·
                      refine ⟨2786885956919004845827159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14863391770234692511078181 2786885956919004845827159)
                      ·
                        rfl

theorem cell23_5427441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_5427441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427441 prefixEnd_5427441 := by exact prefixLift 5427441
  have htrace : WordTrace (prefixWord ++ tailWord_5427441) baseStart_5427441 baseEnd_5427441 := by
    simpa [prefixWord, tailWord_5427441, baseEnd_5427441] using wordTrace_append hprefix tailTrace_5427441
  have hstable : (prefixWord ++ tailWord_5427441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427441).length < 2 ^ (prefixWord ++ tailWord_5427441).sum := by decide
  have hdescent : baseEnd_5427441 < baseStart_5427441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427485 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_5427485 : Nat := 118140960795 + 5427485 * 2 ^ 59
def prefixEnd_5427485 : Nat := 4983230072969 + 3 ^ 40 * 5427485 * 2
def baseEnd_5427485 : Nat := 928969516689267557892319

theorem tailTrace_5427485 : CollatzResearch.WordTrace tailWord_5427485 prefixEnd_5427485 928969516689267557892319 := by
  unfold tailWord_5427485
  simp only [CollatzResearch.WordTrace]
  refine ⟨197956640742156260485595909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131971093828104173657063939 197956640742156260485595909)
  ·
    refine ⟨37116870139154298841049233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197956640742156260485595909 37116870139154298841049233)
    ·
      refine ⟨27837652604365724130786925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37116870139154298841049233 27837652604365724130786925)
      ·
        refine ⟨10439119726637146549045097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27837652604365724130786925 10439119726637146549045097)
        ·
          refine ⟨7829339794977859911783823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10439119726637146549045097 7829339794977859911783823)
          ·
            refine ⟨11744009692466789867675735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829339794977859911783823 11744009692466789867675735)
            ·
              refine ⟨17616014538700184801513603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11744009692466789867675735 17616014538700184801513603)
              ·
                refine ⟨26424021808050277202270405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17616014538700184801513603 26424021808050277202270405)
                ·
                  refine ⟨4954504089009426975425701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26424021808050277202270405 4954504089009426975425701)
                  ·
                    refine ⟨928969516689267557892319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954504089009426975425701 928969516689267557892319)
                    ·
                      rfl

theorem cell23_5427485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_5427485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427485 prefixEnd_5427485 := by exact prefixLift 5427485
  have htrace : WordTrace (prefixWord ++ tailWord_5427485) baseStart_5427485 baseEnd_5427485 := by
    simpa [prefixWord, tailWord_5427485, baseEnd_5427485] using wordTrace_append hprefix tailTrace_5427485
  have hstable : (prefixWord ++ tailWord_5427485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427485).length < 2 ^ (prefixWord ++ tailWord_5427485).sum := by decide
  have hdescent : baseEnd_5427485 < baseStart_5427485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427492 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_5427492 : Nat := 118140960795 + 5427492 * 2 ^ 59
def prefixEnd_5427492 : Nat := 4983230072969 + 3 ^ 40 * 5427492 * 2
def baseEnd_5427492 : Nat := 2786912144432384146289425

theorem tailTrace_5427492 : CollatzResearch.WordTrace tailWord_5427492 prefixEnd_5427492 2786912144432384146289425 := by
  unfold tailWord_5427492
  simp only [CollatzResearch.WordTrace]
  refine ⟨98978448026565450340550365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131971264035420600454067153 98978448026565450340550365)
  ·
    refine ⟨37116918009962043877706387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98978448026565450340550365 37116918009962043877706387)
    ·
      refine ⟨55675377014943065816559581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37116918009962043877706387 55675377014943065816559581)
      ·
        refine ⟨20878266380603649681209843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55675377014943065816559581 20878266380603649681209843)
        ·
          refine ⟨31317399570905474521814765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20878266380603649681209843 31317399570905474521814765)
          ·
            refine ⟨11744024839089552945680537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31317399570905474521814765 11744024839089552945680537)
            ·
              refine ⟨8808018629317164709260403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11744024839089552945680537 8808018629317164709260403)
              ·
                refine ⟨13212027943975747063890605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8808018629317164709260403 13212027943975747063890605)
                ·
                  refine ⟨4954510478990905148958977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13212027943975747063890605 4954510478990905148958977)
                  ·
                    refine ⟨3715882859243178861719233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4954510478990905148958977 3715882859243178861719233)
                    ·
                      refine ⟨2786912144432384146289425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715882859243178861719233 2786912144432384146289425)
                      ·
                        rfl

theorem cell23_5427492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_5427492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427492 prefixEnd_5427492 := by exact prefixLift 5427492
  have htrace : WordTrace (prefixWord ++ tailWord_5427492) baseStart_5427492 baseEnd_5427492 := by
    simpa [prefixWord, tailWord_5427492, baseEnd_5427492] using wordTrace_append hprefix tailTrace_5427492
  have hstable : (prefixWord ++ tailWord_5427492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427492).length < 2 ^ (prefixWord ++ tailWord_5427492).sum := by decide
  have hdescent : baseEnd_5427492 < baseStart_5427492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427502 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5427502 : Nat := 118140960795 + 5427502 * 2 ^ 59
def prefixEnd_5427502 : Nat := 4983230072969 + 3 ^ 40 * 5427502 * 2
def baseEnd_5427502 : Nat := 928972426412976369054793

theorem tailTrace_5427502 : CollatzResearch.WordTrace tailWord_5427502 prefixEnd_5427502 928972426412976369054793 := by
  unfold tailWord_5427502
  simp only [CollatzResearch.WordTrace]
  refine ⟨24744657597886834048620595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131971507188729781592643173 24744657597886834048620595)
  ·
    refine ⟨37116986396830251072930893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24744657597886834048620595 37116986396830251072930893)
    ·
      refine ⟨13918869898811344152349085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37116986396830251072930893 13918869898811344152349085)
      ·
        refine ⟨5219576212054254057130907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13918869898811344152349085 5219576212054254057130907)
        ·
          refine ⟨7829364318081381085696361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219576212054254057130907 7829364318081381085696361)
          ·
            refine ⟨5872023238561035814272271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7829364318081381085696361 5872023238561035814272271)
            ·
              refine ⟨8808034857841553721408407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872023238561035814272271 8808034857841553721408407)
              ·
                refine ⟨13212052286762330582112611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8808034857841553721408407 13212052286762330582112611)
                ·
                  refine ⟨19818078430143495873168917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13212052286762330582112611 19818078430143495873168917)
                  ·
                    refine ⟨928972426412976369054793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19818078430143495873168917 928972426412976369054793)
                    ·
                      rfl

theorem cell23_5427502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5427502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427502 prefixEnd_5427502 := by exact prefixLift 5427502
  have htrace : WordTrace (prefixWord ++ tailWord_5427502) baseStart_5427502 baseEnd_5427502 := by
    simpa [prefixWord, tailWord_5427502, baseEnd_5427502] using wordTrace_append hprefix tailTrace_5427502
  have hstable : (prefixWord ++ tailWord_5427502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427502).length < 2 ^ (prefixWord ++ tailWord_5427502).sum := by decide
  have hdescent : baseEnd_5427502 < baseStart_5427502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427505 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_5427505 : Nat := 118140960795 + 5427505 * 2 ^ 59
def prefixEnd_5427505 : Nat := 4983230072969 + 3 ^ 40 * 5427505 * 2
def baseEnd_5427505 : Nat := 2786918819680892595426865

theorem tailTrace_5427505 : CollatzResearch.WordTrace tailWord_5427505 prefixEnd_5427505 2786918819680892595426865 := by
  unfold tailWord_5427505
  simp only [CollatzResearch.WordTrace]
  refine ⟨197957370202083803901323969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131971580134722535934215979 197957370202083803901323969)
  ·
    refine ⟨148468027651562852925992977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197957370202083803901323969 148468027651562852925992977)
    ·
      refine ⟨111351020738672139694494733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148468027651562852925992977 111351020738672139694494733)
      ·
        refine ⟨41756632777002052385435525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111351020738672139694494733 41756632777002052385435525)
        ·
          refine ⟨7829368645687884822269161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41756632777002052385435525 7829368645687884822269161)
          ·
            refine ⟨5872026484265913616701871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7829368645687884822269161 5872026484265913616701871)
            ·
              refine ⟨8808039726398870425052807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872026484265913616701871 8808039726398870425052807)
              ·
                refine ⟨13212059589598305637579211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8808039726398870425052807 13212059589598305637579211)
                ·
                  refine ⟨19818089384397458456368817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13212059589598305637579211 19818089384397458456368817)
                  ·
                    refine ⟨14863567038298093842276613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19818089384397458456368817 14863567038298093842276613)
                    ·
                      refine ⟨2786918819680892595426865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14863567038298093842276613 2786918819680892595426865)
                      ·
                        rfl

theorem cell23_5427505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_5427505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427505 prefixEnd_5427505 := by exact prefixLift 5427505
  have htrace : WordTrace (prefixWord ++ tailWord_5427505) baseStart_5427505 baseEnd_5427505 := by
    simpa [prefixWord, tailWord_5427505, baseEnd_5427505] using wordTrace_append hprefix tailTrace_5427505
  have hstable : (prefixWord ++ tailWord_5427505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427505).length < 2 ^ (prefixWord ++ tailWord_5427505).sum := by decide
  have hdescent : baseEnd_5427505 < baseStart_5427505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427559 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_5427559 : Nat := 118140960795 + 5427559 * 2 ^ 59
def prefixEnd_5427559 : Nat := 4983230072969 + 3 ^ 40 * 5427559 * 2
def baseEnd_5427559 : Nat := 2786946547636235384151617

theorem tailTrace_5427559 : CollatzResearch.WordTrace tailWord_5427559 prefixEnd_5427559 2786946547636235384151617 := by
  unfold tailWord_5427559
  simp only [CollatzResearch.WordTrace]
  refine ⟨197959339743888171123789731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131972893162592114082526487 197959339743888171123789731)
  ·
    refine ⟨296939009615832256685684597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197959339743888171123789731 296939009615832256685684597)
    ·
      refine ⟨27838032151484274064282931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296939009615832256685684597 27838032151484274064282931)
      ·
        refine ⟨41757048227226411096424397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27838032151484274064282931 41757048227226411096424397)
        ·
          refine ⟨15658893085209904161159149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41757048227226411096424397 15658893085209904161159149)
          ·
            refine ⟨5872084906953714060434681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15658893085209904161159149 5872084906953714060434681)
            ·
              refine ⟨4404063680215285545326011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872084906953714060434681 4404063680215285545326011)
              ·
                refine ⟨6606095520322928317989017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404063680215285545326011 6606095520322928317989017)
                ·
                  refine ⟨4954571640242196238491763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6606095520322928317989017 4954571640242196238491763)
                  ·
                    refine ⟨7431857460363294357737645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954571640242196238491763 7431857460363294357737645)
                    ·
                      refine ⟨2786946547636235384151617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7431857460363294357737645 2786946547636235384151617)
                      ·
                        rfl

theorem cell23_5427559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_5427559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427559 prefixEnd_5427559 := by exact prefixLift 5427559
  have htrace : WordTrace (prefixWord ++ tailWord_5427559) baseStart_5427559 baseEnd_5427559 := by
    simpa [prefixWord, tailWord_5427559, baseEnd_5427559] using wordTrace_append hprefix tailTrace_5427559
  have hstable : (prefixWord ++ tailWord_5427559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427559).length < 2 ^ (prefixWord ++ tailWord_5427559).sum := by decide
  have hdescent : baseEnd_5427559 < baseStart_5427559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427561 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_5427561 : Nat := 118140960795 + 5427561 * 2 ^ 59
def prefixEnd_5427561 : Nat := 4983230072969 + 3 ^ 40 * 5427561 * 2
def baseEnd_5427561 : Nat := 2786947574597544376326607

theorem tailTrace_5427561 : CollatzResearch.WordTrace tailWord_5427561 prefixEnd_5427561 2786947574597544376326607 := by
  unfold tailWord_5427561
  simp only [CollatzResearch.WordTrace]
  refine ⟨197959412689880925465362537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131972941793253950310241691 197959412689880925465362537)
  ·
    refine ⟨148469559517410694099021903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197959412689880925465362537 148469559517410694099021903)
    ·
      refine ⟨222704339276116041148532855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148469559517410694099021903 222704339276116041148532855)
      ·
        refine ⟨334056508914174061722799283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222704339276116041148532855 334056508914174061722799283)
        ·
          refine ⟨501084763371261092584198925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334056508914174061722799283 501084763371261092584198925)
          ·
            refine ⟨187906786264222909719074597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501084763371261092584198925 187906786264222909719074597)
            ·
              refine ⟨35232522424541795572326487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187906786264222909719074597 35232522424541795572326487)
              ·
                refine ⟨52848783636812693358489731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35232522424541795572326487 52848783636812693358489731)
                ·
                  refine ⟨79273175455219040037734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52848783636812693358489731 79273175455219040037734597)
                  ·
                    refine ⟨14863720397853570007075237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79273175455219040037734597 14863720397853570007075237)
                    ·
                      refine ⟨2786947574597544376326607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14863720397853570007075237 2786947574597544376326607)
                      ·
                        rfl

theorem cell23_5427561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_5427561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427561 prefixEnd_5427561 := by exact prefixLift 5427561
  have htrace : WordTrace (prefixWord ++ tailWord_5427561) baseStart_5427561 baseEnd_5427561 := by
    simpa [prefixWord, tailWord_5427561, baseEnd_5427561] using wordTrace_append hprefix tailTrace_5427561
  have hstable : (prefixWord ++ tailWord_5427561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427561).length < 2 ^ (prefixWord ++ tailWord_5427561).sum := by decide
  have hdescent : baseEnd_5427561 < baseStart_5427561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427565 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_5427565 : Nat := 118140960795 + 5427565 * 2 ^ 59
def prefixEnd_5427565 : Nat := 4983230072969 + 3 ^ 40 * 5427565 * 2
def baseEnd_5427565 : Nat := 2786949628520162360676589

theorem tailTrace_5427565 : CollatzResearch.WordTrace tailWord_5427565 prefixEnd_5427565 2786949628520162360676589 := by
  unfold tailWord_5427565
  simp only [CollatzResearch.WordTrace]
  refine ⟨197959558581866434148508149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131973039054577622765672099 197959558581866434148508149)
  ·
    refine ⟨18558708617049978201422639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197959558581866434148508149 18558708617049978201422639)
    ·
      refine ⟨27838062925574967302133959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18558708617049978201422639 27838062925574967302133959)
      ·
        refine ⟨41757094388362450953200939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27838062925574967302133959 41757094388362450953200939)
        ·
          refine ⟨62635641582543676429801409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41757094388362450953200939 62635641582543676429801409)
          ·
            refine ⟨46976731186907757322351057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62635641582543676429801409 46976731186907757322351057)
            ·
              refine ⟨35232548390180817991763293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46976731186907757322351057 35232548390180817991763293)
              ·
                refine ⟨13212205646317806746911235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35232548390180817991763293 13212205646317806746911235)
                ·
                  refine ⟨19818308469476710120366853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13212205646317806746911235 19818308469476710120366853)
                  ·
                    refine ⟨3715932838026883147568785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19818308469476710120366853 3715932838026883147568785)
                    ·
                      refine ⟨2786949628520162360676589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715932838026883147568785 2786949628520162360676589)
                      ·
                        rfl

theorem cell23_5427565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_5427565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427565 prefixEnd_5427565 := by exact prefixLift 5427565
  have htrace : WordTrace (prefixWord ++ tailWord_5427565) baseStart_5427565 baseEnd_5427565 := by
    simpa [prefixWord, tailWord_5427565, baseEnd_5427565] using wordTrace_append hprefix tailTrace_5427565
  have hstable : (prefixWord ++ tailWord_5427565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427565).length < 2 ^ (prefixWord ++ tailWord_5427565).sum := by decide
  have hdescent : baseEnd_5427565 < baseStart_5427565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427618 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5427618 : Nat := 118140960795 + 5427618 * 2 ^ 59
def prefixEnd_5427618 : Nat := 4983230072969 + 3 ^ 40 * 5427618 * 2
def baseEnd_5427618 : Nat := 928992280998283551104615

theorem tailTrace_5427618 : CollatzResearch.WordTrace tailWord_5427618 prefixEnd_5427618 928992280998283551104615 := by
  unfold tailWord_5427618
  simp only [CollatzResearch.WordTrace]
  refine ⟨49490372912668606050046877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131974327767116282800125005 49490372912668606050046877)
  ·
    refine ⟨18558889842250727268767579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49490372912668606050046877 18558889842250727268767579)
    ·
      refine ⟨27838334763376090903151369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18558889842250727268767579 27838334763376090903151369)
      ·
        refine ⟨20878751072532068177363527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27838334763376090903151369 20878751072532068177363527)
        ·
          refine ⟨31318126608798102266045291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20878751072532068177363527 31318126608798102266045291)
          ·
            refine ⟨46977189913197153399067937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31318126608798102266045291 46977189913197153399067937)
            ·
              refine ⟨35232892434897865049300953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46977189913197153399067937 35232892434897865049300953)
              ·
                refine ⟨26424669326173398786975715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35232892434897865049300953 26424669326173398786975715)
                ·
                  refine ⟨39637003989260098180463573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26424669326173398786975715 39637003989260098180463573)
                  ·
                    refine ⟨928992280998283551104615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39637003989260098180463573 928992280998283551104615)
                    ·
                      rfl

theorem cell23_5427618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5427618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427618 prefixEnd_5427618 := by exact prefixLift 5427618
  have htrace : WordTrace (prefixWord ++ tailWord_5427618) baseStart_5427618 baseEnd_5427618 := by
    simpa [prefixWord, tailWord_5427618, baseEnd_5427618] using wordTrace_append hprefix tailTrace_5427618
  have hstable : (prefixWord ++ tailWord_5427618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427618).length < 2 ^ (prefixWord ++ tailWord_5427618).sum := by decide
  have hdescent : baseEnd_5427618 < baseStart_5427618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427648 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 7, 4]
def baseStart_5427648 : Nat := 118140960795 + 5427648 * 2 ^ 59
def prefixEnd_5427648 : Nat := 4983230072969 + 3 ^ 40 * 5427648 * 2
def baseEnd_5427648 : Nat := 928997415804828511979569

theorem tailTrace_5427648 : CollatzResearch.WordTrace tailWord_5427648 prefixEnd_5427648 928997415804828511979569 := by
  unfold tailWord_5427648
  simp only [CollatzResearch.WordTrace]
  refine ⟨98981292920282869661889799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131975057227043826215853065 98981292920282869661889799)
  ·
    refine ⟨148471939380424304492834699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98981292920282869661889799 148471939380424304492834699)
    ·
      refine ⟨222707909070636456739252049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148471939380424304492834699 222707909070636456739252049)
      ·
        refine ⟨167030931802977342554439037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222707909070636456739252049 167030931802977342554439037)
        ·
          refine ⟨62636599426116503457914639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167030931802977342554439037 62636599426116503457914639)
          ·
            refine ⟨93954899139174755186871959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62636599426116503457914639 93954899139174755186871959)
            ·
              refine ⟨140932348708762132780307939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93954899139174755186871959 140932348708762132780307939)
              ·
                refine ⟨211398523063143199170461909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140932348708762132780307939 211398523063143199170461909)
                ·
                  refine ⟨4954652884292418730557701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 211398523063143199170461909 4954652884292418730557701)
                  ·
                    refine ⟨928997415804828511979569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954652884292418730557701 928997415804828511979569)
                    ·
                      rfl

theorem cell23_5427648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_5427648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427648 prefixEnd_5427648 := by exact prefixLift 5427648
  have htrace : WordTrace (prefixWord ++ tailWord_5427648) baseStart_5427648 baseEnd_5427648 := by
    simpa [prefixWord, tailWord_5427648, baseEnd_5427648] using wordTrace_append hprefix tailTrace_5427648
  have hstable : (prefixWord ++ tailWord_5427648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427648).length < 2 ^ (prefixWord ++ tailWord_5427648).sum := by decide
  have hdescent : baseEnd_5427648 < baseStart_5427648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427655 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_5427655 : Nat := 118140960795 + 5427655 * 2 ^ 59
def prefixEnd_5427655 : Nat := 4983230072969 + 3 ^ 40 * 5427655 * 2
def baseEnd_5427655 : Nat := 2786995841779067008551175

theorem tailTrace_5427655 : CollatzResearch.WordTrace tailWord_5427655 prefixEnd_5427655 2786995841779067008551175 := by
  unfold tailWord_5427655
  simp only [CollatzResearch.WordTrace]
  refine ⟨197962841151540379519284419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131975227434360253012856279 197962841151540379519284419)
  ·
    refine ⟨296944261727310569278926629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197962841151540379519284419 296944261727310569278926629)
    ·
      refine ⟨55677049073870731739798743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296944261727310569278926629 55677049073870731739798743)
      ·
        refine ⟨83515573610806097609698115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55677049073870731739798743 83515573610806097609698115)
        ·
          refine ⟨125273360416209146414547173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83515573610806097609698115 125273360416209146414547173)
          ·
            refine ⟨23488755078039214952727595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125273360416209146414547173 23488755078039214952727595)
            ·
              refine ⟨35233132617058822429091393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23488755078039214952727595 35233132617058822429091393)
              ·
                refine ⟨26424849462794116821818545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35233132617058822429091393 26424849462794116821818545)
                ·
                  refine ⟨19818637097095587616363909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26424849462794116821818545 19818637097095587616363909)
                  ·
                    refine ⟨3715994455705422678068233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19818637097095587616363909 3715994455705422678068233)
                    ·
                      refine ⟨2786995841779067008551175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3715994455705422678068233 2786995841779067008551175)
                      ·
                        rfl

theorem cell23_5427655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_5427655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427655 prefixEnd_5427655 := by exact prefixLift 5427655
  have htrace : WordTrace (prefixWord ++ tailWord_5427655) baseStart_5427655 baseEnd_5427655 := by
    simpa [prefixWord, tailWord_5427655, baseEnd_5427655] using wordTrace_append hprefix tailTrace_5427655
  have hstable : (prefixWord ++ tailWord_5427655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427655).length < 2 ^ (prefixWord ++ tailWord_5427655).sum := by decide
  have hdescent : baseEnd_5427655 < baseStart_5427655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427705 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 3]
def baseStart_5427705 : Nat := 118140960795 + 5427705 * 2 ^ 59
def prefixEnd_5427705 : Nat := 4983230072969 + 3 ^ 40 * 5427705 * 2
def baseEnd_5427705 : Nat := 2787021515811791812925945

theorem tailTrace_5427705 : CollatzResearch.WordTrace tailWord_5427705 prefixEnd_5427705 2787021515811791812925945 := by
  unfold tailWord_5427705
  simp only [CollatzResearch.WordTrace]
  refine ⟨197964664801359238058604569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131976443200906158705736379 197964664801359238058604569)
  ·
    refine ⟨148473498601019428543953427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197964664801359238058604569 148473498601019428543953427)
    ·
      refine ⟨222710247901529142815930141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148473498601019428543953427 222710247901529142815930141)
      ·
        refine ⟨83516342963073428555973803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222710247901529142815930141 83516342963073428555973803)
        ·
          refine ⟨125274514444610142833960705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83516342963073428555973803 125274514444610142833960705)
          ·
            refine ⟨93955885833457607125470529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125274514444610142833960705 93955885833457607125470529)
            ·
              refine ⟨70466914375093205344102897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93955885833457607125470529 70466914375093205344102897)
              ·
                refine ⟨52850185781319904008077173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70466914375093205344102897 52850185781319904008077173)
                ·
                  refine ⟨4954704916998741000757235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52850185781319904008077173 4954704916998741000757235)
                  ·
                    refine ⟨7432057375498111501135853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954704916998741000757235 7432057375498111501135853)
                    ·
                      refine ⟨2787021515811791812925945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432057375498111501135853 2787021515811791812925945)
                      ·
                        rfl

theorem cell23_5427705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_5427705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427705 prefixEnd_5427705 := by exact prefixLift 5427705
  have htrace : WordTrace (prefixWord ++ tailWord_5427705) baseStart_5427705 baseEnd_5427705 := by
    simpa [prefixWord, tailWord_5427705, baseEnd_5427705] using wordTrace_append hprefix tailTrace_5427705
  have hstable : (prefixWord ++ tailWord_5427705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427705).length < 2 ^ (prefixWord ++ tailWord_5427705).sum := by decide
  have hdescent : baseEnd_5427705 < baseStart_5427705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427708 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_5427708 : Nat := 118140960795 + 5427708 * 2 ^ 59
def prefixEnd_5427708 : Nat := 4983230072969 + 3 ^ 40 * 5427708 * 2
def baseEnd_5427708 : Nat := 929007685417918433729477

theorem tailTrace_5427708 : CollatzResearch.WordTrace tailWord_5427708 prefixEnd_5427708 929007685417918433729477 := by
  unfold tailWord_5427708
  simp only [CollatzResearch.WordTrace]
  refine ⟨98982387110174184785481889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131976516146898913047309185 98982387110174184785481889)
  ·
    refine ⟨74236790332630638589111417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98982387110174184785481889 74236790332630638589111417)
    ·
      refine ⟨55677592749472978941833563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74236790332630638589111417 55677592749472978941833563)
      ·
        refine ⟨83516389124209468412750345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55677592749472978941833563 83516389124209468412750345)
        ·
          refine ⟨62637291843157101309562759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83516389124209468412750345 62637291843157101309562759)
          ·
            refine ⟨93955937764735651964344139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62637291843157101309562759 93955937764735651964344139)
            ·
              refine ⟨140933906647103477946516209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93955937764735651964344139 140933906647103477946516209)
              ·
                refine ⟨105700429985327608459887157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140933906647103477946516209 105700429985327608459887157)
                ·
                  refine ⟨9909415311124463293114421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105700429985327608459887157 9909415311124463293114421)
                  ·
                    refine ⟨929007685417918433729477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9909415311124463293114421 929007685417918433729477)
                    ·
                      rfl

theorem cell23_5427708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_5427708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427708 prefixEnd_5427708 := by exact prefixLift 5427708
  have htrace : WordTrace (prefixWord ++ tailWord_5427708) baseStart_5427708 baseEnd_5427708 := by
    simpa [prefixWord, tailWord_5427708, baseEnd_5427708] using wordTrace_append hprefix tailTrace_5427708
  have hstable : (prefixWord ++ tailWord_5427708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427708).length < 2 ^ (prefixWord ++ tailWord_5427708).sum := by decide
  have hdescent : baseEnd_5427708 < baseStart_5427708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427716 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_5427716 : Nat := 118140960795 + 5427716 * 2 ^ 59
def prefixEnd_5427716 : Nat := 4983230072969 + 3 ^ 40 * 5427716 * 2
def baseEnd_5427716 : Nat := 929009054699663756629465

theorem tailTrace_5427716 : CollatzResearch.WordTrace tailWord_5427716 prefixEnd_5427716 929009054699663756629465 := by
  unfold tailWord_5427716
  simp only [CollatzResearch.WordTrace]
  refine ⟨98982533002159693468627501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131976710669546257958170001 98982533002159693468627501)
  ·
    refine ⟨37118449875809885050735313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98982533002159693468627501 37118449875809885050735313)
    ·
      refine ⟨27838837406857413788051485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37118449875809885050735313 27838837406857413788051485)
      ·
        refine ⟨10439564027571530170519307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27838837406857413788051485 10439564027571530170519307)
        ·
          refine ⟨15659346041357295255778961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10439564027571530170519307 15659346041357295255778961)
          ·
            refine ⟨11744509531017971441834221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15659346041357295255778961 11744509531017971441834221)
            ·
              refine ⟨4404191074131739290687833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11744509531017971441834221 4404191074131739290687833)
              ·
                refine ⟨3303143305598804468015875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4404191074131739290687833 3303143305598804468015875)
                ·
                  refine ⟨4954714958398206702023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303143305598804468015875 4954714958398206702023813)
                  ·
                    refine ⟨929009054699663756629465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954714958398206702023813 929009054699663756629465)
                    ·
                      rfl

theorem cell23_5427716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_5427716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427716 prefixEnd_5427716 := by exact prefixLift 5427716
  have htrace : WordTrace (prefixWord ++ tailWord_5427716) baseStart_5427716 baseEnd_5427716 := by
    simpa [prefixWord, tailWord_5427716, baseEnd_5427716] using wordTrace_append hprefix tailTrace_5427716
  have hstable : (prefixWord ++ tailWord_5427716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427716).length < 2 ^ (prefixWord ++ tailWord_5427716).sum := by decide
  have hdescent : baseEnd_5427716 < baseStart_5427716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427745 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_5427745 : Nat := 118140960795 + 5427745 * 2 ^ 59
def prefixEnd_5427745 : Nat := 4983230072969 + 3 ^ 40 * 5427745 * 2
def baseEnd_5427745 : Nat := 2787042055037971656425761

theorem tailTrace_5427745 : CollatzResearch.WordTrace tailWord_5427745 prefixEnd_5427745 2787042055037971656425761 := by
  unfold tailWord_5427745
  simp only [CollatzResearch.WordTrace]
  refine ⟨197966123721214324890060689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131977415814142883260040459 197966123721214324890060689)
  ·
    refine ⟨148474592790910743667545517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197966123721214324890060689 148474592790910743667545517)
    ·
      refine ⟨55677972296591528875329569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148474592790910743667545517 55677972296591528875329569)
      ·
        refine ⟨41758479222443646656497177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55677972296591528875329569 41758479222443646656497177)
        ·
          refine ⟨31318859416832734992372883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41758479222443646656497177 31318859416832734992372883)
          ·
            refine ⟨46978289125249102488559325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31318859416832734992372883 46978289125249102488559325)
            ·
              refine ⟨17616858421968413433209747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46978289125249102488559325 17616858421968413433209747)
              ·
                refine ⟨26425287632952620149814621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17616858421968413433209747 26425287632952620149814621)
                ·
                  refine ⟨9909482862357232556180483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26425287632952620149814621 9909482862357232556180483)
                  ·
                    refine ⟨14864224293535848834270725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9909482862357232556180483 14864224293535848834270725)
                    ·
                      refine ⟨2787042055037971656425761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14864224293535848834270725 2787042055037971656425761)
                      ·
                        rfl

theorem cell23_5427745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_5427745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427745 prefixEnd_5427745 := by exact prefixLift 5427745
  have htrace : WordTrace (prefixWord ++ tailWord_5427745) baseStart_5427745 baseEnd_5427745 := by
    simpa [prefixWord, tailWord_5427745, baseEnd_5427745] using wordTrace_append hprefix tailTrace_5427745
  have hstable : (prefixWord ++ tailWord_5427745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427745).length < 2 ^ (prefixWord ++ tailWord_5427745).sum := by decide
  have hdescent : baseEnd_5427745 < baseStart_5427745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427772 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_5427772 : Nat := 118140960795 + 5427772 * 2 ^ 59
def prefixEnd_5427772 : Nat := 4983230072969 + 3 ^ 40 * 5427772 * 2
def baseEnd_5427772 : Nat := 929018639671881016929379

theorem tailTrace_5427772 : CollatzResearch.WordTrace tailWord_5427772 prefixEnd_5427772 929018639671881016929379 := by
  unfold tailWord_5427772
  simp only [CollatzResearch.WordTrace]
  refine ⟨98983554246058254250646785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131978072328077672334195713 98983554246058254250646785)
  ·
    refine ⟨74237665684543690687985089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98983554246058254250646785 74237665684543690687985089)
    ·
      refine ⟨55678249263407768015988817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74237665684543690687985089 55678249263407768015988817)
      ·
        refine ⟨41758686947555826011991613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55678249263407768015988817 41758686947555826011991613)
        ·
          refine ⟨15659507605333434754496855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41758686947555826011991613 15659507605333434754496855)
          ·
            refine ⟨23489261408000152131745283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15659507605333434754496855 23489261408000152131745283)
            ·
              refine ⟨35233892112000228197617925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23489261408000152131745283 35233892112000228197617925)
              ·
                refine ⟨6606354771000042787053361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35233892112000228197617925 6606354771000042787053361)
                ·
                  refine ⟨4954766078250032090290021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6606354771000042787053361 4954766078250032090290021)
                  ·
                    refine ⟨929018639671881016929379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954766078250032090290021 929018639671881016929379)
                    ·
                      rfl

theorem cell23_5427772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_5427772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427772 prefixEnd_5427772 := by exact prefixLift 5427772
  have htrace : WordTrace (prefixWord ++ tailWord_5427772) baseStart_5427772 baseEnd_5427772 := by
    simpa [prefixWord, tailWord_5427772, baseEnd_5427772] using wordTrace_append hprefix tailTrace_5427772
  have hstable : (prefixWord ++ tailWord_5427772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427772).length < 2 ^ (prefixWord ++ tailWord_5427772).sum := by decide
  have hdescent : baseEnd_5427772 < baseStart_5427772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427773 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_5427773 : Nat := 118140960795 + 5427773 * 2 ^ 59
def prefixEnd_5427773 : Nat := 4983230072969 + 3 ^ 40 * 5427773 * 2
def baseEnd_5427773 : Nat := 2787056432496297546875633

theorem tailTrace_5427773 : CollatzResearch.WordTrace tailWord_5427773 prefixEnd_5427773 2787056432496297546875633 := by
  unfold tailWord_5427773
  simp only [CollatzResearch.WordTrace]
  refine ⟨197967144965112885672079973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131978096643408590448053315 197967144965112885672079973)
  ·
    refine ⟨37118839680958666063514995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197967144965112885672079973 37118839680958666063514995)
    ·
      refine ⟨55678259521437999095272493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37118839680958666063514995 55678259521437999095272493)
      ·
        refine ⟨20879347320539249660727185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55678259521437999095272493 20879347320539249660727185)
        ·
          refine ⟨15659510490404437245545389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20879347320539249660727185 15659510490404437245545389)
          ·
            refine ⟨5872316433901663967079521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15659510490404437245545389 5872316433901663967079521)
            ·
              refine ⟨4404237325426247975309641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872316433901663967079521 4404237325426247975309641)
              ·
                refine ⟨3303177994069685981482231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4404237325426247975309641 3303177994069685981482231)
                ·
                  refine ⟨4954766991104528972223347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303177994069685981482231 4954766991104528972223347)
                  ·
                    refine ⟨7432150486656793458335021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954766991104528972223347 7432150486656793458335021)
                    ·
                      refine ⟨2787056432496297546875633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432150486656793458335021 2787056432496297546875633)
                      ·
                        rfl

theorem cell23_5427773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_5427773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427773 prefixEnd_5427773 := by exact prefixLift 5427773
  have htrace : WordTrace (prefixWord ++ tailWord_5427773) baseStart_5427773 baseEnd_5427773 := by
    simpa [prefixWord, tailWord_5427773, baseEnd_5427773] using wordTrace_append hprefix tailTrace_5427773
  have hstable : (prefixWord ++ tailWord_5427773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427773).length < 2 ^ (prefixWord ++ tailWord_5427773).sum := by decide
  have hdescent : baseEnd_5427773 < baseStart_5427773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427789 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5427789 : Nat := 118140960795 + 5427789 * 2 ^ 59
def prefixEnd_5427789 : Nat := 4983230072969 + 3 ^ 40 * 5427789 * 2
def baseEnd_5427789 : Nat := 929021549395589828091853

theorem tailTrace_5427789 : CollatzResearch.WordTrace tailWord_5427789 prefixEnd_5427789 929021549395589828091853 := by
  unfold tailWord_5427789
  simp only [CollatzResearch.WordTrace]
  refine ⟨197967728533054920404662421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131978485688703280269774947 197967728533054920404662421)
  ·
    refine ⟨9279737274986949393968551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197967728533054920404662421 9279737274986949393968551)
    ·
      refine ⟨13919605912480424090952827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9279737274986949393968551 13919605912480424090952827)
      ·
        refine ⟨20879408868720636136429241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13919605912480424090952827 20879408868720636136429241)
        ·
          refine ⟨15659556651540477102321931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20879408868720636136429241 15659556651540477102321931)
          ·
            refine ⟨23489334977310715653482897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15659556651540477102321931 23489334977310715653482897)
            ·
              refine ⟨17617001232983036740112173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23489334977310715653482897 17617001232983036740112173)
              ·
                refine ⟨6606375462368638777542065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17617001232983036740112173 6606375462368638777542065)
                ·
                  refine ⟨4954781596776479083156549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6606375462368638777542065 4954781596776479083156549)
                  ·
                    refine ⟨929021549395589828091853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954781596776479083156549 929021549395589828091853)
                    ·
                      rfl

theorem cell23_5427789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5427789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427789 prefixEnd_5427789 := by exact prefixLift 5427789
  have htrace : WordTrace (prefixWord ++ tailWord_5427789) baseStart_5427789 baseEnd_5427789 := by
    simpa [prefixWord, tailWord_5427789, baseEnd_5427789] using wordTrace_append hprefix tailTrace_5427789
  have hstable : (prefixWord ++ tailWord_5427789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427789).length < 2 ^ (prefixWord ++ tailWord_5427789).sum := by decide
  have hdescent : baseEnd_5427789 < baseStart_5427789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427812 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_5427812 : Nat := 118140960795 + 5427812 * 2 ^ 59
def prefixEnd_5427812 : Nat := 4983230072969 + 3 ^ 40 * 5427812 * 2
def baseEnd_5427812 : Nat := 2787076458241822894287953

theorem tailTrace_5427812 : CollatzResearch.WordTrace tailWord_5427812 prefixEnd_5427812 2787076458241822894287953 := by
  unfold tailWord_5427812
  simp only [CollatzResearch.WordTrace]
  refine ⟨98984283705985797666374845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131979044941314396888499793 98984283705985797666374845)
  ·
    refine ⟨37119106389744674124890567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98984283705985797666374845 37119106389744674124890567)
    ·
      refine ⟨55678659584617011187335851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37119106389744674124890567 55678659584617011187335851)
      ·
        refine ⟨83517989376925516781003777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55678659584617011187335851 83517989376925516781003777)
        ·
          refine ⟨62638492032694137585752833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83517989376925516781003777 62638492032694137585752833)
          ·
            refine ⟨46978869024520603189314625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62638492032694137585752833 46978869024520603189314625)
            ·
              refine ⟨35234151768390452391985969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46978869024520603189314625 35234151768390452391985969)
              ·
                refine ⟨26425613826292839293989477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35234151768390452391985969 26425613826292839293989477)
                ·
                  refine ⟨4954802592429907367623027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26425613826292839293989477 4954802592429907367623027)
                  ·
                    refine ⟨7432203888644861051434541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954802592429907367623027 7432203888644861051434541)
                    ·
                      refine ⟨2787076458241822894287953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432203888644861051434541 2787076458241822894287953)
                      ·
                        rfl

theorem cell23_5427812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_5427812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427812 prefixEnd_5427812 := by exact prefixLift 5427812
  have htrace : WordTrace (prefixWord ++ tailWord_5427812) baseStart_5427812 baseEnd_5427812 := by
    simpa [prefixWord, tailWord_5427812, baseEnd_5427812] using wordTrace_append hprefix tailTrace_5427812
  have hstable : (prefixWord ++ tailWord_5427812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427812).length < 2 ^ (prefixWord ++ tailWord_5427812).sum := by decide
  have hdescent : baseEnd_5427812 < baseStart_5427812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427813 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 1, 2, 2]
def baseStart_5427813 : Nat := 118140960795 + 5427813 * 2 ^ 59
def prefixEnd_5427813 : Nat := 4983230072969 + 3 ^ 40 * 5427813 * 2
def baseEnd_5427813 : Nat := 2787076971722477390375449

theorem tailTrace_5427813 : CollatzResearch.WordTrace tailWord_5427813 prefixEnd_5427813 2787076971722477390375449 := by
  unfold tailWord_5427813
  simp only [CollatzResearch.WordTrace]
  refine ⟨197968603884967972503536093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131979069256645315002357395 197968603884967972503536093)
  ·
    refine ⟨74238226456862989688826035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197968603884967972503536093 74238226456862989688826035)
    ·
      refine ⟨111357339685294484533239053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74238226456862989688826035 111357339685294484533239053)
      ·
        refine ⟨41759002381985431699964645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111357339685294484533239053 41759002381985431699964645)
        ·
          refine ⟨7829812946622268443743371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41759002381985431699964645 7829812946622268443743371)
          ·
            refine ⟨11744719419933402665615057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829812946622268443743371 11744719419933402665615057)
            ·
              refine ⟨8808539564950051999211293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11744719419933402665615057 8808539564950051999211293)
              ·
                refine ⟨3303202336856269499704235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8808539564950051999211293 3303202336856269499704235)
                ·
                  refine ⟨4954803505284404249556353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303202336856269499704235 4954803505284404249556353)
                  ·
                    refine ⟨3716102628963303187167265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4954803505284404249556353 3716102628963303187167265)
                    ·
                      refine ⟨2787076971722477390375449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716102628963303187167265 2787076971722477390375449)
                      ·
                        rfl

theorem cell23_5427813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_5427813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427813 prefixEnd_5427813 := by exact prefixLift 5427813
  have htrace : WordTrace (prefixWord ++ tailWord_5427813) baseStart_5427813 baseEnd_5427813 := by
    simpa [prefixWord, tailWord_5427813, baseEnd_5427813] using wordTrace_append hprefix tailTrace_5427813
  have hstable : (prefixWord ++ tailWord_5427813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427813).length < 2 ^ (prefixWord ++ tailWord_5427813).sum := by decide
  have hdescent : baseEnd_5427813 < baseStart_5427813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427845 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_5427845 : Nat := 118140960795 + 5427845 * 2 ^ 59
def prefixEnd_5427845 : Nat := 4983230072969 + 3 ^ 40 * 5427845 * 2
def baseEnd_5427845 : Nat := 929031134367807088391767

theorem tailTrace_5427845 : CollatzResearch.WordTrace tailWord_5427845 prefixEnd_5427845 929031134367807088391767 := by
  unfold tailWord_5427845
  simp only [CollatzResearch.WordTrace]
  refine ⟨197969771020852041968700989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131979847347234694645800659 197969771020852041968700989)
  ·
    refine ⟨74238664132819515738262871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197969771020852041968700989 74238664132819515738262871)
    ·
      refine ⟨111357996199229273607394307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74238664132819515738262871 111357996199229273607394307)
      ·
        refine ⟨167036994298843910411091461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111357996199229273607394307 167036994298843910411091461)
        ·
          refine ⟨31319436431033233202079649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167036994298843910411091461 31319436431033233202079649)
          ·
            refine ⟨23489577323274924901559737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31319436431033233202079649 23489577323274924901559737)
            ·
              refine ⟨17617182992456193676169803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23489577323274924901559737 17617182992456193676169803)
              ·
                refine ⟨26425774488684290514254705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17617182992456193676169803 26425774488684290514254705)
                ·
                  refine ⟨19819330866513217885691029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26425774488684290514254705 19819330866513217885691029)
                  ·
                    refine ⟨929031134367807088391767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19819330866513217885691029 929031134367807088391767)
                    ·
                      rfl

theorem cell23_5427845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_5427845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427845 prefixEnd_5427845 := by exact prefixLift 5427845
  have htrace : WordTrace (prefixWord ++ tailWord_5427845) baseStart_5427845 baseEnd_5427845 := by
    simpa [prefixWord, tailWord_5427845, baseEnd_5427845] using wordTrace_append hprefix tailTrace_5427845
  have hstable : (prefixWord ++ tailWord_5427845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427845).length < 2 ^ (prefixWord ++ tailWord_5427845).sum := by decide
  have hdescent : baseEnd_5427845 < baseStart_5427845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427852 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 1, 4, 2]
def baseStart_5427852 : Nat := 118140960795 + 5427852 * 2 ^ 59
def prefixEnd_5427852 : Nat := 4983230072969 + 3 ^ 40 * 5427852 * 2
def baseEnd_5427852 : Nat := 2787096997468002737787769

theorem tailTrace_5427852 : CollatzResearch.WordTrace tailWord_5427852 prefixEnd_5427852 2787096997468002737787769 := by
  unfold tailWord_5427852
  simp only [CollatzResearch.WordTrace]
  refine ⟨98985013165913341082102905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131980017554551121442803873 98985013165913341082102905)
  ·
    refine ⟨74238759874435005811577179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98985013165913341082102905 74238759874435005811577179)
    ·
      refine ⟨111358139811652508717365769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74238759874435005811577179 111358139811652508717365769)
      ·
        refine ⟨83518604858739381538024327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111358139811652508717365769 83518604858739381538024327)
        ·
          refine ⟨125277907288109072307036491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83518604858739381538024327 125277907288109072307036491)
          ·
            refine ⟨187916860932163608460554737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125277907288109072307036491 187916860932163608460554737)
            ·
              refine ⟨140937645699122706345416053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187916860932163608460554737 140937645699122706345416053)
              ·
                refine ⟨13212904284292753719882755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140937645699122706345416053 13212904284292753719882755)
                ·
                  refine ⟨19819356426439130579824133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13212904284292753719882755 19819356426439130579824133)
                  ·
                    refine ⟨3716129329957336983717025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19819356426439130579824133 3716129329957336983717025)
                    ·
                      refine ⟨2787096997468002737787769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716129329957336983717025 2787096997468002737787769)
                      ·
                        rfl

theorem cell23_5427852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_5427852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427852 prefixEnd_5427852 := by exact prefixLift 5427852
  have htrace : WordTrace (prefixWord ++ tailWord_5427852) baseStart_5427852 baseEnd_5427852 := by
    simpa [prefixWord, tailWord_5427852, baseEnd_5427852] using wordTrace_append hprefix tailTrace_5427852
  have hstable : (prefixWord ++ tailWord_5427852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427852).length < 2 ^ (prefixWord ++ tailWord_5427852).sum := by decide
  have hdescent : baseEnd_5427852 < baseStart_5427852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427869 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_5427869 : Nat := 118140960795 + 5427869 * 2 ^ 59
def prefixEnd_5427869 : Nat := 4983230072969 + 3 ^ 40 * 5427869 * 2
def baseEnd_5427869 : Nat := 2787105726639129171275191

theorem tailTrace_5427869 : CollatzResearch.WordTrace tailWord_5427869 prefixEnd_5427869 2787105726639129171275191 := by
  unfold tailWord_5427869
  simp only [CollatzResearch.WordTrace]
  refine ⟨197970646372765094067574661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131980430915176729378383107 197970646372765094067574661)
  ·
    refine ⟨37119496194893455137670249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197970646372765094067574661 37119496194893455137670249)
    ·
      refine ⟨27839622146170091353252687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37119496194893455137670249 27839622146170091353252687)
      ·
        refine ⟨41759433219255137029879031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27839622146170091353252687 41759433219255137029879031)
        ·
          refine ⟨62639149828882705544818547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41759433219255137029879031 62639149828882705544818547)
          ·
            refine ⟨93958724743324058317227821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62639149828882705544818547 93958724743324058317227821)
            ·
              refine ⟨35234521778746521868960433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93958724743324058317227821 35234521778746521868960433)
              ·
                refine ⟨26425891334059891401720325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35234521778746521868960433 26425891334059891401720325)
                ·
                  refine ⟨4954854625136229637822561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26425891334059891401720325 4954854625136229637822561)
                  ·
                    refine ⟨3716140968852172228366921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4954854625136229637822561 3716140968852172228366921)
                    ·
                      refine ⟨2787105726639129171275191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716140968852172228366921 2787105726639129171275191)
                      ·
                        rfl

theorem cell23_5427869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_5427869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427869 prefixEnd_5427869 := by exact prefixLift 5427869
  have htrace : WordTrace (prefixWord ++ tailWord_5427869) baseStart_5427869 baseEnd_5427869 := by
    simpa [prefixWord, tailWord_5427869, baseEnd_5427869] using wordTrace_append hprefix tailTrace_5427869
  have hstable : (prefixWord ++ tailWord_5427869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427869).length < 2 ^ (prefixWord ++ tailWord_5427869).sum := by decide
  have hdescent : baseEnd_5427869 < baseStart_5427869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427872 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_5427872 : Nat := 118140960795 + 5427872 * 2 ^ 59
def prefixEnd_5427872 : Nat := 4983230072969 + 3 ^ 40 * 5427872 * 2
def baseEnd_5427872 : Nat := 2787107267081092659537677

theorem tailTrace_5427872 : CollatzResearch.WordTrace tailWord_5427872 prefixEnd_5427872 2787107267081092659537677 := by
  unfold tailWord_5427872
  simp only [CollatzResearch.WordTrace]
  refine ⟨98985377895877112789966935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131980503861169483719955913 98985377895877112789966935)
  ·
    refine ⟨148478066843815669184950403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98985377895877112789966935 148478066843815669184950403)
    ·
      refine ⟨222717100265723503777425605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148478066843815669184950403 222717100265723503777425605)
      ·
        refine ⟨41759456299823156958267301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222717100265723503777425605 41759456299823156958267301)
        ·
          refine ⟨7829898056216841929675119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41759456299823156958267301 7829898056216841929675119)
          ·
            refine ⟨11744847084325262894512679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829898056216841929675119 11744847084325262894512679)
            ·
              refine ⟨17617270626487894341769019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11744847084325262894512679 17617270626487894341769019)
              ·
                refine ⟨26425905939731841512653529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17617270626487894341769019 26425905939731841512653529)
                ·
                  refine ⟨19819429454798881134490147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26425905939731841512653529 19819429454798881134490147)
                  ·
                    refine ⟨29729144182198321701735221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19819429454798881134490147 29729144182198321701735221)
                    ·
                      refine ⟨2787107267081092659537677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29729144182198321701735221 2787107267081092659537677)
                      ·
                        rfl

theorem cell23_5427872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_5427872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427872 prefixEnd_5427872 := by exact prefixLift 5427872
  have htrace : WordTrace (prefixWord ++ tailWord_5427872) baseStart_5427872 baseEnd_5427872 := by
    simpa [prefixWord, tailWord_5427872, baseEnd_5427872] using wordTrace_append hprefix tailTrace_5427872
  have hstable : (prefixWord ++ tailWord_5427872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427872).length < 2 ^ (prefixWord ++ tailWord_5427872).sum := by decide
  have hdescent : baseEnd_5427872 < baseStart_5427872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
