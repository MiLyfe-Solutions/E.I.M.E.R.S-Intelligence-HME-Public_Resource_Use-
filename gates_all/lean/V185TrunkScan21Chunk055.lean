import V185TrunkScan21Chunk054

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_665673 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_665673 : Nat := 118140960795 + 665673 * 2 ^ 59
def prefixEnd_665673 : Nat := 4983230072969 + 3 ^ 40 * 665673 * 2
def baseEnd_665673 : Nat := 151915647875768571122725

theorem tailTrace_665673 : CollatzResearch.WordTrace tailWord_665673 prefixEnd_665673 151915647875768571122725 := by
  unfold tailWord_665673
  simp only [CollatzResearch.WordTrace]
  refine ⟨24279088917387883742353673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16186059278258589161569115 24279088917387883742353673)
  ·
    refine ⟨18209316688040912806765255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24279088917387883742353673 18209316688040912806765255)
    ·
      refine ⟨27313975032061369210147883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18209316688040912806765255 27313975032061369210147883)
      ·
        refine ⟨40970962548092053815221825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27313975032061369210147883 40970962548092053815221825)
        ·
          refine ⟨30728221911069040361416369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40970962548092053815221825 30728221911069040361416369)
          ·
            refine ⟨23046166433301780271062277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30728221911069040361416369 23046166433301780271062277)
            ·
              refine ⟨4321156206244083800824177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23046166433301780271062277 4321156206244083800824177)
              ·
                refine ⟨3240867154683062850618133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321156206244083800824177 3240867154683062850618133)
                ·
                  refine ⟨151915647875768571122725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3240867154683062850618133 151915647875768571122725)
                  ·
                    rfl

theorem cell21_665673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_665673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665673 prefixEnd_665673 := by exact prefixLift 665673
  have htrace : WordTrace (prefixWord ++ tailWord_665673) baseStart_665673 baseEnd_665673 := by
    simpa [prefixWord, tailWord_665673, baseEnd_665673] using wordTrace_append hprefix tailTrace_665673
  have hstable : (prefixWord ++ tailWord_665673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665673).length < 2 ^ (prefixWord ++ tailWord_665673).sum := by decide
  have hdescent : baseEnd_665673 < baseStart_665673 := by decide
  rcases family_descends (prefixWord ++ tailWord_665673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665676 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_665676 : Nat := 118140960795 + 665676 * 2 ^ 59
def prefixEnd_665676 : Nat := 4983230072969 + 3 ^ 40 * 665676 * 2
def baseEnd_665676 : Nat := 151916332516641232572719

theorem tailTrace_665676 : CollatzResearch.WordTrace tailWord_665676 prefixEnd_665676 151916332516641232572719 := by
  unfold tailWord_665676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139599168188507627356441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16186132224251343503141921 12139599168188507627356441)
  ·
    refine ⟨9104699376141380720517331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12139599168188507627356441 9104699376141380720517331)
    ·
      refine ⟨13657049064212071080775997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9104699376141380720517331 13657049064212071080775997)
      ·
        refine ⟨5121393399079526655290999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13657049064212071080775997 5121393399079526655290999)
        ·
          refine ⟨7682090098619289982936499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121393399079526655290999 7682090098619289982936499)
          ·
            refine ⟨11523135147928934974404749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682090098619289982936499 11523135147928934974404749)
            ·
              refine ⟨4321175680473350615401781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11523135147928934974404749 4321175680473350615401781)
              ·
                refine ⟨405110220044376620193917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4321175680473350615401781 405110220044376620193917)
                ·
                  refine ⟨151916332516641232572719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405110220044376620193917 151916332516641232572719)
                  ·
                    rfl

theorem cell21_665676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_665676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665676 prefixEnd_665676 := by exact prefixLift 665676
  have htrace : WordTrace (prefixWord ++ tailWord_665676) baseStart_665676 baseEnd_665676 := by
    simpa [prefixWord, tailWord_665676, baseEnd_665676] using wordTrace_append hprefix tailTrace_665676
  have hstable : (prefixWord ++ tailWord_665676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665676).length < 2 ^ (prefixWord ++ tailWord_665676).sum := by decide
  have hdescent : baseEnd_665676 < baseStart_665676 := by decide
  rcases family_descends (prefixWord ++ tailWord_665676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665693 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 5]
def baseStart_665693 : Nat := 118140960795 + 665693 * 2 ^ 59
def prefixEnd_665693 : Nat := 4983230072969 + 3 ^ 40 * 665693 * 2
def baseEnd_665693 : Nat := 151920212148252980789351

theorem tailTrace_665693 : CollatzResearch.WordTrace tailWord_665693 prefixEnd_665693 151920212148252980789351 := by
  unfold tailWord_665693
  simp only [CollatzResearch.WordTrace]
  refine ⟨24279818377315427158081733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16186545584876951438721155 24279818377315427158081733)
  ·
    refine ⟨4552465945746642592140325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24279818377315427158081733 4552465945746642592140325)
    ·
      refine ⟨853587364827495486026311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4552465945746642592140325 853587364827495486026311)
      ·
        refine ⟨1280381047241243229039467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853587364827495486026311 1280381047241243229039467)
        ·
          refine ⟨1920571570861864843559201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280381047241243229039467 1920571570861864843559201)
          ·
            refine ⟨1440428678146398632669401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1920571570861864843559201 1440428678146398632669401)
            ·
              refine ⟨1080321508609798974502051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440428678146398632669401 1080321508609798974502051)
              ·
                refine ⟨1620482262914698461753077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080321508609798974502051 1620482262914698461753077)
                ·
                  refine ⟨151920212148252980789351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1620482262914698461753077 151920212148252980789351)
                  ·
                    rfl

theorem cell21_665693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_665693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665693 prefixEnd_665693 := by exact prefixLift 665693
  have htrace : WordTrace (prefixWord ++ tailWord_665693) baseStart_665693 baseEnd_665693 := by
    simpa [prefixWord, tailWord_665693, baseEnd_665693] using wordTrace_append hprefix tailTrace_665693
  have hstable : (prefixWord ++ tailWord_665693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665693).length < 2 ^ (prefixWord ++ tailWord_665693).sum := by decide
  have hdescent : baseEnd_665693 < baseStart_665693 := by decide
  rcases family_descends (prefixWord ++ tailWord_665693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665721 : List Nat := [1, 2, 1, 3, 4, 1, 4, 5]
def baseStart_665721 : Nat := 118140960795 + 665721 * 2 ^ 59
def prefixEnd_665721 : Nat := 4983230072969 + 3 ^ 40 * 665721 * 2
def baseEnd_665721 : Nat := 50642200709910384774209

theorem tailTrace_665721 : CollatzResearch.WordTrace tailWord_665721 prefixEnd_665721 50642200709910384774209 := by
  unfold tailWord_665721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24280839621213987940101017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16187226414142658626734011 24280839621213987940101017)
  ·
    refine ⟨18210629715910490955075763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24280839621213987940101017 18210629715910490955075763)
    ·
      refine ⟨27315944573865736432613645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18210629715910490955075763 27315944573865736432613645)
      ·
        refine ⟨10243479215199651162230117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27315944573865736432613645 10243479215199651162230117)
        ·
          refine ⟨1920652352849934592918147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10243479215199651162230117 1920652352849934592918147)
          ·
            refine ⟨2880978529274901889377221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920652352849934592918147 2880978529274901889377221)
            ·
              refine ⟨540183474239044104258229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2880978529274901889377221 540183474239044104258229)
              ·
                refine ⟨50642200709910384774209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540183474239044104258229 50642200709910384774209)
                ·
                  rfl

theorem cell21_665721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 5].length) (baseStart_665721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665721 prefixEnd_665721 := by exact prefixLift 665721
  have htrace : WordTrace (prefixWord ++ tailWord_665721) baseStart_665721 baseEnd_665721 := by
    simpa [prefixWord, tailWord_665721, baseEnd_665721] using wordTrace_append hprefix tailTrace_665721
  have hstable : (prefixWord ++ tailWord_665721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665721).length < 2 ^ (prefixWord ++ tailWord_665721).sum := by decide
  have hdescent : baseEnd_665721 < baseStart_665721 := by decide
  rcases family_descends (prefixWord ++ tailWord_665721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665749 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_665749 : Nat := 118140960795 + 665749 * 2 ^ 59
def prefixEnd_665749 : Nat := 4983230072969 + 3 ^ 40 * 665749 * 2
def baseEnd_665749 : Nat := 151932992111209327855903

theorem tailTrace_665749 : CollatzResearch.WordTrace tailWord_665749 prefixEnd_665749 151932992111209327855903 := by
  unfold tailWord_665749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24281860865112548722120301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16187907243408365814746867 24281860865112548722120301)
  ·
    refine ⟨9105697824417205770795113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24281860865112548722120301 9105697824417205770795113)
    ·
      refine ⟨6829273368312904328096335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9105697824417205770795113 6829273368312904328096335)
      ·
        refine ⟨10243910052469356492144503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6829273368312904328096335 10243910052469356492144503)
        ·
          refine ⟨15365865078704034738216755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10243910052469356492144503 15365865078704034738216755)
          ·
            refine ⟨23048797618056052107325133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15365865078704034738216755 23048797618056052107325133)
            ·
              refine ⟨8643299106771019540246925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23048797618056052107325133 8643299106771019540246925)
              ·
                refine ⟨3241237165039132327592597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8643299106771019540246925 3241237165039132327592597)
                ·
                  refine ⟨151932992111209327855903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3241237165039132327592597 151932992111209327855903)
                  ·
                    rfl

theorem cell21_665749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_665749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665749 prefixEnd_665749 := by exact prefixLift 665749
  have htrace : WordTrace (prefixWord ++ tailWord_665749) baseStart_665749 baseEnd_665749 := by
    simpa [prefixWord, tailWord_665749, baseEnd_665749] using wordTrace_append hprefix tailTrace_665749
  have hstable : (prefixWord ++ tailWord_665749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665749).length < 2 ^ (prefixWord ++ tailWord_665749).sum := by decide
  have hdescent : baseEnd_665749 < baseStart_665749 := by decide
  rcases family_descends (prefixWord ++ tailWord_665749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665758 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_665758 : Nat := 118140960795 + 665758 * 2 ^ 59
def prefixEnd_665758 : Nat := 4983230072969 + 3 ^ 40 * 665758 * 2
def baseEnd_665758 : Nat := 151935046033827312205885

theorem tailTrace_665758 : CollatzResearch.WordTrace tailWord_665758 prefixEnd_665758 151935046033827312205885 := by
  unfold tailWord_665758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035273640259992907399741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16188126081386628839465285 3035273640259992907399741)
  ·
    refine ⟨1138227615097497340274903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3035273640259992907399741 1138227615097497340274903)
    ·
      refine ⟨1707341422646246010412355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138227615097497340274903 1707341422646246010412355)
      ·
        refine ⟨2561012133969369015618533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707341422646246010412355 2561012133969369015618533)
        ·
          refine ⟨480189775119256690428475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2561012133969369015618533 480189775119256690428475)
          ·
            refine ⟨720284662678885035642713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480189775119256690428475 720284662678885035642713)
            ·
              refine ⟨540213497009163776732035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720284662678885035642713 540213497009163776732035)
              ·
                refine ⟨810320245513745665098053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540213497009163776732035 810320245513745665098053)
                ·
                  refine ⟨151935046033827312205885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 810320245513745665098053 151935046033827312205885)
                  ·
                    rfl

theorem cell21_665758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_665758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665758 prefixEnd_665758 := by exact prefixLift 665758
  have htrace : WordTrace (prefixWord ++ tailWord_665758) baseStart_665758 baseEnd_665758 := by
    simpa [prefixWord, tailWord_665758, baseEnd_665758] using wordTrace_append hprefix tailTrace_665758
  have hstable : (prefixWord ++ tailWord_665758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665758).length < 2 ^ (prefixWord ++ tailWord_665758).sum := by decide
  have hdescent : baseEnd_665758 < baseStart_665758 := by decide
  rcases family_descends (prefixWord ++ tailWord_665758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665814 : List Nat := [5, 2, 1, 2, 1, 1, 3, 6]
def baseStart_665814 : Nat := 118140960795 + 665814 * 2 ^ 59
def prefixEnd_665814 : Nat := 4983230072969 + 3 ^ 40 * 665814 * 2
def baseEnd_665814 : Nat := 50649275332261219757479

theorem tailTrace_665814 : CollatzResearch.WordTrace tailWord_665814 prefixEnd_665814 50649275332261219757479 := by
  unfold tailWord_665814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517764475617316551452281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16189487739918043215490997 1517764475617316551452281)
  ·
    refine ⟨1138323356712987413589211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1517764475617316551452281 1138323356712987413589211)
    ·
      refine ⟨1707485035069481120383817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138323356712987413589211 1707485035069481120383817)
      ·
        refine ⟨1280613776302110840287863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707485035069481120383817 1280613776302110840287863)
        ·
          refine ⟨1920920664453166260431795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280613776302110840287863 1920920664453166260431795)
          ·
            refine ⟨2881380996679749390647693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920920664453166260431795 2881380996679749390647693)
            ·
              refine ⟨1080517873754906021492885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2881380996679749390647693 1080517873754906021492885)
              ·
                refine ⟨50649275332261219757479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1080517873754906021492885 50649275332261219757479)
                ·
                  rfl

theorem cell21_665814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_665814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665814 prefixEnd_665814 := by exact prefixLift 665814
  have htrace : WordTrace (prefixWord ++ tailWord_665814) baseStart_665814 baseEnd_665814 := by
    simpa [prefixWord, tailWord_665814, baseEnd_665814] using wordTrace_append hprefix tailTrace_665814
  have hstable : (prefixWord ++ tailWord_665814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665814).length < 2 ^ (prefixWord ++ tailWord_665814).sum := by decide
  have hdescent : baseEnd_665814 < baseStart_665814 := by decide
  rcases family_descends (prefixWord ++ tailWord_665814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665887 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_665887 : Nat := 118140960795 + 665887 * 2 ^ 59
def prefixEnd_665887 : Nat := 4983230072969 + 3 ^ 40 * 665887 * 2
def baseEnd_665887 : Nat := 151964485591351754555621

theorem tailTrace_665887 : CollatzResearch.WordTrace tailWord_665887 prefixEnd_665887 151964485591351754555621 := by
  unfold tailWord_665887
  simp only [CollatzResearch.WordTrace]
  refine ⟨24286894138612598290643915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16191262759075065527095943 24286894138612598290643915)
  ·
    refine ⟨36430341207918897435965873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24286894138612598290643915 36430341207918897435965873)
    ·
      refine ⟨27322755905939173076974405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36430341207918897435965873 27322755905939173076974405)
      ·
        refine ⟨5123016732363594951932701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27322755905939173076974405 5123016732363594951932701)
        ·
          refine ⟨1921131274636348106974763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5123016732363594951932701 1921131274636348106974763)
          ·
            refine ⟨2881696911954522160462145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921131274636348106974763 2881696911954522160462145)
            ·
              refine ⟨2161272683965891620346609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881696911954522160462145 2161272683965891620346609)
              ·
                refine ⟨1620954512974418715259957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161272683965891620346609 1620954512974418715259957)
                ·
                  refine ⟨151964485591351754555621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1620954512974418715259957 151964485591351754555621)
                  ·
                    rfl

theorem cell21_665887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_665887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665887 prefixEnd_665887 := by exact prefixLift 665887
  have htrace : WordTrace (prefixWord ++ tailWord_665887) baseStart_665887 baseEnd_665887 := by
    simpa [prefixWord, tailWord_665887, baseEnd_665887] using wordTrace_append hprefix tailTrace_665887
  have hstable : (prefixWord ++ tailWord_665887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665887).length < 2 ^ (prefixWord ++ tailWord_665887).sum := by decide
  have hdescent : baseEnd_665887 < baseStart_665887 := by decide
  rcases family_descends (prefixWord ++ tailWord_665887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665890 : List Nat := [3, 3, 1, 1, 3, 3, 2, 5]
def baseStart_665890 : Nat := 118140960795 + 665890 * 2 ^ 59
def prefixEnd_665890 : Nat := 4983230072969 + 3 ^ 40 * 665890 * 2
def baseEnd_665890 : Nat := 50655056744074805335205

theorem tailTrace_665890 : CollatzResearch.WordTrace tailWord_665890 prefixEnd_665890 50655056744074805335205 := by
  unfold tailWord_665890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071750889400432450750781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16191335705067819868668749 6071750889400432450750781)
  ·
    refine ⟨2276906583525162169031543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6071750889400432450750781 2276906583525162169031543)
    ·
      refine ⟨3415359875287743253547315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2276906583525162169031543 3415359875287743253547315)
      ·
        refine ⟨5123039812931614880320973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415359875287743253547315 5123039812931614880320973)
        ·
          refine ⟨1921139929849355580120365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5123039812931614880320973 1921139929849355580120365)
          ·
            refine ⟨720427473693508342545137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1921139929849355580120365 720427473693508342545137)
            ·
              refine ⟨540320605270131256908853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720427473693508342545137 540320605270131256908853)
              ·
                refine ⟨50655056744074805335205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540320605270131256908853 50655056744074805335205)
                ·
                  rfl

theorem cell21_665890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_665890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665890 prefixEnd_665890 := by exact prefixLift 665890
  have htrace : WordTrace (prefixWord ++ tailWord_665890) baseStart_665890 baseEnd_665890 := by
    simpa [prefixWord, tailWord_665890, baseEnd_665890] using wordTrace_append hprefix tailTrace_665890
  have hstable : (prefixWord ++ tailWord_665890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665890).length < 2 ^ (prefixWord ++ tailWord_665890).sum := by decide
  have hdescent : baseEnd_665890 < baseStart_665890 := by decide
  rcases family_descends (prefixWord ++ tailWord_665890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665918 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_665918 : Nat := 118140960795 + 665918 * 2 ^ 59
def prefixEnd_665918 : Nat := 4983230072969 + 3 ^ 40 * 665918 * 2
def baseEnd_665918 : Nat := 151971560213702589538891

theorem tailTrace_665918 : CollatzResearch.WordTrace tailWord_665918 prefixEnd_665918 151971560213702589538891 := by
  unfold tailWord_665918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036003100187536323127801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16192016534333527056681605 3036003100187536323127801)
  ·
    refine ⟨2277002325140652242345851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3036003100187536323127801 2277002325140652242345851)
    ·
      refine ⟨3415503487710978363518777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277002325140652242345851 3415503487710978363518777)
      ·
        refine ⟨2561627615783233772639083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3415503487710978363518777 2561627615783233772639083)
        ·
          refine ⟨3842441423674850658958625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561627615783233772639083 3842441423674850658958625)
          ·
            refine ⟨2881831067756137994218969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3842441423674850658958625 2881831067756137994218969)
            ·
              refine ⟨2161373300817103495664227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881831067756137994218969 2161373300817103495664227)
              ·
                refine ⟨3242059951225655243496341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161373300817103495664227 3242059951225655243496341)
                ·
                  refine ⟨151971560213702589538891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3242059951225655243496341 151971560213702589538891)
                  ·
                    rfl

theorem cell21_665918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_665918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665918 prefixEnd_665918 := by exact prefixLift 665918
  have htrace : WordTrace (prefixWord ++ tailWord_665918) baseStart_665918 baseEnd_665918 := by
    simpa [prefixWord, tailWord_665918, baseEnd_665918] using wordTrace_append hprefix tailTrace_665918
  have hstable : (prefixWord ++ tailWord_665918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665918).length < 2 ^ (prefixWord ++ tailWord_665918).sum := by decide
  have hdescent : baseEnd_665918 < baseStart_665918 := by decide
  rcases family_descends (prefixWord ++ tailWord_665918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665921 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 5]
def baseStart_665921 : Nat := 118140960795 + 665921 * 2 ^ 59
def prefixEnd_665921 : Nat := 4983230072969 + 3 ^ 40 * 665921 * 2
def baseEnd_665921 : Nat := 151972244854575250988885

theorem tailTrace_665921 : CollatzResearch.WordTrace tailWord_665921 prefixEnd_665921 151972244854575250988885 := by
  unfold tailWord_665921
  simp only [CollatzResearch.WordTrace]
  refine ⟨24288134220489422097381617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16192089480326281398254411 24288134220489422097381617)
  ·
    refine ⟨18216100665367066573036213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24288134220489422097381617 18216100665367066573036213)
    ·
      refine ⟨1707759437378162491222145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18216100665367066573036213 1707759437378162491222145)
      ·
        refine ⟨1280819578033621868416609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707759437378162491222145 1280819578033621868416609)
        ·
          refine ⟨960614683525216401312457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1280819578033621868416609 960614683525216401312457)
          ·
            refine ⟨720461012643912300984343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960614683525216401312457 720461012643912300984343)
            ·
              refine ⟨1080691518965868451476515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720461012643912300984343 1080691518965868451476515)
              ·
                refine ⟨1621037278448802677214773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080691518965868451476515 1621037278448802677214773)
                ·
                  refine ⟨151972244854575250988885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621037278448802677214773 151972244854575250988885)
                  ·
                    rfl

theorem cell21_665921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_665921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665921 prefixEnd_665921 := by exact prefixLift 665921
  have htrace : WordTrace (prefixWord ++ tailWord_665921) baseStart_665921 baseEnd_665921 := by
    simpa [prefixWord, tailWord_665921, baseEnd_665921] using wordTrace_append hprefix tailTrace_665921
  have hstable : (prefixWord ++ tailWord_665921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665921).length < 2 ^ (prefixWord ++ tailWord_665921).sum := by decide
  have hdescent : baseEnd_665921 < baseStart_665921 := by decide
  rcases family_descends (prefixWord ++ tailWord_665921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665932 : List Nat := [2, 2, 1, 3, 2, 1, 4, 6]
def baseStart_665932 : Nat := 118140960795 + 665932 * 2 ^ 59
def prefixEnd_665932 : Nat := 4983230072969 + 3 ^ 40 * 665932 * 2
def baseEnd_665932 : Nat := 50658251734813892101843

theorem tailTrace_665932 : CollatzResearch.WordTrace tailWord_665932 prefixEnd_665932 50658251734813892101843 := by
  unfold tailWord_665932
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144267711724785488016025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16192356948966380650688033 12144267711724785488016025)
  ·
    refine ⟨9108200783793589116012019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12144267711724785488016025 9108200783793589116012019)
    ·
      refine ⟨13662301175690383674018029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9108200783793589116012019 13662301175690383674018029)
      ·
        refine ⟨5123362940883893877756761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13662301175690383674018029 5123362940883893877756761)
        ·
          refine ⟨3842522205662920408317571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5123362940883893877756761 3842522205662920408317571)
          ·
            refine ⟨5763783308494380612476357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842522205662920408317571 5763783308494380612476357)
            ·
              refine ⟨1080709370342696364839317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5763783308494380612476357 1080709370342696364839317)
              ·
                refine ⟨50658251734813892101843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1080709370342696364839317 50658251734813892101843)
                ·
                  rfl

theorem cell21_665932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_665932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665932 prefixEnd_665932 := by exact prefixLift 665932
  have htrace : WordTrace (prefixWord ++ tailWord_665932) baseStart_665932 baseEnd_665932 := by
    simpa [prefixWord, tailWord_665932, baseEnd_665932] using wordTrace_append hprefix tailTrace_665932
  have hstable : (prefixWord ++ tailWord_665932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665932).length < 2 ^ (prefixWord ++ tailWord_665932).sum := by decide
  have hdescent : baseEnd_665932 < baseStart_665932 := by decide
  rcases family_descends (prefixWord ++ tailWord_665932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665946 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_665946 : Nat := 118140960795 + 665946 * 2 ^ 59
def prefixEnd_665946 : Nat := 4983230072969 + 3 ^ 40 * 665946 * 2
def baseEnd_665946 : Nat := 151977950195180763072167

theorem tailTrace_665946 : CollatzResearch.WordTrace tailWord_665946 prefixEnd_665946 151977950195180763072167 := by
  unfold tailWord_665946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6072261511349712841760423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16192697363599234244694461 6072261511349712841760423)
  ·
    refine ⟨9108392267024569262640635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6072261511349712841760423 9108392267024569262640635)
    ·
      refine ⟨13662588400536853893960953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9108392267024569262640635 13662588400536853893960953)
      ·
        refine ⟨10246941300402640420470715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13662588400536853893960953 10246941300402640420470715)
        ·
          refine ⟨15370411950603960630706073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10246941300402640420470715 15370411950603960630706073)
          ·
            refine ⟨11527808962952970473029555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15370411950603960630706073 11527808962952970473029555)
            ·
              refine ⟨17291713444429455709544333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11527808962952970473029555 17291713444429455709544333)
              ·
                refine ⟨6484392541661045891079125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17291713444429455709544333 6484392541661045891079125)
                ·
                  refine ⟨151977950195180763072167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6484392541661045891079125 151977950195180763072167)
                  ·
                    rfl

theorem cell21_665946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_665946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665946 prefixEnd_665946 := by exact prefixLift 665946
  have htrace : WordTrace (prefixWord ++ tailWord_665946) baseStart_665946 baseEnd_665946 := by
    simpa [prefixWord, tailWord_665946, baseEnd_665946] using wordTrace_append hprefix tailTrace_665946
  have hstable : (prefixWord ++ tailWord_665946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665946).length < 2 ^ (prefixWord ++ tailWord_665946).sum := by decide
  have hdescent : baseEnd_665946 < baseStart_665946 := by decide
  rcases family_descends (prefixWord ++ tailWord_665946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666014 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_666014 : Nat := 118140960795 + 666014 * 2 ^ 59
def prefixEnd_666014 : Nat := 4983230072969 + 3 ^ 40 * 666014 * 2
def baseEnd_666014 : Nat := 151993468721627755938695

theorem tailTrace_666014 : CollatzResearch.WordTrace tailWord_666014 prefixEnd_666014 151993468721627755938695 := by
  unfold tailWord_666014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036440776144062372564637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16194350806101665987011397 3036440776144062372564637)
  ·
    refine ⟨1138665291054023389711739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3036440776144062372564637 1138665291054023389711739)
    ·
      refine ⟨1707997936581035084567609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138665291054023389711739 1707997936581035084567609)
      ·
        refine ⟨1280998452435776313425707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707997936581035084567609 1280998452435776313425707)
        ·
          refine ⟨1921497678653664470138561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280998452435776313425707 1921497678653664470138561)
          ·
            refine ⟨1441123258990248352603921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1921497678653664470138561 1441123258990248352603921)
            ·
              refine ⟨1080842444242686264452941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441123258990248352603921 1080842444242686264452941)
              ·
                refine ⟨405315916591007349169853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1080842444242686264452941 405315916591007349169853)
                ·
                  refine ⟨151993468721627755938695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405315916591007349169853 151993468721627755938695)
                  ·
                    rfl

theorem cell21_666014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_666014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666014 prefixEnd_666014 := by exact prefixLift 666014
  have htrace : WordTrace (prefixWord ++ tailWord_666014) baseStart_666014 baseEnd_666014 := by
    simpa [prefixWord, tailWord_666014, baseEnd_666014] using wordTrace_append hprefix tailTrace_666014
  have hstable : (prefixWord ++ tailWord_666014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666014).length < 2 ^ (prefixWord ++ tailWord_666014).sum := by decide
  have hdescent : baseEnd_666014 < baseStart_666014 := by decide
  rcases family_descends (prefixWord ++ tailWord_666014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666039 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 5]
def baseStart_666039 : Nat := 118140960795 + 666039 * 2 ^ 59
def prefixEnd_666039 : Nat := 4983230072969 + 3 ^ 40 * 666039 * 2
def baseEnd_666039 : Nat := 151999174062233268021977

theorem tailTrace_666039 : CollatzResearch.WordTrace tailWord_666039 prefixEnd_666039 151999174062233268021977 := by
  unfold tailWord_666039
  simp only [CollatzResearch.WordTrace]
  refine ⟨24292438034061928250177171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16194958689374618833451447 24292438034061928250177171)
  ·
    refine ⟨36438657051092892375265757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24292438034061928250177171 36438657051092892375265757)
    ·
      refine ⟨13664496394159834640724659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36438657051092892375265757 13664496394159834640724659)
      ·
        refine ⟨20496744591239751961086989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13664496394159834640724659 20496744591239751961086989)
        ·
          refine ⟨7686279221714906985407621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20496744591239751961086989 7686279221714906985407621)
          ·
            refine ⟨1441177354071545059763929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7686279221714906985407621 1441177354071545059763929)
            ·
              refine ⟨1080883015553658794822947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441177354071545059763929 1080883015553658794822947)
              ·
                refine ⟨1621324523330488192234421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080883015553658794822947 1621324523330488192234421)
                ·
                  refine ⟨151999174062233268021977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621324523330488192234421 151999174062233268021977)
                  ·
                    rfl

theorem cell21_666039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_666039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666039 prefixEnd_666039 := by exact prefixLift 666039
  have htrace : WordTrace (prefixWord ++ tailWord_666039) baseStart_666039 baseEnd_666039 := by
    simpa [prefixWord, tailWord_666039, baseEnd_666039] using wordTrace_append hprefix tailTrace_666039
  have hstable : (prefixWord ++ tailWord_666039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666039).length < 2 ^ (prefixWord ++ tailWord_666039).sum := by decide
  have hdescent : baseEnd_666039 < baseStart_666039 := by decide
  rcases family_descends (prefixWord ++ tailWord_666039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666070 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_666070 : Nat := 118140960795 + 666070 * 2 ^ 59
def prefixEnd_666070 : Nat := 4983230072969 + 3 ^ 40 * 666070 * 2
def baseEnd_666070 : Nat := 152006248684584103005247

theorem tailTrace_666070 : CollatzResearch.WordTrace tailWord_666070 prefixEnd_666070 152006248684584103005247 := by
  unfold tailWord_666070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518348043559351284034729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16195712464633080363037109 1518348043559351284034729)
  ·
    refine ⟨1138761032669513463026047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1518348043559351284034729 1138761032669513463026047)
    ·
      refine ⟨1708141549004270194539071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138761032669513463026047 1708141549004270194539071)
      ·
        refine ⟨2562212323506405291808607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708141549004270194539071 2562212323506405291808607)
        ·
          refine ⟨3843318485259607937712911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562212323506405291808607 3843318485259607937712911)
          ·
            refine ⟨5764977727889411906569367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843318485259607937712911 5764977727889411906569367)
            ·
              refine ⟨8647466591834117859854051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5764977727889411906569367 8647466591834117859854051)
              ·
                refine ⟨12971199887751176789781077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8647466591834117859854051 12971199887751176789781077)
                ·
                  refine ⟨152006248684584103005247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12971199887751176789781077 152006248684584103005247)
                  ·
                    rfl

theorem cell21_666070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_666070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666070 prefixEnd_666070 := by exact prefixLift 666070
  have htrace : WordTrace (prefixWord ++ tailWord_666070) baseStart_666070 baseEnd_666070 := by
    simpa [prefixWord, tailWord_666070, baseEnd_666070] using wordTrace_append hprefix tailTrace_666070
  have hstable : (prefixWord ++ tailWord_666070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666070).length < 2 ^ (prefixWord ++ tailWord_666070).sum := by decide
  have hdescent : baseEnd_666070 < baseStart_666070 := by decide
  rcases family_descends (prefixWord ++ tailWord_666070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666177 : List Nat := [1, 2, 5, 1, 1, 3, 3, 5]
def baseStart_666177 : Nat := 118140960795 + 666177 * 2 ^ 59
def prefixEnd_666177 : Nat := 4983230072969 + 3 ^ 40 * 666177 * 2
def baseEnd_666177 : Nat := 50676889180791898240565

theorem tailTrace_666177 : CollatzResearch.WordTrace tailWord_666177 prefixEnd_666177 50676889180791898240565 := by
  unfold tailWord_666177
  simp only [CollatzResearch.WordTrace]
  refine ⟨24297471307561977818700785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16198314205041318545800523 24297471307561977818700785)
  ·
    refine ⟨18223103480671483364025589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24297471307561977818700785 18223103480671483364025589)
    ·
      refine ⟨1708415951312951565377399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18223103480671483364025589 1708415951312951565377399)
      ·
        refine ⟨2562623926969427348066099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708415951312951565377399 2562623926969427348066099)
        ·
          refine ⟨3843935890454141022099149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562623926969427348066099 3843935890454141022099149)
          ·
            refine ⟨1441475958920302883287181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3843935890454141022099149 1441475958920302883287181)
            ·
              refine ⟨540553484595113581232693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441475958920302883287181 540553484595113581232693)
              ·
                refine ⟨50676889180791898240565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540553484595113581232693 50676889180791898240565)
                ·
                  rfl

theorem cell21_666177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 5].length) (baseStart_666177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666177 prefixEnd_666177 := by exact prefixLift 666177
  have htrace : WordTrace (prefixWord ++ tailWord_666177) baseStart_666177 baseEnd_666177 := by
    simpa [prefixWord, tailWord_666177, baseEnd_666177] using wordTrace_append hprefix tailTrace_666177
  have hstable : (prefixWord ++ tailWord_666177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666177).length < 2 ^ (prefixWord ++ tailWord_666177).sum := by decide
  have hdescent : baseEnd_666177 < baseStart_666177 := by decide
  rcases family_descends (prefixWord ++ tailWord_666177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666191 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 3]
def baseStart_666191 : Nat := 118140960795 + 666191 * 2 ^ 59
def prefixEnd_666191 : Nat := 4983230072969 + 3 ^ 40 * 666191 * 2
def baseEnd_666191 : Nat := 152033862533114781488333

theorem tailTrace_666191 : CollatzResearch.WordTrace tailWord_666191 prefixEnd_666191 152033862533114781488333 := by
  unfold tailWord_666191
  simp only [CollatzResearch.WordTrace]
  refine ⟨24297981929511258209710427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16198654619674172139806951 24297981929511258209710427)
  ·
    refine ⟨36446972894266887314565641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24297981929511258209710427 36446972894266887314565641)
    ·
      refine ⟨27335229670700165485924231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36446972894266887314565641 27335229670700165485924231)
      ·
        refine ⟨41002844506050248228886347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27335229670700165485924231 41002844506050248228886347)
        ·
          refine ⟨61504266759075372343329521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41002844506050248228886347 61504266759075372343329521)
          ·
            refine ⟨46128200069306529257497141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61504266759075372343329521 46128200069306529257497141)
            ·
              refine ⟨4324518756497487117890357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46128200069306529257497141 4324518756497487117890357)
              ·
                refine ⟨405423633421639417302221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4324518756497487117890357 405423633421639417302221)
                ·
                  refine ⟨152033862533114781488333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405423633421639417302221 152033862533114781488333)
                  ·
                    rfl

theorem cell21_666191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 3].length) (baseStart_666191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666191 prefixEnd_666191 := by exact prefixLift 666191
  have htrace : WordTrace (prefixWord ++ tailWord_666191) baseStart_666191 baseEnd_666191 := by
    simpa [prefixWord, tailWord_666191, baseEnd_666191] using wordTrace_append hprefix tailTrace_666191
  have hstable : (prefixWord ++ tailWord_666191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666191).length < 2 ^ (prefixWord ++ tailWord_666191).sum := by decide
  have hdescent : baseEnd_666191 < baseStart_666191 := by decide
  rcases family_descends (prefixWord ++ tailWord_666191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666236 : List Nat := [2, 2, 2, 1, 1, 2, 6, 5]
def baseStart_666236 : Nat := 118140960795 + 666236 * 2 ^ 59
def prefixEnd_666236 : Nat := 4983230072969 + 3 ^ 40 * 666236 * 2
def baseEnd_666236 : Nat := 50681377382068234412747

theorem tailTrace_666236 : CollatzResearch.WordTrace tailWord_666236 prefixEnd_666236 50681377382068234412747 := by
  unfold tailWord_666236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149811607174115447549281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16199748809565487263399041 12149811607174115447549281)
  ·
    refine ⟨9112358705380586585661961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12149811607174115447549281 9112358705380586585661961)
    ·
      refine ⟨6834269029035439939246471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9112358705380586585661961 6834269029035439939246471)
      ·
        refine ⟨10251403543553159908869707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6834269029035439939246471 10251403543553159908869707)
        ·
          refine ⟨15377105315329739863304561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10251403543553159908869707 15377105315329739863304561)
          ·
            refine ⟨11532828986497304897478421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15377105315329739863304561 11532828986497304897478421)
            ·
              refine ⟨540601358742061167069301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11532828986497304897478421 540601358742061167069301)
              ·
                refine ⟨50681377382068234412747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540601358742061167069301 50681377382068234412747)
                ·
                  rfl

theorem cell21_666236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_666236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666236 prefixEnd_666236 := by exact prefixLift 666236
  have htrace : WordTrace (prefixWord ++ tailWord_666236) baseStart_666236 baseEnd_666236 := by
    simpa [prefixWord, tailWord_666236, baseEnd_666236] using wordTrace_append hprefix tailTrace_666236
  have hstable : (prefixWord ++ tailWord_666236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666236).length < 2 ^ (prefixWord ++ tailWord_666236).sum := by decide
  have hdescent : baseEnd_666236 < baseStart_666236 := by decide
  rcases family_descends (prefixWord ++ tailWord_666236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666391 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 4]
def baseStart_666391 : Nat := 118140960795 + 666391 * 2 ^ 59
def prefixEnd_666391 : Nat := 4983230072969 + 3 ^ 40 * 666391 * 2
def baseEnd_666391 : Nat := 152079505257958878154591

theorem tailTrace_666391 : CollatzResearch.WordTrace tailWord_666391 prefixEnd_666391 152079505257958878154591 := by
  unfold tailWord_666391
  simp only [CollatzResearch.WordTrace]
  refine ⟨24305276528786692366991027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16203517685857794911327351 24305276528786692366991027)
  ·
    refine ⟨36457914793180038550486541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24305276528786692366991027 36457914793180038550486541)
    ·
      refine ⟨13671718047442514456432453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36457914793180038550486541 13671718047442514456432453)
      ·
        refine ⟨2563447133895471460581085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13671718047442514456432453 2563447133895471460581085)
        ·
          refine ⟨961292675210801797717907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2563447133895471460581085 961292675210801797717907)
          ·
            refine ⟨1441939012816202696576861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961292675210801797717907 1441939012816202696576861)
            ·
              refine ⟨540727129806076011216323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441939012816202696576861 540727129806076011216323)
              ·
                refine ⟨811090694709114016824485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540727129806076011216323 811090694709114016824485)
                ·
                  refine ⟨152079505257958878154591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811090694709114016824485 152079505257958878154591)
                  ·
                    rfl

theorem cell21_666391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 4].length) (baseStart_666391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666391 prefixEnd_666391 := by exact prefixLift 666391
  have htrace : WordTrace (prefixWord ++ tailWord_666391) baseStart_666391 baseEnd_666391 := by
    simpa [prefixWord, tailWord_666391, baseEnd_666391] using wordTrace_append hprefix tailTrace_666391
  have hstable : (prefixWord ++ tailWord_666391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666391).length < 2 ^ (prefixWord ++ tailWord_666391).sum := by decide
  have hdescent : baseEnd_666391 < baseStart_666391 := by decide
  rcases family_descends (prefixWord ++ tailWord_666391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666422 : List Nat := [5, 1, 2, 2, 3, 1, 7]
def baseStart_666422 : Nat := 118140960795 + 666422 * 2 ^ 59
def prefixEnd_666422 : Nat := 4983230072969 + 3 ^ 40 * 666422 * 2
def baseEnd_666422 : Nat := 16898508875589968126429

theorem tailTrace_666422 : CollatzResearch.WordTrace tailWord_666422 prefixEnd_666422 16898508875589968126429 := by
  unfold tailWord_666422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519150449479649041335595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16204271461116256440913013 1519150449479649041335595)
  ·
    refine ⟨2278725674219473562003393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519150449479649041335595 2278725674219473562003393)
    ·
      refine ⟨1709044255664605171502545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2278725674219473562003393 1709044255664605171502545)
      ·
        refine ⟨1281783191748453878626909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1709044255664605171502545 1281783191748453878626909)
        ·
          refine ⟨480668696905670204485091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1281783191748453878626909 480668696905670204485091)
          ·
            refine ⟨721003045358505306727637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480668696905670204485091 721003045358505306727637)
            ·
              refine ⟨16898508875589968126429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 721003045358505306727637 16898508875589968126429)
              ·
                rfl

theorem cell21_666422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 7].length) (baseStart_666422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666422 prefixEnd_666422 := by exact prefixLift 666422
  have htrace : WordTrace (prefixWord ++ tailWord_666422) baseStart_666422 baseEnd_666422 := by
    simpa [prefixWord, tailWord_666422, baseEnd_666422] using wordTrace_append hprefix tailTrace_666422
  have hstable : (prefixWord ++ tailWord_666422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666422).length < 2 ^ (prefixWord ++ tailWord_666422).sum := by decide
  have hdescent : baseEnd_666422 < baseStart_666422 := by decide
  rcases family_descends (prefixWord ++ tailWord_666422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666492 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_666492 : Nat := 118140960795 + 666492 * 2 ^ 59
def prefixEnd_666492 : Nat := 4983230072969 + 3 ^ 40 * 666492 * 2
def baseEnd_666492 : Nat := 152102554834005146971051

theorem tailTrace_666492 : CollatzResearch.WordTrace tailWord_666492 prefixEnd_666492 152102554834005146971051 := by
  unfold tailWord_666492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154480150710393308208865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16205973534280524410945153 12154480150710393308208865)
  ·
    refine ⟨9115860113032794981156649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12154480150710393308208865 9115860113032794981156649)
    ·
      refine ⟨6836895084774596235867487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9115860113032794981156649 6836895084774596235867487)
      ·
        refine ⟨10255342627161894353801231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836895084774596235867487 10255342627161894353801231)
        ·
          refine ⟨15383013940742841530701847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10255342627161894353801231 15383013940742841530701847)
          ·
            refine ⟨23074520911114262296052771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15383013940742841530701847 23074520911114262296052771)
            ·
              refine ⟨34611781366671393444079157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23074520911114262296052771 34611781366671393444079157)
              ·
                refine ⟨3244854503125443135382421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34611781366671393444079157 3244854503125443135382421)
                ·
                  refine ⟨152102554834005146971051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3244854503125443135382421 152102554834005146971051)
                  ·
                    rfl

theorem cell21_666492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_666492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666492 prefixEnd_666492 := by exact prefixLift 666492
  have htrace : WordTrace (prefixWord ++ tailWord_666492) baseStart_666492 baseEnd_666492 := by
    simpa [prefixWord, tailWord_666492, baseEnd_666492] using wordTrace_append hprefix tailTrace_666492
  have hstable : (prefixWord ++ tailWord_666492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666492).length < 2 ^ (prefixWord ++ tailWord_666492).sum := by decide
  have hdescent : baseEnd_666492 < baseStart_666492 := by decide
  rcases family_descends (prefixWord ++ tailWord_666492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666537 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_666537 : Nat := 118140960795 + 666537 * 2 ^ 59
def prefixEnd_666537 : Nat := 4983230072969 + 3 ^ 40 * 666537 * 2
def baseEnd_666537 : Nat := 152112824447095068720959

theorem tailTrace_666537 : CollatzResearch.WordTrace tailWord_666537 prefixEnd_666537 152112824447095068720959 := by
  unfold tailWord_666537
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310601586257759301805865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16207067724171839534537243 24310601586257759301805865)
  ·
    refine ⟨18232951189693319476354399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24310601586257759301805865 18232951189693319476354399)
    ·
      refine ⟨27349426784539979214531599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18232951189693319476354399 27349426784539979214531599)
      ·
        refine ⟨41024140176809968821797399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27349426784539979214531599 41024140176809968821797399)
        ·
          refine ⟨61536210265214953232696099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41024140176809968821797399 61536210265214953232696099)
          ·
            refine ⟨92304315397822429849044149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61536210265214953232696099 92304315397822429849044149)
            ·
              refine ⟨8653529568545852798347889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92304315397822429849044149 8653529568545852798347889)
              ·
                refine ⟨6490147176409389598760917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8653529568545852798347889 6490147176409389598760917)
                ·
                  refine ⟨152112824447095068720959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6490147176409389598760917 152112824447095068720959)
                  ·
                    rfl

theorem cell21_666537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_666537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666537 prefixEnd_666537 := by exact prefixLift 666537
  have htrace : WordTrace (prefixWord ++ tailWord_666537) baseStart_666537 baseEnd_666537 := by
    simpa [prefixWord, tailWord_666537, baseEnd_666537] using wordTrace_append hprefix tailTrace_666537
  have hstable : (prefixWord ++ tailWord_666537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666537).length < 2 ^ (prefixWord ++ tailWord_666537).sum := by decide
  have hdescent : baseEnd_666537 < baseStart_666537 := by decide
  rcases family_descends (prefixWord ++ tailWord_666537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666554 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_666554 : Nat := 118140960795 + 666554 * 2 ^ 59
def prefixEnd_666554 : Nat := 4983230072969 + 3 ^ 40 * 666554 * 2
def baseEnd_666554 : Nat := 152116704078706816937591

theorem tailTrace_666554 : CollatzResearch.WordTrace tailWord_666554 prefixEnd_666554 152116704078706816937591 := by
  unfold tailWord_666554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077805406799042801293679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16207481084797447470116477 6077805406799042801293679)
  ·
    refine ⟨9116708110198564201940519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6077805406799042801293679 9116708110198564201940519)
    ·
      refine ⟨13675062165297846302910779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9116708110198564201940519 13675062165297846302910779)
      ·
        refine ⟨20512593247946769454366169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13675062165297846302910779 20512593247946769454366169)
        ·
          refine ⟨15384444935960077090774627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20512593247946769454366169 15384444935960077090774627)
          ·
            refine ⟨23076667403940115636161941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15384444935960077090774627 23076667403940115636161941)
            ·
              refine ⟨1081718784559692920445091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23076667403940115636161941 1081718784559692920445091)
              ·
                refine ⟨1622578176839539380667637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081718784559692920445091 1622578176839539380667637)
                ·
                  refine ⟨152116704078706816937591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1622578176839539380667637 152116704078706816937591)
                  ·
                    rfl

theorem cell21_666554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_666554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666554 prefixEnd_666554 := by exact prefixLift 666554
  have htrace : WordTrace (prefixWord ++ tailWord_666554) baseStart_666554 baseEnd_666554 := by
    simpa [prefixWord, tailWord_666554, baseEnd_666554] using wordTrace_append hprefix tailTrace_666554
  have hstable : (prefixWord ++ tailWord_666554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666554).length < 2 ^ (prefixWord ++ tailWord_666554).sum := by decide
  have hdescent : baseEnd_666554 < baseStart_666554 := by decide
  rcases family_descends (prefixWord ++ tailWord_666554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666599 : List Nat := [1, 1, 5, 2, 2, 1, 9]
def baseStart_666599 : Nat := 118140960795 + 666599 * 2 ^ 59
def prefixEnd_666599 : Nat := 4983230072969 + 3 ^ 40 * 666599 * 2
def baseEnd_666599 : Nat := 16902997076866304298611

theorem tailTrace_666599 : CollatzResearch.WordTrace tailWord_666599 prefixEnd_666599 16902997076866304298611 := by
  unfold tailWord_666599
  simp only [CollatzResearch.WordTrace]
  refine ⟨24312862912033143890562851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16208575274688762593708567 24312862912033143890562851)
  ·
    refine ⟨36469294368049715835844277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24312862912033143890562851 36469294368049715835844277)
    ·
      refine ⟨3418996347004660859610401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36469294368049715835844277 3418996347004660859610401)
      ·
        refine ⟨2564247260253495644707801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3418996347004660859610401 2564247260253495644707801)
        ·
          refine ⟨1923185445190121733530851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564247260253495644707801 1923185445190121733530851)
          ·
            refine ⟨2884778167785182600296277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923185445190121733530851 2884778167785182600296277)
            ·
              refine ⟨16902997076866304298611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2884778167785182600296277 16902997076866304298611)
              ·
                rfl

theorem cell21_666599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 9].length) (baseStart_666599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666599 prefixEnd_666599 := by exact prefixLift 666599
  have htrace : WordTrace (prefixWord ++ tailWord_666599) baseStart_666599 baseEnd_666599 := by
    simpa [prefixWord, tailWord_666599, baseEnd_666599] using wordTrace_append hprefix tailTrace_666599
  have hstable : (prefixWord ++ tailWord_666599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666599).length < 2 ^ (prefixWord ++ tailWord_666599).sum := by decide
  have hdescent : baseEnd_666599 < baseStart_666599 := by decide
  rcases family_descends (prefixWord ++ tailWord_666599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666661 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 4]
def baseStart_666661 : Nat := 118140960795 + 666661 * 2 ^ 59
def prefixEnd_666661 : Nat := 4983230072969 + 3 ^ 40 * 666661 * 2
def baseEnd_666661 : Nat := 152141122936498408654039

theorem tailTrace_666661 : CollatzResearch.WordTrace tailWord_666661 prefixEnd_666661 152141122936498408654039 := by
  unfold tailWord_666661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24315124237808528479319837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16210082825205685652879891 24315124237808528479319837)
  ·
    refine ⟨9118171589178198179744939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24315124237808528479319837 9118171589178198179744939)
    ·
      refine ⟨13677257383767297269617409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9118171589178198179744939 13677257383767297269617409)
      ·
        refine ⟨10257943037825472952213057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13677257383767297269617409 10257943037825472952213057)
        ·
          refine ⟨7693457278369104714159793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10257943037825472952213057 7693457278369104714159793)
          ·
            refine ⟨5770092958776828535619845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7693457278369104714159793 5770092958776828535619845)
            ·
              refine ⟨1081892429770655350428721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5770092958776828535619845 1081892429770655350428721)
              ·
                refine ⟨811419322327991512821541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081892429770655350428721 811419322327991512821541)
                ·
                  refine ⟨152141122936498408654039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811419322327991512821541 152141122936498408654039)
                  ·
                    rfl

theorem cell21_666661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_666661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666661 prefixEnd_666661 := by exact prefixLift 666661
  have htrace : WordTrace (prefixWord ++ tailWord_666661) baseStart_666661 baseEnd_666661 := by
    simpa [prefixWord, tailWord_666661, baseEnd_666661] using wordTrace_append hprefix tailTrace_666661
  have hstable : (prefixWord ++ tailWord_666661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666661).length < 2 ^ (prefixWord ++ tailWord_666661).sum := by decide
  have hdescent : baseEnd_666661 < baseStart_666661 := by decide
  rcases family_descends (prefixWord ++ tailWord_666661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666678 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_666678 : Nat := 118140960795 + 666678 * 2 ^ 59
def prefixEnd_666678 : Nat := 4983230072969 + 3 ^ 40 * 666678 * 2
def baseEnd_666678 : Nat := 152145002568110156870671

theorem tailTrace_666678 : CollatzResearch.WordTrace tailWord_666678 prefixEnd_666678 152145002568110156870671 := by
  unfold tailWord_666678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519734017421683773918043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16210496185831293588459125 1519734017421683773918043)
  ·
    refine ⟨2279601026132525660877065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519734017421683773918043 2279601026132525660877065)
    ·
      refine ⟨1709700769599394245657799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2279601026132525660877065 1709700769599394245657799)
      ·
        refine ⟨2564551154399091368486699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709700769599394245657799 2564551154399091368486699)
        ·
          refine ⟨3846826731598637052730049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564551154399091368486699 3846826731598637052730049)
          ·
            refine ⟨2885120048698977789547537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3846826731598637052730049 2885120048698977789547537)
            ·
              refine ⟨2163840036524233342160653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885120048698977789547537 2163840036524233342160653)
              ·
                refine ⟨811440013696587503310245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2163840036524233342160653 811440013696587503310245)
                ·
                  refine ⟨152145002568110156870671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811440013696587503310245 152145002568110156870671)
                  ·
                    rfl

theorem cell21_666678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_666678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666678 prefixEnd_666678 := by exact prefixLift 666678
  have htrace : WordTrace (prefixWord ++ tailWord_666678) baseStart_666678 baseEnd_666678 := by
    simpa [prefixWord, tailWord_666678, baseEnd_666678] using wordTrace_append hprefix tailTrace_666678
  have hstable : (prefixWord ++ tailWord_666678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666678).length < 2 ^ (prefixWord ++ tailWord_666678).sum := by decide
  have hdescent : baseEnd_666678 < baseStart_666678 := by decide
  rcases family_descends (prefixWord ++ tailWord_666678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666720 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_666720 : Nat := 118140960795 + 666720 * 2 ^ 59
def prefixEnd_666720 : Nat := 4983230072969 + 3 ^ 40 * 666720 * 2
def baseEnd_666720 : Nat := 152154587540327417170585

theorem tailTrace_666720 : CollatzResearch.WordTrace tailWord_666720 prefixEnd_666720 152154587540327417170585 := by
  unfold tailWord_666720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158638072297390777858807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16211517429729854370478409 12158638072297390777858807)
  ·
    refine ⟨18237957108446086166788211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12158638072297390777858807 18237957108446086166788211)
    ·
      refine ⟨27356935662669129250182317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18237957108446086166788211 27356935662669129250182317)
      ·
        refine ⟨10258850873500923468818369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27356935662669129250182317 10258850873500923468818369)
        ·
          refine ⟨7694138155125692601613777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10258850873500923468818369 7694138155125692601613777)
          ·
            refine ⟨5770603616344269451210333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7694138155125692601613777 5770603616344269451210333)
            ·
              refine ⟨2163976356129101044203875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5770603616344269451210333 2163976356129101044203875)
              ·
                refine ⟨3245964534193651566305813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163976356129101044203875 3245964534193651566305813)
                ·
                  refine ⟨152154587540327417170585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3245964534193651566305813 152154587540327417170585)
                  ·
                    rfl

theorem cell21_666720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_666720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666720 prefixEnd_666720 := by exact prefixLift 666720
  have htrace : WordTrace (prefixWord ++ tailWord_666720) baseStart_666720 baseEnd_666720 := by
    simpa [prefixWord, tailWord_666720, baseEnd_666720] using wordTrace_append hprefix tailTrace_666720
  have hstable : (prefixWord ++ tailWord_666720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666720).length < 2 ^ (prefixWord ++ tailWord_666720).sum := by decide
  have hdescent : baseEnd_666720 < baseStart_666720 := by decide
  rcases family_descends (prefixWord ++ tailWord_666720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666757 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 3]
def baseStart_666757 : Nat := 118140960795 + 666757 * 2 ^ 59
def prefixEnd_666757 : Nat := 4983230072969 + 3 ^ 40 * 666757 * 2
def baseEnd_666757 : Nat := 152163031444423575053843

theorem tailTrace_666757 : CollatzResearch.WordTrace tailWord_666757 prefixEnd_666757 152163031444423575053843 := by
  unfold tailWord_666757
  simp only [CollatzResearch.WordTrace]
  refine ⟨24318625645460736874814525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16212417096973824583209683 24318625645460736874814525)
  ·
    refine ⟨9119484617047776328055447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24318625645460736874814525 9119484617047776328055447)
    ·
      refine ⟨13679226925571664492083171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119484617047776328055447 13679226925571664492083171)
      ·
        refine ⟨20518840388357496738124757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13679226925571664492083171 20518840388357496738124757)
        ·
          refine ⟨480910321602128829799799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20518840388357496738124757 480910321602128829799799)
          ·
            refine ⟨721365482403193244699699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480910321602128829799799 721365482403193244699699)
            ·
              refine ⟨1082048223604789867049549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721365482403193244699699 1082048223604789867049549)
              ·
                refine ⟨405768083851796200143581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1082048223604789867049549 405768083851796200143581)
                ·
                  refine ⟨152163031444423575053843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405768083851796200143581 152163031444423575053843)
                  ·
                    rfl

theorem cell21_666757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_666757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666757 prefixEnd_666757 := by exact prefixLift 666757
  have htrace : WordTrace (prefixWord ++ tailWord_666757) baseStart_666757 baseEnd_666757 := by
    simpa [prefixWord, tailWord_666757, baseEnd_666757] using wordTrace_append hprefix tailTrace_666757
  have hstable : (prefixWord ++ tailWord_666757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666757).length < 2 ^ (prefixWord ++ tailWord_666757).sum := by decide
  have hdescent : baseEnd_666757 < baseStart_666757 := by decide
  rcases family_descends (prefixWord ++ tailWord_666757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666830 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_666830 : Nat := 118140960795 + 666830 * 2 ^ 59
def prefixEnd_666830 : Nat := 4983230072969 + 3 ^ 40 * 666830 * 2
def baseEnd_666830 : Nat := 152179691038991670337027

theorem tailTrace_666830 : CollatzResearch.WordTrace tailWord_666830 prefixEnd_666830 152179691038991670337027 := by
  unfold tailWord_666830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040161021774533792777743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16214192116130846894814629 3040161021774533792777743)
  ·
    refine ⟨4560241532661800689166615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3040161021774533792777743 4560241532661800689166615)
    ·
      refine ⟨6840362298992701033749923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560241532661800689166615 6840362298992701033749923)
      ·
        refine ⟨10260543448489051550624885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840362298992701033749923 10260543448489051550624885)
        ·
          refine ⟨961925948295848582871083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10260543448489051550624885 961925948295848582871083)
          ·
            refine ⟨1442888922443772874306625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961925948295848582871083 1442888922443772874306625)
            ·
              refine ⟨1082166691832829655729969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442888922443772874306625 1082166691832829655729969)
              ·
                refine ⟨811625018874622241797477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082166691832829655729969 811625018874622241797477)
                ·
                  refine ⟨152179691038991670337027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811625018874622241797477 152179691038991670337027)
                  ·
                    rfl

theorem cell21_666830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_666830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666830 prefixEnd_666830 := by exact prefixLift 666830
  have htrace : WordTrace (prefixWord ++ tailWord_666830) baseStart_666830 baseEnd_666830 := by
    simpa [prefixWord, tailWord_666830, baseEnd_666830] using wordTrace_append hprefix tailTrace_666830
  have hstable : (prefixWord ++ tailWord_666830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666830).length < 2 ^ (prefixWord ++ tailWord_666830).sum := by decide
  have hdescent : baseEnd_666830 < baseStart_666830 := by decide
  rcases family_descends (prefixWord ++ tailWord_666830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666841 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_666841 : Nat := 118140960795 + 666841 * 2 ^ 59
def prefixEnd_666841 : Nat := 4983230072969 + 3 ^ 40 * 666841 * 2
def baseEnd_666841 : Nat := 152182201388858095653671

theorem tailTrace_666841 : CollatzResearch.WordTrace tailWord_666841 prefixEnd_666841 152182201388858095653671 := by
  unfold tailWord_666841
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321689377156419220872377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16214459584770946147248251 24321689377156419220872377)
  ·
    refine ⟨18241267032867314415654283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24321689377156419220872377 18241267032867314415654283)
    ·
      refine ⟨27361900549300971623481425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18241267032867314415654283 27361900549300971623481425)
      ·
        refine ⟨20521425411975728717611069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27361900549300971623481425 20521425411975728717611069)
        ·
          refine ⟨7695534529490898269104151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20521425411975728717611069 7695534529490898269104151)
          ·
            refine ⟨11543301794236347403656227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695534529490898269104151 11543301794236347403656227)
            ·
              refine ⟨17314952691354521105484341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543301794236347403656227 17314952691354521105484341)
              ·
                refine ⟨1623276814814486353639157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17314952691354521105484341 1623276814814486353639157)
                ·
                  refine ⟨152182201388858095653671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1623276814814486353639157 152182201388858095653671)
                  ·
                    rfl

theorem cell21_666841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_666841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666841 prefixEnd_666841 := by exact prefixLift 666841
  have htrace : WordTrace (prefixWord ++ tailWord_666841) baseStart_666841 baseEnd_666841 := by
    simpa [prefixWord, tailWord_666841, baseEnd_666841] using wordTrace_append hprefix tailTrace_666841
  have hstable : (prefixWord ++ tailWord_666841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666841).length < 2 ^ (prefixWord ++ tailWord_666841).sum := by decide
  have hdescent : baseEnd_666841 < baseStart_666841 := by decide
  rcases family_descends (prefixWord ++ tailWord_666841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666858 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_666858 : Nat := 118140960795 + 666858 * 2 ^ 59
def prefixEnd_666858 : Nat := 4983230072969 + 3 ^ 40 * 666858 * 2
def baseEnd_666858 : Nat := 152186081020469843870303

theorem tailTrace_666858 : CollatzResearch.WordTrace tailWord_666858 prefixEnd_666858 152186081020469843870303 := by
  unfold tailWord_666858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080577354523707781060307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16214872945396554082827485 6080577354523707781060307)
  ·
    refine ⟨9120866031785561671590461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6080577354523707781060307 9120866031785561671590461)
    ·
      refine ⟨3420324761919585626846423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9120866031785561671590461 3420324761919585626846423)
      ·
        refine ⟨5130487142879378440269635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3420324761919585626846423 5130487142879378440269635)
        ·
          refine ⟨7695730714319067660404453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130487142879378440269635 7695730714319067660404453)
          ·
            refine ⟨1442949508934825186325835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7695730714319067660404453 1442949508934825186325835)
            ·
              refine ⟨2164424263402237779488753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442949508934825186325835 2164424263402237779488753)
              ·
                refine ⟨1623318197551678334616565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2164424263402237779488753 1623318197551678334616565)
                ·
                  refine ⟨152186081020469843870303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1623318197551678334616565 152186081020469843870303)
                  ·
                    rfl

theorem cell21_666858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_666858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666858 prefixEnd_666858 := by exact prefixLift 666858
  have htrace : WordTrace (prefixWord ++ tailWord_666858) baseStart_666858 baseEnd_666858 := by
    simpa [prefixWord, tailWord_666858, baseEnd_666858] using wordTrace_append hprefix tailTrace_666858
  have hstable : (prefixWord ++ tailWord_666858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666858).length < 2 ^ (prefixWord ++ tailWord_666858).sum := by decide
  have hdescent : baseEnd_666858 < baseStart_666858 := by decide
  rcases family_descends (prefixWord ++ tailWord_666858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666906 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_666906 : Nat := 118140960795 + 666906 * 2 ^ 59
def prefixEnd_666906 : Nat := 4983230072969 + 3 ^ 40 * 666906 * 2
def baseEnd_666906 : Nat := 152197035274432427070205

theorem tailTrace_666906 : CollatzResearch.WordTrace tailWord_666906 prefixEnd_666906 152197035274432427070205 := by
  unfold tailWord_666906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081015030480233830497143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16216040081280623547992381 6081015030480233830497143)
  ·
    refine ⟨9121522545720350745745715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6081015030480233830497143 9121522545720350745745715)
    ·
      refine ⟨13682283818580526118618573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9121522545720350745745715 13682283818580526118618573)
      ·
        refine ⟨5130856431967697294481965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13682283818580526118618573 5130856431967697294481965)
        ·
          refine ⟨1924071161987886485430737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5130856431967697294481965 1924071161987886485430737)
          ·
            refine ⟨1443053371490914864073053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1924071161987886485430737 1443053371490914864073053)
            ·
              refine ⟨541145014309093074027395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1443053371490914864073053 541145014309093074027395)
              ·
                refine ⟨811717521463639611041093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541145014309093074027395 811717521463639611041093)
                ·
                  refine ⟨152197035274432427070205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811717521463639611041093 152197035274432427070205)
                  ·
                    rfl

theorem cell21_666906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_666906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666906 prefixEnd_666906 := by exact prefixLift 666906
  have htrace : WordTrace (prefixWord ++ tailWord_666906) baseStart_666906 baseEnd_666906 := by
    simpa [prefixWord, tailWord_666906, baseEnd_666906] using wordTrace_append hprefix tailTrace_666906
  have hstable : (prefixWord ++ tailWord_666906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666906).length < 2 ^ (prefixWord ++ tailWord_666906).sum := by decide
  have hdescent : baseEnd_666906 < baseStart_666906 := by decide
  rcases family_descends (prefixWord ++ tailWord_666906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666920 : List Nat := [2, 1, 5, 1, 2, 1, 4, 5]
def baseStart_666920 : Nat := 118140960795 + 666920 * 2 ^ 59
def prefixEnd_666920 : Nat := 4983230072969 + 3 ^ 40 * 666920 * 2
def baseEnd_666920 : Nat := 50733410088390504612281

theorem tailTrace_666920 : CollatzResearch.WordTrace tailWord_666920 prefixEnd_666920 50733410088390504612281 := by
  unfold tailWord_666920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12162285371935107856499107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16216380495913477141998809 12162285371935107856499107)
  ·
    refine ⟨18243428057902661784748661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12162285371935107856499107 18243428057902661784748661)
    ·
      refine ⟨1710321380428374542320187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18243428057902661784748661 1710321380428374542320187)
      ·
        refine ⟨2565482070642561813480281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710321380428374542320187 2565482070642561813480281)
        ·
          refine ⟨1924111552981921360110211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2565482070642561813480281 1924111552981921360110211)
          ·
            refine ⟨2886167329472882040165317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924111552981921360110211 2886167329472882040165317)
            ·
              refine ⟨541156374276165382530997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2886167329472882040165317 541156374276165382530997)
              ·
                refine ⟨50733410088390504612281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 541156374276165382530997 50733410088390504612281)
                ·
                  rfl

theorem cell21_666920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_666920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666920 prefixEnd_666920 := by exact prefixLift 666920
  have htrace : WordTrace (prefixWord ++ tailWord_666920) baseStart_666920 baseEnd_666920 := by
    simpa [prefixWord, tailWord_666920, baseEnd_666920] using wordTrace_append hprefix tailTrace_666920
  have hstable : (prefixWord ++ tailWord_666920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666920).length < 2 ^ (prefixWord ++ tailWord_666920).sum := by decide
  have hdescent : baseEnd_666920 < baseStart_666920 := by decide
  rcases family_descends (prefixWord ++ tailWord_666920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666957 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 4]
def baseStart_666957 : Nat := 118140960795 + 666957 * 2 ^ 59
def prefixEnd_666957 : Nat := 4983230072969 + 3 ^ 40 * 666957 * 2
def baseEnd_666957 : Nat := 152208674169267671720101

theorem tailTrace_666957 : CollatzResearch.WordTrace tailWord_666957 prefixEnd_666957 152208674169267671720101 := by
  unfold tailWord_666957
  simp only [CollatzResearch.WordTrace]
  refine ⟨24325920244736171032095125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16217280163157447354730083 24325920244736171032095125)
  ·
    refine ⟨1140277511472008017129459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24325920244736171032095125 1140277511472008017129459)
    ·
      refine ⟨1710416267208012025694189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140277511472008017129459 1710416267208012025694189)
      ·
        refine ⟨641406100203004509635321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1710416267208012025694189 641406100203004509635321)
        ·
          refine ⟨481054575152253382226491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641406100203004509635321 481054575152253382226491)
          ·
            refine ⟨721581862728380073339737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481054575152253382226491 721581862728380073339737)
            ·
              refine ⟨541186397046285055004803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721581862728380073339737 541186397046285055004803)
              ·
                refine ⟨811779595569427582507205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541186397046285055004803 811779595569427582507205)
                ·
                  refine ⟨152208674169267671720101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811779595569427582507205 152208674169267671720101)
                  ·
                    rfl

theorem cell21_666957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_666957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666957 prefixEnd_666957 := by exact prefixLift 666957
  have htrace : WordTrace (prefixWord ++ tailWord_666957) baseStart_666957 baseEnd_666957 := by
    simpa [prefixWord, tailWord_666957, baseEnd_666957] using wordTrace_append hprefix tailTrace_666957
  have hstable : (prefixWord ++ tailWord_666957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666957).length < 2 ^ (prefixWord ++ tailWord_666957).sum := by decide
  have hdescent : baseEnd_666957 < baseStart_666957 := by decide
  rcases family_descends (prefixWord ++ tailWord_666957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666965 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 4]
def baseStart_666965 : Nat := 118140960795 + 666965 * 2 ^ 59
def prefixEnd_666965 : Nat := 4983230072969 + 3 ^ 40 * 666965 * 2
def baseEnd_666965 : Nat := 152210499878261435586751

theorem tailTrace_666965 : CollatzResearch.WordTrace tailWord_666965 prefixEnd_666965 152210499878261435586751 := by
  unfold tailWord_666965
  simp only [CollatzResearch.WordTrace]
  refine ⟨24326212028707188398386349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16217474685804792265590899 24326212028707188398386349)
  ·
    refine ⟨9122329510765195649394881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24326212028707188398386349 9122329510765195649394881)
    ·
      refine ⟨6841747133073896737046161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9122329510765195649394881 6841747133073896737046161)
      ·
        refine ⟨5131310349805422552784621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6841747133073896737046161 5131310349805422552784621)
        ·
          refine ⟨1924241381177033457294233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5131310349805422552784621 1924241381177033457294233)
          ·
            refine ⟨1443181035882775092970675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1924241381177033457294233 1443181035882775092970675)
            ·
              refine ⟨2164771553824162639456013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443181035882775092970675 2164771553824162639456013)
              ·
                refine ⟨811789332684060989796005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164771553824162639456013 811789332684060989796005)
                ·
                  refine ⟨152210499878261435586751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811789332684060989796005 152210499878261435586751)
                  ·
                    rfl

theorem cell21_666965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_666965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_666965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_666965 prefixEnd_666965 := by exact prefixLift 666965
  have htrace : WordTrace (prefixWord ++ tailWord_666965) baseStart_666965 baseEnd_666965 := by
    simpa [prefixWord, tailWord_666965, baseEnd_666965] using wordTrace_append hprefix tailTrace_666965
  have hstable : (prefixWord ++ tailWord_666965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666965).length < 2 ^ (prefixWord ++ tailWord_666965).sum := by decide
  have hdescent : baseEnd_666965 < baseStart_666965 := by decide
  rcases family_descends (prefixWord ++ tailWord_666965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667162 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_667162 : Nat := 118140960795 + 667162 * 2 ^ 59
def prefixEnd_667162 : Nat := 4983230072969 + 3 ^ 40 * 667162 * 2
def baseEnd_667162 : Nat := 152255457962232870803015

theorem tailTrace_667162 : CollatzResearch.WordTrace tailWord_667162 prefixEnd_667162 152255457962232870803015 := by
  unfold tailWord_667162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083349302248372760826935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16222264805995660695538493 6083349302248372760826935)
  ·
    refine ⟨9125023953372559141240403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6083349302248372760826935 9125023953372559141240403)
    ·
      refine ⟨13687535930058838711860605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9125023953372559141240403 13687535930058838711860605)
      ·
        refine ⟨5132825973772064516947727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13687535930058838711860605 5132825973772064516947727)
        ·
          refine ⟨7699238960658096775421591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132825973772064516947727 7699238960658096775421591)
          ·
            refine ⟨11548858440987145163132387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7699238960658096775421591 11548858440987145163132387)
            ·
              refine ⟨17323287661480717744698581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11548858440987145163132387 17323287661480717744698581)
              ·
                refine ⟨406014554565954322141373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17323287661480717744698581 406014554565954322141373)
                ·
                  refine ⟨152255457962232870803015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406014554565954322141373 152255457962232870803015)
                  ·
                    rfl

theorem cell21_667162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_667162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667162 prefixEnd_667162 := by exact prefixLift 667162
  have htrace : WordTrace (prefixWord ++ tailWord_667162) baseStart_667162 baseEnd_667162 := by
    simpa [prefixWord, tailWord_667162, baseEnd_667162] using wordTrace_append hprefix tailTrace_667162
  have hstable : (prefixWord ++ tailWord_667162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667162).length < 2 ^ (prefixWord ++ tailWord_667162).sum := by decide
  have hdescent : baseEnd_667162 < baseStart_667162 := by decide
  rcases family_descends (prefixWord ++ tailWord_667162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667280 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_667280 : Nat := 118140960795 + 667280 * 2 ^ 59
def prefixEnd_667280 : Nat := 4983230072969 + 3 ^ 40 * 667280 * 2
def baseEnd_667280 : Nat := 152282387169890887836107

theorem tailTrace_667280 : CollatzResearch.WordTrace tailWord_667280 prefixEnd_667280 152282387169890887836107 := by
  unfold tailWord_667280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168850511282998598051647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16225134015043998130735529 12168850511282998598051647)
  ·
    refine ⟨18253275766924497897077471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12168850511282998598051647 18253275766924497897077471)
    ·
      refine ⟨27379913650386746845616207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18253275766924497897077471 27379913650386746845616207)
      ·
        refine ⟨41069870475580120268424311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27379913650386746845616207 41069870475580120268424311)
        ·
          refine ⟨61604805713370180402636467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41069870475580120268424311 61604805713370180402636467)
          ·
            refine ⟨92407208570055270603954701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61604805713370180402636467 92407208570055270603954701)
            ·
              refine ⟨34652703213770726476483013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92407208570055270603954701 34652703213770726476483013)
              ·
                refine ⟨6497381852582011214340565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34652703213770726476483013 6497381852582011214340565)
                ·
                  refine ⟨152282387169890887836107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6497381852582011214340565 152282387169890887836107)
                  ·
                    rfl

theorem cell21_667280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_667280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667280 prefixEnd_667280 := by exact prefixLift 667280
  have htrace : WordTrace (prefixWord ++ tailWord_667280) baseStart_667280 baseEnd_667280 := by
    simpa [prefixWord, tailWord_667280, baseEnd_667280] using wordTrace_append hprefix tailTrace_667280
  have hstable : (prefixWord ++ tailWord_667280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667280).length < 2 ^ (prefixWord ++ tailWord_667280).sum := by decide
  have hdescent : baseEnd_667280 < baseStart_667280 := by decide
  rcases family_descends (prefixWord ++ tailWord_667280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667348 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_667348 : Nat := 118140960795 + 667348 * 2 ^ 59
def prefixEnd_667348 : Nat := 4983230072969 + 3 ^ 40 * 667348 * 2
def baseEnd_667348 : Nat := 152297905696337880702635

theorem tailTrace_667348 : CollatzResearch.WordTrace tailWord_667348 prefixEnd_667348 152297905696337880702635 := by
  unfold tailWord_667348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12170090593159822404789349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16226787457546429873052465 12170090593159822404789349)
  ·
    refine ⟨2281891986217466700898003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12170090593159822404789349 2281891986217466700898003)
    ·
      refine ⟨3422837979326200051347005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2281891986217466700898003 3422837979326200051347005)
      ·
        refine ⟨1283564242247325019255127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3422837979326200051347005 1283564242247325019255127)
        ·
          refine ⟨1925346363370987528882691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283564242247325019255127 1925346363370987528882691)
          ·
            refine ⟨2888019545056481293324037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925346363370987528882691 2888019545056481293324037)
            ·
              refine ⟨541503664698090242498257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2888019545056481293324037 541503664698090242498257)
              ·
                refine ⟨406127748523567681873693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541503664698090242498257 406127748523567681873693)
                ·
                  refine ⟨152297905696337880702635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406127748523567681873693 152297905696337880702635)
                  ·
                    rfl

theorem cell21_667348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_667348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667348 prefixEnd_667348 := by exact prefixLift 667348
  have htrace : WordTrace (prefixWord ++ tailWord_667348) baseStart_667348 baseEnd_667348 := by
    simpa [prefixWord, tailWord_667348, baseEnd_667348] using wordTrace_append hprefix tailTrace_667348
  have hstable : (prefixWord ++ tailWord_667348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667348).length < 2 ^ (prefixWord ++ tailWord_667348).sum := by decide
  have hdescent : baseEnd_667348 < baseStart_667348 := by decide
  rcases family_descends (prefixWord ++ tailWord_667348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667373 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_667373 : Nat := 118140960795 + 667373 * 2 ^ 59
def prefixEnd_667373 : Nat := 4983230072969 + 3 ^ 40 * 667373 * 2
def baseEnd_667373 : Nat := 152303611036943392785917

theorem tailTrace_667373 : CollatzResearch.WordTrace tailWord_667373 prefixEnd_667373 152303611036943392785917 := by
  unfold tailWord_667373
  simp only [CollatzResearch.WordTrace]
  refine ⟨24341093011229074079238773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16227395340819382719492515 24341093011229074079238773)
  ·
    refine ⟨2281977469802725694928635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24341093011229074079238773 2281977469802725694928635)
    ·
      refine ⟨3422966204704088542392953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2281977469802725694928635 3422966204704088542392953)
      ·
        refine ⟨2567224653528066406794715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3422966204704088542392953 2567224653528066406794715)
        ·
          refine ⟨3850836980292099610192073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567224653528066406794715 3850836980292099610192073)
          ·
            refine ⟨2888127735219074707644055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3850836980292099610192073 2888127735219074707644055)
            ·
              refine ⟨4332191602828612061466083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2888127735219074707644055 4332191602828612061466083)
              ·
                refine ⟨6498287404242918092199125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332191602828612061466083 6498287404242918092199125)
                ·
                  refine ⟨152303611036943392785917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6498287404242918092199125 152303611036943392785917)
                  ·
                    rfl

theorem cell21_667373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_667373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667373 prefixEnd_667373 := by exact prefixLift 667373
  have htrace : WordTrace (prefixWord ++ tailWord_667373) baseStart_667373 baseEnd_667373 := by
    simpa [prefixWord, tailWord_667373, baseEnd_667373] using wordTrace_append hprefix tailTrace_667373
  have hstable : (prefixWord ++ tailWord_667373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667373).length < 2 ^ (prefixWord ++ tailWord_667373).sum := by decide
  have hdescent : baseEnd_667373 < baseStart_667373 := by decide
  rcases family_descends (prefixWord ++ tailWord_667373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667404 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_667404 : Nat := 118140960795 + 667404 * 2 ^ 59
def prefixEnd_667404 : Nat := 4983230072969 + 3 ^ 40 * 667404 * 2
def baseEnd_667404 : Nat := 152310685659294227769187

theorem tailTrace_667404 : CollatzResearch.WordTrace tailWord_667404 prefixEnd_667404 152310685659294227769187 := by
  unfold tailWord_667404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12171111837058383186808633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16228149116077844249078177 12171111837058383186808633)
  ·
    refine ⟨9128333877793787390106475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12171111837058383186808633 9128333877793787390106475)
    ·
      refine ⟨13692500816690681085159713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9128333877793787390106475 13692500816690681085159713)
      ·
        refine ⟨10269375612518010813869785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13692500816690681085159713 10269375612518010813869785)
        ·
          refine ⟨7702031709388508110402339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10269375612518010813869785 7702031709388508110402339)
          ·
            refine ⟨11553047564082762165603509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7702031709388508110402339 11553047564082762165603509)
            ·
              refine ⟨1083098209132758953025329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11553047564082762165603509 1083098209132758953025329)
              ·
                refine ⟨812323656849569214768997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083098209132758953025329 812323656849569214768997)
                ·
                  refine ⟨152310685659294227769187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 812323656849569214768997 152310685659294227769187)
                  ·
                    rfl

theorem cell21_667404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_667404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667404 prefixEnd_667404 := by exact prefixLift 667404
  have htrace : WordTrace (prefixWord ++ tailWord_667404) baseStart_667404 baseEnd_667404 := by
    simpa [prefixWord, tailWord_667404, baseEnd_667404] using wordTrace_append hprefix tailTrace_667404
  have hstable : (prefixWord ++ tailWord_667404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667404).length < 2 ^ (prefixWord ++ tailWord_667404).sum := by decide
  have hdescent : baseEnd_667404 < baseStart_667404 := by decide
  rcases family_descends (prefixWord ++ tailWord_667404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667463 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_667463 : Nat := 118140960795 + 667463 * 2 ^ 59
def prefixEnd_667463 : Nat := 4983230072969 + 3 ^ 40 * 667463 * 2
def baseEnd_667463 : Nat := 152324150263123236285733

theorem tailTrace_667463 : CollatzResearch.WordTrace tailWord_667463 prefixEnd_667463 152324150263123236285733 := by
  unfold tailWord_667463
  simp only [CollatzResearch.WordTrace]
  refine ⟨24344375580903019450015043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16229583720602012966676695 24344375580903019450015043)
  ·
    refine ⟨36516563371354529175022565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24344375580903019450015043 36516563371354529175022565)
    ·
      refine ⟨6846855632128974220316731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36516563371354529175022565 6846855632128974220316731)
      ·
        refine ⟨10270283448193461330475097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6846855632128974220316731 10270283448193461330475097)
        ·
          refine ⟨7702712586145095997856323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10270283448193461330475097 7702712586145095997856323)
          ·
            refine ⟨11554068879217643996784485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7702712586145095997856323 11554068879217643996784485)
            ·
              refine ⟨2166387914853308249397091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11554068879217643996784485 2166387914853308249397091)
              ·
                refine ⟨3249581872279962374095637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166387914853308249397091 3249581872279962374095637)
                ·
                  refine ⟨152324150263123236285733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3249581872279962374095637 152324150263123236285733)
                  ·
                    rfl

theorem cell21_667463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_667463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667463 prefixEnd_667463 := by exact prefixLift 667463
  have htrace : WordTrace (prefixWord ++ tailWord_667463) baseStart_667463 baseEnd_667463 := by
    simpa [prefixWord, tailWord_667463, baseEnd_667463] using wordTrace_append hprefix tailTrace_667463
  have hstable : (prefixWord ++ tailWord_667463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667463).length < 2 ^ (prefixWord ++ tailWord_667463).sum := by decide
  have hdescent : baseEnd_667463 < baseStart_667463 := by decide
  rcases family_descends (prefixWord ++ tailWord_667463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667528 : List Nat := [2, 1, 3, 3, 4, 1, 1, 6]
def baseStart_667528 : Nat := 118140960795 + 667528 * 2 ^ 59
def prefixEnd_667528 : Nat := 4983230072969 + 3 ^ 40 * 667528 * 2
def baseEnd_667528 : Nat := 50779661382899189234089

theorem tailTrace_667528 : CollatzResearch.WordTrace tailWord_667528 prefixEnd_667528 50779661382899189234089 := by
  unfold tailWord_667528
  simp only [CollatzResearch.WordTrace]
  refine ⟨12173373162833767775565619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16231164217111690367420825 12173373162833767775565619)
  ·
    refine ⟨18260059744250651663348429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12173373162833767775565619 18260059744250651663348429)
    ·
      refine ⟨6847522404093994373755661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18260059744250651663348429 6847522404093994373755661)
      ·
        refine ⟨2567820901535247890158373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6847522404093994373755661 2567820901535247890158373)
        ·
          refine ⟨481466419037858979404695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2567820901535247890158373 481466419037858979404695)
          ·
            refine ⟨722199628556788469107043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481466419037858979404695 722199628556788469107043)
            ·
              refine ⟨1083299442835182703660565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722199628556788469107043 1083299442835182703660565)
              ·
                refine ⟨50779661382899189234089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1083299442835182703660565 50779661382899189234089)
                ·
                  rfl

theorem cell21_667528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_667528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667528 prefixEnd_667528 := by exact prefixLift 667528
  have htrace : WordTrace (prefixWord ++ tailWord_667528) baseStart_667528 baseEnd_667528 := by
    simpa [prefixWord, tailWord_667528, baseEnd_667528] using wordTrace_append hprefix tailTrace_667528
  have hstable : (prefixWord ++ tailWord_667528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667528).length < 2 ^ (prefixWord ++ tailWord_667528).sum := by decide
  have hdescent : baseEnd_667528 < baseStart_667528 := by decide
  rcases family_descends (prefixWord ++ tailWord_667528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667559 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 3]
def baseStart_667559 : Nat := 118140960795 + 667559 * 2 ^ 59
def prefixEnd_667559 : Nat := 4983230072969 + 3 ^ 40 * 667559 * 2
def baseEnd_667559 : Nat := 152346058771048402685537

theorem tailTrace_667559 : CollatzResearch.WordTrace tailWord_667559 prefixEnd_667559 152346058771048402685537 := by
  unfold tailWord_667559
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347876988555227845509731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16231917992370151897006487 24347876988555227845509731)
  ·
    refine ⟨36521815482832841768264597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24347876988555227845509731 36521815482832841768264597)
    ·
      refine ⟨1711960100757789457887403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36521815482832841768264597 1711960100757789457887403)
      ·
        refine ⟨2567940151136684186831105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711960100757789457887403 2567940151136684186831105)
        ·
          refine ⟨1925955113352513140123329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2567940151136684186831105 1925955113352513140123329)
          ·
            refine ⟨1444466335014384855092497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1925955113352513140123329 1444466335014384855092497)
            ·
              refine ⟨1083349751260788641319373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444466335014384855092497 1083349751260788641319373)
              ·
                refine ⟨406256156722795740494765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1083349751260788641319373 406256156722795740494765)
                ·
                  refine ⟨152346058771048402685537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406256156722795740494765 152346058771048402685537)
                  ·
                    rfl

theorem cell21_667559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 3].length) (baseStart_667559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667559 prefixEnd_667559 := by exact prefixLift 667559
  have htrace : WordTrace (prefixWord ++ tailWord_667559) baseStart_667559 baseEnd_667559 := by
    simpa [prefixWord, tailWord_667559, baseEnd_667559] using wordTrace_append hprefix tailTrace_667559
  have hstable : (prefixWord ++ tailWord_667559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667559).length < 2 ^ (prefixWord ++ tailWord_667559).sum := by decide
  have hdescent : baseEnd_667559 < baseStart_667559 := by decide
  rcases family_descends (prefixWord ++ tailWord_667559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667573 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 4]
def baseStart_667573 : Nat := 118140960795 + 667573 * 2 ^ 59
def prefixEnd_667573 : Nat := 4983230072969 + 3 ^ 40 * 667573 * 2
def baseEnd_667573 : Nat := 152349253761787489452175

theorem tailTrace_667573 : CollatzResearch.WordTrace tailWord_667573 prefixEnd_667573 152349253761787489452175 := by
  unfold tailWord_667573
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348387610504508236519373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16232258407003005491012915 24348387610504508236519373)
  ·
    refine ⟨9130645353939190588694765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24348387610504508236519373 9130645353939190588694765)
    ·
      refine ⟨3423992007727196470760537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9130645353939190588694765 3423992007727196470760537)
      ·
        refine ⟨2567994005795397353070403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3423992007727196470760537 2567994005795397353070403)
        ·
          refine ⟨3851991008693096029605605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567994005795397353070403 3851991008693096029605605)
          ·
            refine ⟨722248314129955505551051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3851991008693096029605605 722248314129955505551051)
            ·
              refine ⟨1083372471194933258326577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722248314129955505551051 1083372471194933258326577)
              ·
                refine ⟨812529353396199943744933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083372471194933258326577 812529353396199943744933)
                ·
                  refine ⟨152349253761787489452175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 812529353396199943744933 152349253761787489452175)
                  ·
                    rfl

theorem cell21_667573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_667573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667573 prefixEnd_667573 := by exact prefixLift 667573
  have htrace : WordTrace (prefixWord ++ tailWord_667573) baseStart_667573 baseEnd_667573 := by
    simpa [prefixWord, tailWord_667573, baseEnd_667573] using wordTrace_append hprefix tailTrace_667573
  have hstable : (prefixWord ++ tailWord_667573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667573).length < 2 ^ (prefixWord ++ tailWord_667573).sum := by decide
  have hdescent : baseEnd_667573 < baseStart_667573 := by decide
  rcases family_descends (prefixWord ++ tailWord_667573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667615 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_667615 : Nat := 118140960795 + 667615 * 2 ^ 59
def prefixEnd_667615 : Nat := 4983230072969 + 3 ^ 40 * 667615 * 2
def baseEnd_667615 : Nat := 152358838734004749752089

theorem tailTrace_667615 : CollatzResearch.WordTrace tailWord_667615 prefixEnd_667615 152358838734004749752089 := by
  unfold tailWord_667615
  simp only [CollatzResearch.WordTrace]
  refine ⟨24349919476352349409548299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16233279650901566273032199 24349919476352349409548299)
  ·
    refine ⟨36524879214528524114322449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24349919476352349409548299 36524879214528524114322449)
    ·
      refine ⟨27393659410896393085741837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36524879214528524114322449 27393659410896393085741837)
      ·
        refine ⟨10272622279086147407153189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27393659410896393085741837 10272622279086147407153189)
        ·
          refine ⟨1926116677328652638841223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10272622279086147407153189 1926116677328652638841223)
          ·
            refine ⟨2889175015992978958261835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926116677328652638841223 2889175015992978958261835)
            ·
              refine ⟨4333762523989468437392753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889175015992978958261835 4333762523989468437392753)
              ·
                refine ⟨3250321892992101328044565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333762523989468437392753 3250321892992101328044565)
                ·
                  refine ⟨152358838734004749752089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3250321892992101328044565 152358838734004749752089)
                  ·
                    rfl

theorem cell21_667615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_667615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667615 prefixEnd_667615 := by exact prefixLift 667615
  have htrace : WordTrace (prefixWord ++ tailWord_667615) baseStart_667615 baseEnd_667615 := by
    simpa [prefixWord, tailWord_667615, baseEnd_667615] using wordTrace_append hprefix tailTrace_667615
  have hstable : (prefixWord ++ tailWord_667615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667615).length < 2 ^ (prefixWord ++ tailWord_667615).sum := by decide
  have hdescent : baseEnd_667615 < baseStart_667615 := by decide
  rcases family_descends (prefixWord ++ tailWord_667615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667660 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_667660 : Nat := 118140960795 + 667660 * 2 ^ 59
def prefixEnd_667660 : Nat := 4983230072969 + 3 ^ 40 * 667660 * 2
def baseEnd_667660 : Nat := 152369108347094671501997

theorem tailTrace_667660 : CollatzResearch.WordTrace tailWord_667660 prefixEnd_667660 152369108347094671501997 := by
  unfold tailWord_667660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175780380594661047468217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16234373840792881396624289 12175780380594661047468217)
  ·
    refine ⟨9131835285445995785601163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12175780380594661047468217 9131835285445995785601163)
    ·
      refine ⟨13697752928168993678401745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9131835285445995785601163 13697752928168993678401745)
      ·
        refine ⟨10273314696126745258801309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13697752928168993678401745 10273314696126745258801309)
        ·
          refine ⟨3852493011047529472050491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10273314696126745258801309 3852493011047529472050491)
          ·
            refine ⟨5778739516571294208075737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852493011047529472050491 5778739516571294208075737)
            ·
              refine ⟨4334054637428470656056803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778739516571294208075737 4334054637428470656056803)
              ·
                refine ⟨6501081956142705984085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334054637428470656056803 6501081956142705984085205)
                ·
                  refine ⟨152369108347094671501997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6501081956142705984085205 152369108347094671501997)
                  ·
                    rfl

theorem cell21_667660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_667660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667660 prefixEnd_667660 := by exact prefixLift 667660
  have htrace : WordTrace (prefixWord ++ tailWord_667660) baseStart_667660 baseEnd_667660 := by
    simpa [prefixWord, tailWord_667660, baseEnd_667660] using wordTrace_append hprefix tailTrace_667660
  have hstable : (prefixWord ++ tailWord_667660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667660).length < 2 ^ (prefixWord ++ tailWord_667660).sum := by decide
  have hdescent : baseEnd_667660 < baseStart_667660 := by decide
  rcases family_descends (prefixWord ++ tailWord_667660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667742 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_667742 : Nat := 118140960795 + 667742 * 2 ^ 59
def prefixEnd_667742 : Nat := 4983230072969 + 3 ^ 40 * 667742 * 2
def baseEnd_667742 : Nat := 152387821864280751135163

theorem tailTrace_667742 : CollatzResearch.WordTrace tailWord_667742 prefixEnd_667742 152387821864280751135163 := by
  unfold tailWord_667742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3044318943361531262427685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16236367697928166732947653 3044318943361531262427685)
  ·
    refine ⟨570809801880287111705191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3044318943361531262427685 570809801880287111705191)
    ·
      refine ⟨856214702820430667557787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570809801880287111705191 856214702820430667557787)
      ·
        refine ⟨1284322054230646001336681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856214702820430667557787 1284322054230646001336681)
        ·
          refine ⟨963241540672984501002511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284322054230646001336681 963241540672984501002511)
          ·
            refine ⟨1444862311009476751503767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963241540672984501002511 1444862311009476751503767)
            ·
              refine ⟨2167293466514215127255651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444862311009476751503767 2167293466514215127255651)
              ·
                refine ⟨3250940199771322690883477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167293466514215127255651 3250940199771322690883477)
                ·
                  refine ⟨152387821864280751135163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3250940199771322690883477 152387821864280751135163)
                  ·
                    rfl

theorem cell21_667742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_667742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667742 prefixEnd_667742 := by exact prefixLift 667742
  have htrace : WordTrace (prefixWord ++ tailWord_667742) baseStart_667742 baseEnd_667742 := by
    simpa [prefixWord, tailWord_667742, baseEnd_667742] using wordTrace_append hprefix tailTrace_667742
  have hstable : (prefixWord ++ tailWord_667742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667742).length < 2 ^ (prefixWord ++ tailWord_667742).sum := by decide
  have hdescent : baseEnd_667742 < baseStart_667742 := by decide
  rcases family_descends (prefixWord ++ tailWord_667742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667753 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 3]
def baseStart_667753 : Nat := 118140960795 + 667753 * 2 ^ 59
def prefixEnd_667753 : Nat := 4983230072969 + 3 ^ 40 * 667753 * 2
def baseEnd_667753 : Nat := 152390332214147176451807

theorem tailTrace_667753 : CollatzResearch.WordTrace tailWord_667753 prefixEnd_667753 152390332214147176451807 := by
  unfold tailWord_667753
  simp only [CollatzResearch.WordTrace]
  refine ⟨24354952749852398978071913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16236635166568265985381275 24354952749852398978071913)
  ·
    refine ⟨18266214562389299233553935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24354952749852398978071913 18266214562389299233553935)
    ·
      refine ⟨27399321843583948850330903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18266214562389299233553935 27399321843583948850330903)
      ·
        refine ⟨41098982765375923275496355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27399321843583948850330903 41098982765375923275496355)
        ·
          refine ⟨61648474148063884913244533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41098982765375923275496355 61648474148063884913244533)
          ·
            refine ⟨5779544451380989210616675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61648474148063884913244533 5779544451380989210616675)
            ·
              refine ⟨8669316677071483815925013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779544451380989210616675 8669316677071483815925013)
              ·
                refine ⟨406374219237725803871485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8669316677071483815925013 406374219237725803871485)
                ·
                  refine ⟨152390332214147176451807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406374219237725803871485 152390332214147176451807)
                  ·
                    rfl

theorem cell21_667753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_667753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667753 prefixEnd_667753 := by exact prefixLift 667753
  have htrace : WordTrace (prefixWord ++ tailWord_667753) baseStart_667753 baseEnd_667753 := by
    simpa [prefixWord, tailWord_667753, baseEnd_667753] using wordTrace_append hprefix tailTrace_667753
  have hstable : (prefixWord ++ tailWord_667753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667753).length < 2 ^ (prefixWord ++ tailWord_667753).sum := by decide
  have hdescent : baseEnd_667753 < baseStart_667753 := by decide
  rcases family_descends (prefixWord ++ tailWord_667753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667815 : List Nat := [1, 1, 6, 2, 2, 1, 2, 6]
def baseStart_667815 : Nat := 118140960795 + 667815 * 2 ^ 59
def prefixEnd_667815 : Nat := 4983230072969 + 3 ^ 40 * 667815 * 2
def baseEnd_667815 : Nat := 50801493819616282139449

theorem tailTrace_667815 : CollatzResearch.WordTrace tailWord_667815 prefixEnd_667815 50801493819616282139449 := by
  unfold tailWord_667815
  simp only [CollatzResearch.WordTrace]
  refine ⟨24357214075627783566828899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16238142717085189044552599 24357214075627783566828899)
  ·
    refine ⟨36535821113441675350243349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24357214075627783566828899 36535821113441675350243349)
    ·
      refine ⟨1712616614692578532042657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36535821113441675350243349 1712616614692578532042657)
      ·
        refine ⟨1284462461019433899031993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712616614692578532042657 1284462461019433899031993)
        ·
          refine ⟨963346845764575424273995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284462461019433899031993 963346845764575424273995)
          ·
            refine ⟨1445020268646863136410993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963346845764575424273995 1445020268646863136410993)
            ·
              refine ⟨1083765201485147352308245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445020268646863136410993 1083765201485147352308245)
              ·
                refine ⟨50801493819616282139449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1083765201485147352308245 50801493819616282139449)
                ·
                  rfl

theorem cell21_667815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_667815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_667815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_667815 prefixEnd_667815 := by exact prefixLift 667815
  have htrace : WordTrace (prefixWord ++ tailWord_667815) baseStart_667815 baseEnd_667815 := by
    simpa [prefixWord, tailWord_667815, baseEnd_667815] using wordTrace_append hprefix tailTrace_667815
  have hstable : (prefixWord ++ tailWord_667815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667815).length < 2 ^ (prefixWord ++ tailWord_667815).sum := by decide
  have hdescent : baseEnd_667815 < baseStart_667815 := by decide
  rcases family_descends (prefixWord ++ tailWord_667815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668023 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_668023 : Nat := 118140960795 + 668023 * 2 ^ 59
def prefixEnd_668023 : Nat := 4983230072969 + 3 ^ 40 * 668023 * 2
def baseEnd_668023 : Nat := 152451949892686706951255

theorem tailTrace_668023 : CollatzResearch.WordTrace tailWord_668023 prefixEnd_668023 152451949892686706951255 := by
  unfold tailWord_668023
  simp only [CollatzResearch.WordTrace]
  refine ⟨24364800458874235090400723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16243200305916156726933815 24364800458874235090400723)
  ·
    refine ⟨36547200688311352635601085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24364800458874235090400723 36547200688311352635601085)
    ·
      refine ⟨13705200258116757238350407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36547200688311352635601085 13705200258116757238350407)
      ·
        refine ⟨20557800387175135857525611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13705200258116757238350407 20557800387175135857525611)
        ·
          refine ⟨30836700580762703786288417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20557800387175135857525611 30836700580762703786288417)
          ·
            refine ⟨23127525435572027839716313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30836700580762703786288417 23127525435572027839716313)
            ·
              refine ⟨17345644076679020879787235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23127525435572027839716313 17345644076679020879787235)
              ·
                refine ⟨26018466115018531319680853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17345644076679020879787235 26018466115018531319680853)
                ·
                  refine ⟨152451949892686706951255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26018466115018531319680853 152451949892686706951255)
                  ·
                    rfl

theorem cell21_668023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_668023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668023 prefixEnd_668023 := by exact prefixLift 668023
  have htrace : WordTrace (prefixWord ++ tailWord_668023) baseStart_668023 baseEnd_668023 := by
    simpa [prefixWord, tailWord_668023, baseEnd_668023] using wordTrace_append hprefix tailTrace_668023
  have hstable : (prefixWord ++ tailWord_668023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668023).length < 2 ^ (prefixWord ++ tailWord_668023).sum := by decide
  have hdescent : baseEnd_668023 < baseStart_668023 := by decide
  rcases family_descends (prefixWord ++ tailWord_668023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668040 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_668040 : Nat := 118140960795 + 668040 * 2 ^ 59
def prefixEnd_668040 : Nat := 4983230072969 + 3 ^ 40 * 668040 * 2
def baseEnd_668040 : Nat := 152455829524298455167887

theorem tailTrace_668040 : CollatzResearch.WordTrace tailWord_668040 prefixEnd_668040 152455829524298455167887 := by
  unfold tailWord_668040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182710249906323496884787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16243613666541764662513049 12182710249906323496884787)
  ·
    refine ⟨18274065374859485245327181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12182710249906323496884787 18274065374859485245327181)
    ·
      refine ⟨6852774515572306966997693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18274065374859485245327181 6852774515572306966997693)
      ·
        refine ⟨2569790443339615112624135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6852774515572306966997693 2569790443339615112624135)
        ·
          refine ⟨3854685665009422668936203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569790443339615112624135 3854685665009422668936203)
          ·
            refine ⟨5782028497514134003404305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854685665009422668936203 5782028497514134003404305)
            ·
              refine ⟨4336521373135600502553229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5782028497514134003404305 4336521373135600502553229)
              ·
                refine ⟨1626195514925850188457461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4336521373135600502553229 1626195514925850188457461)
                ·
                  refine ⟨152455829524298455167887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1626195514925850188457461 152455829524298455167887)
                  ·
                    rfl

theorem cell21_668040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_668040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668040 prefixEnd_668040 := by exact prefixLift 668040
  have htrace : WordTrace (prefixWord ++ tailWord_668040) baseStart_668040 baseEnd_668040 := by
    simpa [prefixWord, tailWord_668040, baseEnd_668040] using wordTrace_append hprefix tailTrace_668040
  have hstable : (prefixWord ++ tailWord_668040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668040).length < 2 ^ (prefixWord ++ tailWord_668040).sum := by decide
  have hdescent : baseEnd_668040 < baseStart_668040 := by decide
  rcases family_descends (prefixWord ++ tailWord_668040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668161 : List Nat := [1, 2, 4, 1, 3, 1, 1, 8]
def baseStart_668161 : Nat := 118140960795 + 668161 * 2 ^ 59
def prefixEnd_668161 : Nat := 4983230072969 + 3 ^ 40 * 668161 * 2
def baseEnd_668161 : Nat := 50827814457609711216991

theorem tailTrace_668161 : CollatzResearch.WordTrace tailWord_668161 prefixEnd_668161 50827814457609711216991 := by
  unfold tailWord_668161
  simp only [CollatzResearch.WordTrace]
  refine ⟨24369833732374284658924337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16246555821582856439282891 24369833732374284658924337)
  ·
    refine ⟨18277375299280713494193253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24369833732374284658924337 18277375299280713494193253)
    ·
      refine ⟨3427007868615133780161235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18277375299280713494193253 3427007868615133780161235)
      ·
        refine ⟨5140511802922700670241853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427007868615133780161235 5140511802922700670241853)
        ·
          refine ⟨1927691926096012751340695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5140511802922700670241853 1927691926096012751340695)
          ·
            refine ⟨2891537889144019127011043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927691926096012751340695 2891537889144019127011043)
            ·
              refine ⟨4337306833716028690516565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891537889144019127011043 4337306833716028690516565)
              ·
                refine ⟨50827814457609711216991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4337306833716028690516565 50827814457609711216991)
                ·
                  rfl

theorem cell21_668161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_668161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668161 prefixEnd_668161 := by exact prefixLift 668161
  have htrace : WordTrace (prefixWord ++ tailWord_668161) baseStart_668161 baseEnd_668161 := by
    simpa [prefixWord, tailWord_668161, baseEnd_668161] using wordTrace_append hprefix tailTrace_668161
  have hstable : (prefixWord ++ tailWord_668161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668161).length < 2 ^ (prefixWord ++ tailWord_668161).sum := by decide
  have hdescent : baseEnd_668161 < baseStart_668161 := by decide
  rcases family_descends (prefixWord ++ tailWord_668161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668164 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_668164 : Nat := 118140960795 + 668164 * 2 ^ 59
def prefixEnd_668164 : Nat := 4983230072969 + 3 ^ 40 * 668164 * 2
def baseEnd_668164 : Nat := 152484128013701795100967

theorem tailTrace_668164 : CollatzResearch.WordTrace tailWord_668164 prefixEnd_668164 152484128013701795100967 := by
  unfold tailWord_668164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12184971575681708085641773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16246628767575610780855697 12184971575681708085641773)
  ·
    refine ⟨4569364340880640532115665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12184971575681708085641773 4569364340880640532115665)
    ·
      refine ⟨3427023255660480399086749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4569364340880640532115665 3427023255660480399086749)
      ·
        refine ⟨1285133720872680149657531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3427023255660480399086749 1285133720872680149657531)
        ·
          refine ⟨1927700581309020224486297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285133720872680149657531 1927700581309020224486297)
          ·
            refine ⟨1445775435981765168364723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1927700581309020224486297 1445775435981765168364723)
            ·
              refine ⟨2168663153972647752547085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445775435981765168364723 2168663153972647752547085)
              ·
                refine ⟨813248682739742907205157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2168663153972647752547085 813248682739742907205157)
                ·
                  refine ⟨152484128013701795100967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813248682739742907205157 152484128013701795100967)
                  ·
                    rfl

theorem cell21_668164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_668164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668164 prefixEnd_668164 := by exact prefixLift 668164
  have htrace : WordTrace (prefixWord ++ tailWord_668164) baseStart_668164 baseEnd_668164 := by
    simpa [prefixWord, tailWord_668164, baseEnd_668164] using wordTrace_append hprefix tailTrace_668164
  have hstable : (prefixWord ++ tailWord_668164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668164).length < 2 ^ (prefixWord ++ tailWord_668164).sum := by decide
  have hdescent : baseEnd_668164 < baseStart_668164 := by decide
  rcases family_descends (prefixWord ++ tailWord_668164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668212 : List Nat := [2, 5, 1, 3, 1, 2, 1, 6]
def baseStart_668212 : Nat := 118140960795 + 668212 * 2 ^ 59
def prefixEnd_668212 : Nat := 4983230072969 + 3 ^ 40 * 668212 * 2
def baseEnd_668212 : Nat := 50831694089221459433623

theorem tailTrace_668212 : CollatzResearch.WordTrace tailWord_668212 prefixEnd_668212 50831694089221459433623 := by
  unfold tailWord_668212
  simp only [CollatzResearch.WordTrace]
  refine ⟨12185846927594760184515445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16247795903459680246020593 12185846927594760184515445)
  ·
    refine ⟨1142423149462008767298323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12185846927594760184515445 1142423149462008767298323)
    ·
      refine ⟨1713634724193013150947485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142423149462008767298323 1713634724193013150947485)
      ·
        refine ⟨642613021572379931605307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1713634724193013150947485 642613021572379931605307)
        ·
          refine ⟨963919532358569897407961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642613021572379931605307 963919532358569897407961)
          ·
            refine ⟨722939649268927423055971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963919532358569897407961 722939649268927423055971)
            ·
              refine ⟨1084409473903391134583957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722939649268927423055971 1084409473903391134583957)
              ·
                refine ⟨50831694089221459433623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1084409473903391134583957 50831694089221459433623)
                ·
                  rfl

theorem cell21_668212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_668212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668212 prefixEnd_668212 := by exact prefixLift 668212
  have htrace : WordTrace (prefixWord ++ tailWord_668212) baseStart_668212 baseEnd_668212 := by
    simpa [prefixWord, tailWord_668212, baseEnd_668212] using wordTrace_append hprefix tailTrace_668212
  have hstable : (prefixWord ++ tailWord_668212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668212).length < 2 ^ (prefixWord ++ tailWord_668212).sum := by decide
  have hdescent : baseEnd_668212 < baseStart_668212 := by decide
  rcases family_descends (prefixWord ++ tailWord_668212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668333 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 4]
def baseStart_668333 : Nat := 118140960795 + 668333 * 2 ^ 59
def prefixEnd_668333 : Nat := 4983230072969 + 3 ^ 40 * 668333 * 2
def baseEnd_668333 : Nat := 152522696116195056783955

theorem tailTrace_668333 : CollatzResearch.WordTrace tailWord_668333 prefixEnd_668333 152522696116195056783955 := by
  unfold tailWord_668333
  simp only [CollatzResearch.WordTrace]
  refine ⟨24376107087751158034185653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16250738058500772022790435 24376107087751158034185653)
  ·
    refine ⟨2285260039476671065704905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24376107087751158034185653 2285260039476671065704905)
    ·
      refine ⟨1713945029607503299278679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2285260039476671065704905 1713945029607503299278679)
      ·
        refine ⟨2570917544411254948918019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713945029607503299278679 2570917544411254948918019)
        ·
          refine ⟨3856376316616882423377029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570917544411254948918019 3856376316616882423377029)
          ·
            refine ⟨723070559365665454383193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3856376316616882423377029 723070559365665454383193)
            ·
              refine ⟨542302919524249090787395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723070559365665454383193 542302919524249090787395)
              ·
                refine ⟨813454379286373636181093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542302919524249090787395 813454379286373636181093)
                ·
                  refine ⟨152522696116195056783955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813454379286373636181093 152522696116195056783955)
                  ·
                    rfl

theorem cell21_668333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_668333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668333 prefixEnd_668333 := by exact prefixLift 668333
  have htrace : WordTrace (prefixWord ++ tailWord_668333) baseStart_668333 baseEnd_668333 := by
    simpa [prefixWord, tailWord_668333, baseEnd_668333] using wordTrace_append hprefix tailTrace_668333
  have hstable : (prefixWord ++ tailWord_668333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668333).length < 2 ^ (prefixWord ++ tailWord_668333).sum := by decide
  have hdescent : baseEnd_668333 < baseStart_668333 := by decide
  rcases family_descends (prefixWord ++ tailWord_668333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668375 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 4]
def baseStart_668375 : Nat := 118140960795 + 668375 * 2 ^ 59
def prefixEnd_668375 : Nat := 4983230072969 + 3 ^ 40 * 668375 * 2
def baseEnd_668375 : Nat := 152532281088412317083869

theorem tailTrace_668375 : CollatzResearch.WordTrace tailWord_668375 prefixEnd_668375 152532281088412317083869 := by
  unfold tailWord_668375
  simp only [CollatzResearch.WordTrace]
  refine ⟨24377638953598999207214579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16251759302399332804809719 24377638953598999207214579)
  ·
    refine ⟨36566458430398498810821869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24377638953598999207214579 36566458430398498810821869)
    ·
      refine ⟨13712421911399437054058201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36566458430398498810821869 13712421911399437054058201)
      ·
        refine ⟨10284316433549577790543651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13712421911399437054058201 10284316433549577790543651)
        ·
          refine ⟨15426474650324366685815477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10284316433549577790543651 15426474650324366685815477)
          ·
            refine ⟨1446231998467909376795201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15426474650324366685815477 1446231998467909376795201)
            ·
              refine ⟨1084673998850932032596401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446231998467909376795201 1084673998850932032596401)
              ·
                refine ⟨813505499138199024447301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084673998850932032596401 813505499138199024447301)
                ·
                  refine ⟨152532281088412317083869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813505499138199024447301 152532281088412317083869)
                  ·
                    rfl

theorem cell21_668375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_668375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668375 prefixEnd_668375 := by exact prefixLift 668375
  have htrace : WordTrace (prefixWord ++ tailWord_668375) baseStart_668375 baseEnd_668375 := by
    simpa [prefixWord, tailWord_668375, baseEnd_668375] using wordTrace_append hprefix tailTrace_668375
  have hstable : (prefixWord ++ tailWord_668375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668375).length < 2 ^ (prefixWord ++ tailWord_668375).sum := by decide
  have hdescent : baseEnd_668375 < baseStart_668375 := by decide
  rcases family_descends (prefixWord ++ tailWord_668375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668389 : List Nat := [1, 3, 1, 4, 1, 2, 3, 6]
def baseStart_668389 : Nat := 118140960795 + 668389 * 2 ^ 59
def prefixEnd_668389 : Nat := 4983230072969 + 3 ^ 40 * 668389 * 2
def baseEnd_668389 : Nat := 50845158693050467950169

theorem tailTrace_668389 : CollatzResearch.WordTrace tailWord_668389 prefixEnd_668389 50845158693050467950169 := by
  unfold tailWord_668389
  simp only [CollatzResearch.WordTrace]
  refine ⟨24378149575548279598224221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16252099717032186398816147 24378149575548279598224221)
  ·
    refine ⟨9141806090830604849334083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24378149575548279598224221 9141806090830604849334083)
    ·
      refine ⟨13712709136245907274001125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9141806090830604849334083 13712709136245907274001125)
      ·
        refine ⟨2571132963046107613875211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13712709136245907274001125 2571132963046107613875211)
        ·
          refine ⟨3856699444569161420812817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571132963046107613875211 3856699444569161420812817)
          ·
            refine ⟨2892524583426871065609613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3856699444569161420812817 2892524583426871065609613)
            ·
              refine ⟨1084696718785076649603605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2892524583426871065609613 1084696718785076649603605)
              ·
                refine ⟨50845158693050467950169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1084696718785076649603605 50845158693050467950169)
                ·
                  rfl

theorem cell21_668389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 6].length) (baseStart_668389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668389 prefixEnd_668389 := by exact prefixLift 668389
  have htrace : WordTrace (prefixWord ++ tailWord_668389) baseStart_668389 baseEnd_668389 := by
    simpa [prefixWord, tailWord_668389, baseEnd_668389] using wordTrace_append hprefix tailTrace_668389
  have hstable : (prefixWord ++ tailWord_668389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668389).length < 2 ^ (prefixWord ++ tailWord_668389).sum := by decide
  have hdescent : baseEnd_668389 < baseStart_668389 := by decide
  rcases family_descends (prefixWord ++ tailWord_668389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668406 : List Nat := [5, 1, 1, 1, 1, 2, 5, 5]
def baseStart_668406 : Nat := 118140960795 + 668406 * 2 ^ 59
def prefixEnd_668406 : Nat := 4983230072969 + 3 ^ 40 * 668406 * 2
def baseEnd_668406 : Nat := 50846451903587717355713

theorem tailTrace_668406 : CollatzResearch.WordTrace tailWord_668406 prefixEnd_668406 50846451903587717355713 := by
  unfold tailWord_668406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523673101030418218849567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16252513077657794334395381 1523673101030418218849567)
  ·
    refine ⟨2285509651545627328274351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1523673101030418218849567 2285509651545627328274351)
    ·
      refine ⟨3428264477318440992411527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2285509651545627328274351 3428264477318440992411527)
      ·
        refine ⟨5142396715977661488617291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428264477318440992411527 5142396715977661488617291)
        ·
          refine ⟨7713595073966492232925937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142396715977661488617291 7713595073966492232925937)
          ·
            refine ⟨5785196305474869174694453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7713595073966492232925937 5785196305474869174694453)
            ·
              refine ⟨542362153638268985127605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5785196305474869174694453 542362153638268985127605)
              ·
                refine ⟨50846451903587717355713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 542362153638268985127605 50846451903587717355713)
                ·
                  rfl

theorem cell21_668406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_668406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668406 prefixEnd_668406 := by exact prefixLift 668406
  have htrace : WordTrace (prefixWord ++ tailWord_668406) baseStart_668406 baseEnd_668406 := by
    simpa [prefixWord, tailWord_668406, baseEnd_668406] using wordTrace_append hprefix tailTrace_668406
  have hstable : (prefixWord ++ tailWord_668406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668406).length < 2 ^ (prefixWord ++ tailWord_668406).sum := by decide
  have hdescent : baseEnd_668406 < baseStart_668406 := by decide
  rcases family_descends (prefixWord ++ tailWord_668406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668496 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_668496 : Nat := 118140960795 + 668496 * 2 ^ 59
def prefixEnd_668496 : Nat := 4983230072969 + 3 ^ 40 * 668496 * 2
def baseEnd_668496 : Nat := 152559894936942995566955

theorem tailTrace_668496 : CollatzResearch.WordTrace tailWord_668496 prefixEnd_668496 152559894936942995566955 := by
  unfold tailWord_668496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191026093080318436184671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16254701457440424581579561 12191026093080318436184671)
  ·
    refine ⟨18286539139620477654277007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12191026093080318436184671 18286539139620477654277007)
    ·
      refine ⟨27429808709430716481415511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18286539139620477654277007 27429808709430716481415511)
      ·
        refine ⟨41144713064146074722123267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27429808709430716481415511 41144713064146074722123267)
        ·
          refine ⟨61717069596219112083184901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41144713064146074722123267 61717069596219112083184901)
          ·
            refine ⟨11571950549291083515597169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61717069596219112083184901 11571950549291083515597169)
            ·
              refine ⟨8678962911968312636697877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11571950549291083515597169 8678962911968312636697877)
              ·
                refine ⟨406826386498514654845213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8678962911968312636697877 406826386498514654845213)
                ·
                  refine ⟨152559894936942995566955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406826386498514654845213 152559894936942995566955)
                  ·
                    rfl

theorem cell21_668496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_668496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668496 prefixEnd_668496 := by exact prefixLift 668496
  have htrace : WordTrace (prefixWord ++ tailWord_668496) baseStart_668496 baseEnd_668496 := by
    simpa [prefixWord, tailWord_668496, baseEnd_668496] using wordTrace_append hprefix tailTrace_668496
  have hstable : (prefixWord ++ tailWord_668496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668496).length < 2 ^ (prefixWord ++ tailWord_668496).sum := by decide
  have hdescent : baseEnd_668496 < baseStart_668496 := by decide
  rcases family_descends (prefixWord ++ tailWord_668496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668524 : List Nat := [2, 2, 1, 1, 4, 1, 1, 9]
def baseStart_668524 : Nat := 118140960795 + 668524 * 2 ^ 59
def prefixEnd_668524 : Nat := 4983230072969 + 3 ^ 40 * 668524 * 2
def baseEnd_668524 : Nat := 50855428306140389700077

theorem tailTrace_668524 : CollatzResearch.WordTrace tailWord_668524 prefixEnd_668524 50855428306140389700077 := by
  unfold tailWord_668524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191536715029598827194313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16255382286706131769592417 12191536715029598827194313)
  ·
    refine ⟨9143652536272199120395735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12191536715029598827194313 9143652536272199120395735)
    ·
      refine ⟨13715478804408298680593603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143652536272199120395735 13715478804408298680593603)
      ·
        refine ⟨20573218206612448020890405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13715478804408298680593603 20573218206612448020890405)
        ·
          refine ⟨3857478413739834003916951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20573218206612448020890405 3857478413739834003916951)
          ·
            refine ⟨5786217620609751005875427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857478413739834003916951 5786217620609751005875427)
            ·
              refine ⟨8679326430914626508813141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5786217620609751005875427 8679326430914626508813141)
              ·
                refine ⟨50855428306140389700077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8679326430914626508813141 50855428306140389700077)
                ·
                  rfl

theorem cell21_668524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_668524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668524 prefixEnd_668524 := by exact prefixLift 668524
  have htrace : WordTrace (prefixWord ++ tailWord_668524) baseStart_668524 baseEnd_668524 := by
    simpa [prefixWord, tailWord_668524, baseEnd_668524] using wordTrace_append hprefix tailTrace_668524
  have hstable : (prefixWord ++ tailWord_668524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668524).length < 2 ^ (prefixWord ++ tailWord_668524).sum := by decide
  have hdescent : baseEnd_668524 < baseStart_668524 := by decide
  rcases family_descends (prefixWord ++ tailWord_668524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668569 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_668569 : Nat := 118140960795 + 668569 * 2 ^ 59
def prefixEnd_668569 : Nat := 4983230072969 + 3 ^ 40 * 668569 * 2
def baseEnd_668569 : Nat := 152576554531511090850139

theorem tailTrace_668569 : CollatzResearch.WordTrace tailWord_668569 prefixEnd_668569 152576554531511090850139 := by
  unfold tailWord_668569
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384714714896170339776761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16256476476597446893184507 24384714714896170339776761)
  ·
    refine ⟨18288536036172127754832571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24384714714896170339776761 18288536036172127754832571)
    ·
      refine ⟨27432804054258191632248857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18288536036172127754832571 27432804054258191632248857)
      ·
        refine ⟨20574603040693643724186643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27432804054258191632248857 20574603040693643724186643)
        ·
          refine ⟨30861904561040465586279965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20574603040693643724186643 30861904561040465586279965)
          ·
            refine ⟨11573214210390174594854987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30861904561040465586279965 11573214210390174594854987)
            ·
              refine ⟨17359821315585261892282481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11573214210390174594854987 17359821315585261892282481)
              ·
                refine ⟨13019865986688946419211861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17359821315585261892282481 13019865986688946419211861)
                ·
                  refine ⟨152576554531511090850139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13019865986688946419211861 152576554531511090850139)
                  ·
                    rfl

theorem cell21_668569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_668569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668569 prefixEnd_668569 := by exact prefixLift 668569
  have htrace : WordTrace (prefixWord ++ tailWord_668569) baseStart_668569 baseEnd_668569 := by
    simpa [prefixWord, tailWord_668569, baseEnd_668569] using wordTrace_append hprefix tailTrace_668569
  have hstable : (prefixWord ++ tailWord_668569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668569).length < 2 ^ (prefixWord ++ tailWord_668569).sum := by decide
  have hdescent : baseEnd_668569 < baseStart_668569 := by decide
  rcases family_descends (prefixWord ++ tailWord_668569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668600 : List Nat := [2, 1, 2, 1, 2, 5, 8]
def baseStart_668600 : Nat := 118140960795 + 668600 * 2 ^ 59
def prefixEnd_668600 : Nat := 4983230072969 + 3 ^ 40 * 668600 * 2
def baseEnd_668600 : Nat := 16953736572651325092601

theorem tailTrace_668600 : CollatzResearch.WordTrace tailWord_668600 prefixEnd_668600 16953736572651325092601 := by
  unfold tailWord_668600
  simp only [CollatzResearch.WordTrace]
  refine ⟨12192922688891931317077627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16257230251855908422770169 12192922688891931317077627)
  ·
    refine ⟨18289384033337896975616441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12192922688891931317077627 18289384033337896975616441)
    ·
      refine ⟨13717038025003422731712331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18289384033337896975616441 13717038025003422731712331)
      ·
        refine ⟨20575557037505134097568497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13717038025003422731712331 20575557037505134097568497)
        ·
          refine ⟨15431667778128850573176373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20575557037505134097568497 15431667778128850573176373)
          ·
            refine ⟨1446718854199579741235285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15431667778128850573176373 1446718854199579741235285)
            ·
              refine ⟨16953736572651325092601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1446718854199579741235285 16953736572651325092601)
              ·
                rfl

theorem cell21_668600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 8].length) (baseStart_668600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668600 prefixEnd_668600 := by exact prefixLift 668600
  have htrace : WordTrace (prefixWord ++ tailWord_668600) baseStart_668600 baseEnd_668600 := by
    simpa [prefixWord, tailWord_668600, baseEnd_668600] using wordTrace_append hprefix tailTrace_668600
  have hstable : (prefixWord ++ tailWord_668600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668600).length < 2 ^ (prefixWord ++ tailWord_668600).sum := by decide
  have hdescent : baseEnd_668600 < baseStart_668600 := by decide
  rcases family_descends (prefixWord ++ tailWord_668600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668634 : List Nat := [3, 1, 1, 2, 4, 3, 2, 5]
def baseStart_668634 : Nat := 118140960795 + 668634 * 2 ^ 59
def prefixEnd_668634 : Nat := 4983230072969 + 3 ^ 40 * 668634 * 2
def baseEnd_668634 : Nat := 50863796139028474088891

theorem tailTrace_668634 : CollatzResearch.WordTrace tailWord_668634 prefixEnd_668634 50863796139028474088891 := by
  unfold tailWord_668634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096771364915171610223239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16258056973107124293928637 6096771364915171610223239)
  ·
    refine ⟨9145157047372757415334859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6096771364915171610223239 9145157047372757415334859)
    ·
      refine ⟨13717735571059136123002289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9145157047372757415334859 13717735571059136123002289)
      ·
        refine ⟨10288301678294352092251717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13717735571059136123002289 10288301678294352092251717)
        ·
          refine ⟨1929056564680191017297197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10288301678294352092251717 1929056564680191017297197)
          ·
            refine ⟨723396211755071631486449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1929056564680191017297197 723396211755071631486449)
            ·
              refine ⟨542547158816303723614837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723396211755071631486449 542547158816303723614837)
              ·
                refine ⟨50863796139028474088891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 542547158816303723614837 50863796139028474088891)
                ·
                  rfl

theorem cell21_668634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_668634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668634 prefixEnd_668634 := by exact prefixLift 668634
  have htrace : WordTrace (prefixWord ++ tailWord_668634) baseStart_668634 baseEnd_668634 := by
    simpa [prefixWord, tailWord_668634, baseEnd_668634] using wordTrace_append hprefix tailTrace_668634
  have hstable : (prefixWord ++ tailWord_668634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668634).length < 2 ^ (prefixWord ++ tailWord_668634).sum := by decide
  have hdescent : baseEnd_668634 < baseStart_668634 := by decide
  rcases family_descends (prefixWord ++ tailWord_668634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668665 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 3]
def baseStart_668665 : Nat := 118140960795 + 668665 * 2 ^ 59
def prefixEnd_668665 : Nat := 4983230072969 + 3 ^ 40 * 668665 * 2
def baseEnd_668665 : Nat := 152598463039436257249943

theorem tailTrace_668665 : CollatzResearch.WordTrace tailWord_668665 prefixEnd_668665 152598463039436257249943 := by
  unfold tailWord_668665
  simp only [CollatzResearch.WordTrace]
  refine ⟨24388216122548378735271449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16258810748365585823514299 24388216122548378735271449)
  ·
    refine ⟨18291162091911284051453587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24388216122548378735271449 18291162091911284051453587)
    ·
      refine ⟨27436743137866926077180381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18291162091911284051453587 27436743137866926077180381)
      ·
        refine ⟨10288778676700097278942643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27436743137866926077180381 10288778676700097278942643)
        ·
          refine ⟨15433168015050145918413965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10288778676700097278942643 15433168015050145918413965)
          ·
            refine ⟨5787438005643804719405237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15433168015050145918413965 5787438005643804719405237)
            ·
              refine ⟨542572313029106692444241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5787438005643804719405237 542572313029106692444241)
              ·
                refine ⟨406929234771830019333181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542572313029106692444241 406929234771830019333181)
                ·
                  refine ⟨152598463039436257249943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406929234771830019333181 152598463039436257249943)
                  ·
                    rfl

theorem cell21_668665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_668665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668665 prefixEnd_668665 := by exact prefixLift 668665
  have htrace : WordTrace (prefixWord ++ tailWord_668665) baseStart_668665 baseEnd_668665 := by
    simpa [prefixWord, tailWord_668665, baseEnd_668665] using wordTrace_append hprefix tailTrace_668665
  have hstable : (prefixWord ++ tailWord_668665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668665).length < 2 ^ (prefixWord ++ tailWord_668665).sum := by decide
  have hdescent : baseEnd_668665 < baseStart_668665 := by decide
  rcases family_descends (prefixWord ++ tailWord_668665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668783 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 5]
def baseStart_668783 : Nat := 118140960795 + 668783 * 2 ^ 59
def prefixEnd_668783 : Nat := 4983230072969 + 3 ^ 40 * 668783 * 2
def baseEnd_668783 : Nat := 152625392247094274283035

theorem tailTrace_668783 : CollatzResearch.WordTrace tailWord_668783 prefixEnd_668783 152625392247094274283035 := by
  unfold tailWord_668783
  simp only [CollatzResearch.WordTrace]
  refine ⟨24392519936120884888067003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16261679957413923258711335 24392519936120884888067003)
  ·
    refine ⟨36588779904181327332100505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24392519936120884888067003 36588779904181327332100505)
    ·
      refine ⟨27441584928135995499075379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36588779904181327332100505 27441584928135995499075379)
      ·
        refine ⟨41162377392203993248613069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27441584928135995499075379 41162377392203993248613069)
        ·
          refine ⟨15435891522076497468229901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41162377392203993248613069 15435891522076497468229901)
          ·
            refine ⟨5788459320778686550586213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15435891522076497468229901 5788459320778686550586213)
            ·
              refine ⟨1085336122646003728234915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5788459320778686550586213 1085336122646003728234915)
              ·
                refine ⟨1628004183969005592352373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085336122646003728234915 1628004183969005592352373)
                ·
                  refine ⟨152625392247094274283035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628004183969005592352373 152625392247094274283035)
                  ·
                    rfl

theorem cell21_668783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_668783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668783 prefixEnd_668783 := by exact prefixLift 668783
  have htrace : WordTrace (prefixWord ++ tailWord_668783) baseStart_668783 baseEnd_668783 := by
    simpa [prefixWord, tailWord_668783, baseEnd_668783] using wordTrace_append hprefix tailTrace_668783
  have hstable : (prefixWord ++ tailWord_668783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668783).length < 2 ^ (prefixWord ++ tailWord_668783).sum := by decide
  have hdescent : baseEnd_668783 < baseStart_668783 := by decide
  rcases family_descends (prefixWord ++ tailWord_668783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668789 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 4]
def baseStart_668789 : Nat := 118140960795 + 668789 * 2 ^ 59
def prefixEnd_668789 : Nat := 4983230072969 + 3 ^ 40 * 668789 * 2
def baseEnd_668789 : Nat := 152626761528839597183023

theorem tailTrace_668789 : CollatzResearch.WordTrace tailWord_668789 prefixEnd_668789 152626761528839597183023 := by
  unfold tailWord_668789
  simp only [CollatzResearch.WordTrace]
  refine ⟨24392738774099147912785421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16261825849399431941856947 24392738774099147912785421)
  ·
    refine ⟨9147277040287180467294533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24392738774099147912785421 9147277040287180467294533)
    ·
      refine ⟨1715114445053846337617725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9147277040287180467294533 1715114445053846337617725)
      ·
        refine ⟨643167916895192376606647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1715114445053846337617725 643167916895192376606647)
        ·
          refine ⟨964751875342788564909971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643167916895192376606647 964751875342788564909971)
          ·
            refine ⟨1447127813014182847364957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964751875342788564909971 1447127813014182847364957)
            ·
              refine ⟨542672929880318567761859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1447127813014182847364957 542672929880318567761859)
              ·
                refine ⟨814009394820477851642789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542672929880318567761859 814009394820477851642789)
                ·
                  refine ⟨152626761528839597183023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814009394820477851642789 152626761528839597183023)
                  ·
                    rfl

theorem cell21_668789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_668789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668789 prefixEnd_668789 := by exact prefixLift 668789
  have htrace : WordTrace (prefixWord ++ tailWord_668789) baseStart_668789 baseEnd_668789 := by
    simpa [prefixWord, tailWord_668789, baseEnd_668789] using wordTrace_append hprefix tailTrace_668789
  have hstable : (prefixWord ++ tailWord_668789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668789).length < 2 ^ (prefixWord ++ tailWord_668789).sum := by decide
  have hdescent : baseEnd_668789 < baseStart_668789 := by decide
  rcases family_descends (prefixWord ++ tailWord_668789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668814 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_668814 : Nat := 118140960795 + 668814 * 2 ^ 59
def prefixEnd_668814 : Nat := 4983230072969 + 3 ^ 40 * 668814 * 2
def baseEnd_668814 : Nat := 152632466869445109266305

theorem tailTrace_668814 : CollatzResearch.WordTrace tailWord_668814 prefixEnd_668814 152632466869445109266305 := by
  unfold tailWord_668814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049206324876072147805687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16262433732672384788296997 3049206324876072147805687)
  ·
    refine ⟨4573809487314108221708531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3049206324876072147805687 4573809487314108221708531)
    ·
      refine ⟨6860714230971162332562797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4573809487314108221708531 6860714230971162332562797)
      ·
        refine ⟨2572767836614185874711049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6860714230971162332562797 2572767836614185874711049)
        ·
          refine ⟨1929575877460639406033287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2572767836614185874711049 1929575877460639406033287)
          ·
            refine ⟨2894363816190959109049931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929575877460639406033287 2894363816190959109049931)
            ·
              refine ⟨4341545724286438663574897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894363816190959109049931 4341545724286438663574897)
              ·
                refine ⟨3256159293214828997681173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4341545724286438663574897 3256159293214828997681173)
                ·
                  refine ⟨152632466869445109266305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3256159293214828997681173 152632466869445109266305)
                  ·
                    rfl

theorem cell21_668814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_668814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668814 prefixEnd_668814 := by exact prefixLift 668814
  have htrace : WordTrace (prefixWord ++ tailWord_668814) baseStart_668814 baseEnd_668814 := by
    simpa [prefixWord, tailWord_668814, baseEnd_668814] using wordTrace_append hprefix tailTrace_668814
  have hstable : (prefixWord ++ tailWord_668814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668814).length < 2 ^ (prefixWord ++ tailWord_668814).sum := by decide
  have hdescent : baseEnd_668814 < baseStart_668814 := by decide
  rcases family_descends (prefixWord ++ tailWord_668814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668828 : List Nat := [2, 2, 3, 2, 1, 2, 9]
def baseStart_668828 : Nat := 118140960795 + 668828 * 2 ^ 59
def prefixEnd_668828 : Nat := 4983230072969 + 3 ^ 40 * 668828 * 2
def baseEnd_668828 : Nat := 16959517984464910670327

theorem tailTrace_668828 : CollatzResearch.WordTrace tailWord_668828 prefixEnd_668828 16959517984464910670327 := by
  unfold tailWord_668828
  simp only [CollatzResearch.WordTrace]
  refine ⟨12197080610478928786727569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16262774147305238382303425 12197080610478928786727569)
  ·
    refine ⟨9147810457859196590045677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12197080610478928786727569 9147810457859196590045677)
    ·
      refine ⟨3430428921697198721267129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9147810457859196590045677 3430428921697198721267129)
      ·
        refine ⟨2572821691272899040950347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3430428921697198721267129 2572821691272899040950347)
        ·
          refine ⟨3859232536909348561425521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572821691272899040950347 3859232536909348561425521)
          ·
            refine ⟨2894424402682011421069141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3859232536909348561425521 2894424402682011421069141)
            ·
              refine ⟨16959517984464910670327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2894424402682011421069141 16959517984464910670327)
              ·
                rfl

theorem cell21_668828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 9].length) (baseStart_668828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668828 prefixEnd_668828 := by exact prefixLift 668828
  have htrace : WordTrace (prefixWord ++ tailWord_668828) baseStart_668828 baseEnd_668828 := by
    simpa [prefixWord, tailWord_668828, baseEnd_668828] using wordTrace_append hprefix tailTrace_668828
  have hstable : (prefixWord ++ tailWord_668828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668828).length < 2 ^ (prefixWord ++ tailWord_668828).sum := by decide
  have hdescent : baseEnd_668828 < baseStart_668828 := by decide
  rcases family_descends (prefixWord ++ tailWord_668828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668834 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_668834 : Nat := 118140960795 + 668834 * 2 ^ 59
def prefixEnd_668834 : Nat := 4983230072969 + 3 ^ 40 * 668834 * 2
def baseEnd_668834 : Nat := 152637031141929518932931

theorem tailTrace_668834 : CollatzResearch.WordTrace tailWord_668834 prefixEnd_668834 152637031141929518932931 := by
  unfold tailWord_668834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098595014734030149543389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16262920039290747065449037 6098595014734030149543389)
  ·
    refine ⟨2286973130525261306078771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6098595014734030149543389 2286973130525261306078771)
    ·
      refine ⟨3430459695787891959118157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286973130525261306078771 3430459695787891959118157)
      ·
        refine ⟨1286422385920459484669309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3430459695787891959118157 1286422385920459484669309)
        ·
          refine ⟨482408394720172306750991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1286422385920459484669309 482408394720172306750991)
          ·
            refine ⟨723612592080258460126487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482408394720172306750991 723612592080258460126487)
            ·
              refine ⟨1085418888120387690189731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723612592080258460126487 1085418888120387690189731)
              ·
                refine ⟨1628128332180581535284597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085418888120387690189731 1628128332180581535284597)
                ·
                  refine ⟨152637031141929518932931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628128332180581535284597 152637031141929518932931)
                  ·
                    rfl

theorem cell21_668834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_668834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668834 prefixEnd_668834 := by exact prefixLift 668834
  have htrace : WordTrace (prefixWord ++ tailWord_668834) baseStart_668834 baseEnd_668834 := by
    simpa [prefixWord, tailWord_668834, baseEnd_668834] using wordTrace_append hprefix tailTrace_668834
  have hstable : (prefixWord ++ tailWord_668834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668834).length < 2 ^ (prefixWord ++ tailWord_668834).sum := by decide
  have hdescent : baseEnd_668834 < baseStart_668834 := by decide
  rcases family_descends (prefixWord ++ tailWord_668834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668952 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_668952 : Nat := 118140960795 + 668952 * 2 ^ 59
def prefixEnd_668952 : Nat := 4983230072969 + 3 ^ 40 * 668952 * 2
def baseEnd_668952 : Nat := 152663960349587535966023

theorem tailTrace_668952 : CollatzResearch.WordTrace tailWord_668952 prefixEnd_668952 152663960349587535966023 := by
  unfold tailWord_668952
  simp only [CollatzResearch.WordTrace]
  refine ⟨12199341936254313375484555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16265789248339084500646073 12199341936254313375484555)
  ·
    refine ⟨18299012904381470063226833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12199341936254313375484555 18299012904381470063226833)
    ·
      refine ⟨13724259678286102547420125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18299012904381470063226833 13724259678286102547420125)
      ·
        refine ⟨5146597379357288455282547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13724259678286102547420125 5146597379357288455282547)
        ·
          refine ⟨7719896069035932682923821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146597379357288455282547 7719896069035932682923821)
          ·
            refine ⟨2894961025888474756096433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7719896069035932682923821 2894961025888474756096433)
            ·
              refine ⟨2171220769416356067072325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894961025888474756096433 2171220769416356067072325)
              ·
                refine ⟨407103894265566762576061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2171220769416356067072325 407103894265566762576061)
                ·
                  refine ⟨152663960349587535966023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407103894265566762576061 152663960349587535966023)
                  ·
                    rfl

theorem cell21_668952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_668952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_668952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_668952 prefixEnd_668952 := by exact prefixLift 668952
  have htrace : WordTrace (prefixWord ++ tailWord_668952) baseStart_668952 baseEnd_668952 := by
    simpa [prefixWord, tailWord_668952, baseEnd_668952] using wordTrace_append hprefix tailTrace_668952
  have hstable : (prefixWord ++ tailWord_668952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668952).length < 2 ^ (prefixWord ++ tailWord_668952).sum := by decide
  have hdescent : baseEnd_668952 < baseStart_668952 := by decide
  rcases family_descends (prefixWord ++ tailWord_668952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669039 : List Nat := [1, 1, 2, 1, 3, 1, 3, 9]
def baseStart_669039 : Nat := 118140960795 + 669039 * 2 ^ 59
def prefixEnd_669039 : Nat := 4983230072969 + 3 ^ 40 * 669039 * 2
def baseEnd_669039 : Nat := 50894604978298239338615

theorem tailTrace_669039 : CollatzResearch.WordTrace tailWord_669039 prefixEnd_669039 50894604978298239338615 := by
  unfold tailWord_669039
  simp only [CollatzResearch.WordTrace]
  refine ⟨24401857023193440609386171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16267904682128960406257447 24401857023193440609386171)
  ·
    refine ⟨36602785534790160914079257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24401857023193440609386171 36602785534790160914079257)
    ·
      refine ⟨27452089151092620685559443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36602785534790160914079257 27452089151092620685559443)
      ·
        refine ⟨41178133726638931028339165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27452089151092620685559443 41178133726638931028339165)
        ·
          refine ⟨15441800147489599135627187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41178133726638931028339165 15441800147489599135627187)
          ·
            refine ⟨23162700221234398703440781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15441800147489599135627187 23162700221234398703440781)
            ·
              refine ⟨8686012582962899513790293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23162700221234398703440781 8686012582962899513790293)
              ·
                refine ⟨50894604978298239338615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8686012582962899513790293 50894604978298239338615)
                ·
                  rfl

theorem cell21_669039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_669039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669039 prefixEnd_669039 := by exact prefixLift 669039
  have htrace : WordTrace (prefixWord ++ tailWord_669039) baseStart_669039 baseEnd_669039 := by
    simpa [prefixWord, tailWord_669039, baseEnd_669039] using wordTrace_append hprefix tailTrace_669039
  have hstable : (prefixWord ++ tailWord_669039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669039).length < 2 ^ (prefixWord ++ tailWord_669039).sum := by decide
  have hdescent : baseEnd_669039 < baseStart_669039 := by decide
  rcases family_descends (prefixWord ++ tailWord_669039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669087 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 5]
def baseStart_669087 : Nat := 118140960795 + 669087 * 2 ^ 59
def prefixEnd_669087 : Nat := 4983230072969 + 3 ^ 40 * 669087 * 2
def baseEnd_669087 : Nat := 152694769188857301215747

theorem tailTrace_669087 : CollatzResearch.WordTrace tailWord_669087 prefixEnd_669087 152694769188857301215747 := by
  unfold tailWord_669087
  simp only [CollatzResearch.WordTrace]
  refine ⟨24403607727019544807133515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16269071818013029871422343 24403607727019544807133515)
  ·
    refine ⟨36605411590529317210700273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24403607727019544807133515 36605411590529317210700273)
    ·
      refine ⟨27454058692896987908025205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36605411590529317210700273 27454058692896987908025205)
      ·
        refine ⟨2573818002459092616377363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27454058692896987908025205 2573818002459092616377363)
        ·
          refine ⟨3860727003688638924566045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573818002459092616377363 3860727003688638924566045)
          ·
            refine ⟨1447772626383239596712267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3860727003688638924566045 1447772626383239596712267)
            ·
              refine ⟨2171658939574859395068401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447772626383239596712267 2171658939574859395068401)
              ·
                refine ⟨1628744204681144546301301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171658939574859395068401 1628744204681144546301301)
                ·
                  refine ⟨152694769188857301215747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628744204681144546301301 152694769188857301215747)
                  ·
                    rfl

theorem cell21_669087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_669087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669087 prefixEnd_669087 := by exact prefixLift 669087
  have htrace : WordTrace (prefixWord ++ tailWord_669087) baseStart_669087 baseEnd_669087 := by
    simpa [prefixWord, tailWord_669087, baseEnd_669087] using wordTrace_append hprefix tailTrace_669087
  have hstable : (prefixWord ++ tailWord_669087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669087).length < 2 ^ (prefixWord ++ tailWord_669087).sum := by decide
  have hdescent : baseEnd_669087 < baseStart_669087 := by decide
  rcases family_descends (prefixWord ++ tailWord_669087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669149 : List Nat := [1, 4, 3, 1, 1, 2, 4, 5]
def baseStart_669149 : Nat := 118140960795 + 669149 * 2 ^ 59
def prefixEnd_669149 : Nat := 4983230072969 + 3 ^ 40 * 669149 * 2
def baseEnd_669149 : Nat := 50902972811186323727429

theorem tailTrace_669149 : CollatzResearch.WordTrace tailWord_669149 prefixEnd_669149 50902972811186323727429 := by
  unfold tailWord_669149
  simp only [CollatzResearch.WordTrace]
  refine ⟨24405869052794929395890501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16270579368529952930593667 24405869052794929395890501)
  ·
    refine ⟨4576100447399049261729469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24405869052794929395890501 4576100447399049261729469)
    ·
      refine ⟨1716037667774643473148551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4576100447399049261729469 1716037667774643473148551)
      ·
        refine ⟨2574056501661965209722827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716037667774643473148551 2574056501661965209722827)
        ·
          refine ⟨3861084752492947814584241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574056501661965209722827 3861084752492947814584241)
          ·
            refine ⟨2895813564369710860938181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861084752492947814584241 2895813564369710860938181)
            ·
              refine ⟨542965043319320786425909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2895813564369710860938181 542965043319320786425909)
              ·
                refine ⟨50902972811186323727429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 542965043319320786425909 50902972811186323727429)
                ·
                  rfl

theorem cell21_669149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 5].length) (baseStart_669149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669149 prefixEnd_669149 := by exact prefixLift 669149
  have htrace : WordTrace (prefixWord ++ tailWord_669149) baseStart_669149 baseEnd_669149 := by
    simpa [prefixWord, tailWord_669149, baseEnd_669149] using wordTrace_append hprefix tailTrace_669149
  have hstable : (prefixWord ++ tailWord_669149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669149).length < 2 ^ (prefixWord ++ tailWord_669149).sum := by decide
  have hdescent : baseEnd_669149 < baseStart_669149 := by decide
  rcases family_descends (prefixWord ++ tailWord_669149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669163 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 3]
def baseStart_669163 : Nat := 118140960795 + 669163 * 2 ^ 59
def prefixEnd_669163 : Nat := 4983230072969 + 3 ^ 40 * 669163 * 2
def baseEnd_669163 : Nat := 152712113424298057948925

theorem tailTrace_669163 : CollatzResearch.WordTrace tailWord_669163 prefixEnd_669163 152712113424298057948925 := by
  unfold tailWord_669163
  simp only [CollatzResearch.WordTrace]
  refine ⟨24406379674744209786900143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16270919783162806524600095 24406379674744209786900143)
  ·
    refine ⟨36609569512116314680350215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24406379674744209786900143 36609569512116314680350215)
    ·
      refine ⟨54914354268174472020525323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36609569512116314680350215 54914354268174472020525323)
      ·
        refine ⟨82371531402261708030787985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54914354268174472020525323 82371531402261708030787985)
        ·
          refine ⟨61778648551696281023090989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82371531402261708030787985 61778648551696281023090989)
          ·
            refine ⟨23166993206886105383659121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61778648551696281023090989 23166993206886105383659121)
            ·
              refine ⟨17375244905164579037744341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23166993206886105383659121 17375244905164579037744341)
              ·
                refine ⟨407232302464794821197133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17375244905164579037744341 407232302464794821197133)
                ·
                  refine ⟨152712113424298057948925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407232302464794821197133 152712113424298057948925)
                  ·
                    rfl

theorem cell21_669163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 3].length) (baseStart_669163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669163 prefixEnd_669163 := by exact prefixLift 669163
  have htrace : WordTrace (prefixWord ++ tailWord_669163) baseStart_669163 baseEnd_669163 := by
    simpa [prefixWord, tailWord_669163, baseEnd_669163] using wordTrace_append hprefix tailTrace_669163
  have hstable : (prefixWord ++ tailWord_669163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669163).length < 2 ^ (prefixWord ++ tailWord_669163).sum := by decide
  have hdescent : baseEnd_669163 < baseStart_669163 := by decide
  rcases family_descends (prefixWord ++ tailWord_669163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669177 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 4]
def baseStart_669177 : Nat := 118140960795 + 669177 * 2 ^ 59
def prefixEnd_669177 : Nat := 4983230072969 + 3 ^ 40 * 669177 * 2
def baseEnd_669177 : Nat := 152715308415037144715563

theorem tailTrace_669177 : CollatzResearch.WordTrace tailWord_669177 prefixEnd_669177 152715308415037144715563 := by
  unfold tailWord_669177
  simp only [CollatzResearch.WordTrace]
  refine ⟨24406890296693490177909785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16271260197795660118606523 24406890296693490177909785)
  ·
    refine ⟨18305167722520117633432339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24406890296693490177909785 18305167722520117633432339)
    ·
      refine ⟨27457751583780176450148509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18305167722520117633432339 27457751583780176450148509)
      ·
        refine ⟨10296656843917566168805691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27457751583780176450148509 10296656843917566168805691)
        ·
          refine ⟨15444985265876349253208537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10296656843917566168805691 15444985265876349253208537)
          ·
            refine ⟨11583738949407261939906403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15444985265876349253208537 11583738949407261939906403)
            ·
              refine ⟨17375608424110892909859605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11583738949407261939906403 17375608424110892909859605)
              ·
                refine ⟨814481644880198105149669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17375608424110892909859605 814481644880198105149669)
                ·
                  refine ⟨152715308415037144715563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814481644880198105149669 152715308415037144715563)
                  ·
                    rfl

theorem cell21_669177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_669177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669177 prefixEnd_669177 := by exact prefixLift 669177
  have htrace : WordTrace (prefixWord ++ tailWord_669177) baseStart_669177 baseEnd_669177 := by
    simpa [prefixWord, tailWord_669177, baseEnd_669177] using wordTrace_append hprefix tailTrace_669177
  have hstable : (prefixWord ++ tailWord_669177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669177).length < 2 ^ (prefixWord ++ tailWord_669177).sum := by decide
  have hdescent : baseEnd_669177 < baseStart_669177 := by decide
  rcases family_descends (prefixWord ++ tailWord_669177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669194 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_669194 : Nat := 118140960795 + 669194 * 2 ^ 59
def prefixEnd_669194 : Nat := 4983230072969 + 3 ^ 40 * 669194 * 2
def baseEnd_669194 : Nat := 152719188046648892932195

theorem tailTrace_669194 : CollatzResearch.WordTrace tailWord_669194 prefixEnd_669194 152719188046648892932195 := by
  unfold tailWord_669194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101877584407975520319659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16271673558421268054185757 6101877584407975520319659)
  ·
    refine ⟨9152816376611963280479489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6101877584407975520319659 9152816376611963280479489)
    ·
      refine ⟨6864612282458972460359617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9152816376611963280479489 6864612282458972460359617)
      ·
        refine ⟨5148459211844229345269713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6864612282458972460359617 5148459211844229345269713)
        ·
          refine ⟨3861344408883172008952285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5148459211844229345269713 3861344408883172008952285)
          ·
            refine ⟨1448004153331189503357107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3861344408883172008952285 1448004153331189503357107)
            ·
              refine ⟨2172006229996784255035661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448004153331189503357107 2172006229996784255035661)
              ·
                refine ⟨814502336248794095638373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2172006229996784255035661 814502336248794095638373)
                ·
                  refine ⟨152719188046648892932195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814502336248794095638373 152719188046648892932195)
                  ·
                    rfl

theorem cell21_669194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_669194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669194 prefixEnd_669194 := by exact prefixLift 669194
  have htrace : WordTrace (prefixWord ++ tailWord_669194) baseStart_669194 baseEnd_669194 := by
    simpa [prefixWord, tailWord_669194, baseEnd_669194] using wordTrace_append hprefix tailTrace_669194
  have hstable : (prefixWord ++ tailWord_669194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669194).length < 2 ^ (prefixWord ++ tailWord_669194).sum := by decide
  have hdescent : baseEnd_669194 < baseStart_669194 := by decide
  rcases family_descends (prefixWord ++ tailWord_669194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669253 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 4]
def baseStart_669253 : Nat := 118140960795 + 669253 * 2 ^ 59
def prefixEnd_669253 : Nat := 4983230072969 + 3 ^ 40 * 669253 * 2
def baseEnd_669253 : Nat := 152732652650477901448741

theorem tailTrace_669253 : CollatzResearch.WordTrace tailWord_669253 prefixEnd_669253 152732652650477901448741 := by
  unfold tailWord_669253
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409662244418155157676413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16273108162945436771784275 24409662244418155157676413)
  ·
    refine ⟨9153623341656808184128655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24409662244418155157676413 9153623341656808184128655)
    ·
      refine ⟨13730435012485212276192983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9153623341656808184128655 13730435012485212276192983)
      ·
        refine ⟨20595652518727818414289475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13730435012485212276192983 20595652518727818414289475)
        ·
          refine ⟨30893478778091727621434213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20595652518727818414289475 30893478778091727621434213)
          ·
            refine ⟨5792527270892198929018915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30893478778091727621434213 5792527270892198929018915)
            ·
              refine ⟨8688790906338298393528373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792527270892198929018915 8688790906338298393528373)
              ·
                refine ⟨814574147469215474393285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8688790906338298393528373 814574147469215474393285)
                ·
                  refine ⟨152732652650477901448741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814574147469215474393285 152732652650477901448741)
                  ·
                    rfl

theorem cell21_669253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_669253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669253 prefixEnd_669253 := by exact prefixLift 669253
  have htrace : WordTrace (prefixWord ++ tailWord_669253) baseStart_669253 baseEnd_669253 := by
    simpa [prefixWord, tailWord_669253, baseEnd_669253] using wordTrace_append hprefix tailTrace_669253
  have hstable : (prefixWord ++ tailWord_669253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669253).length < 2 ^ (prefixWord ++ tailWord_669253).sum := by decide
  have hdescent : baseEnd_669253 < baseStart_669253 := by decide
  rcases family_descends (prefixWord ++ tailWord_669253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669408 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_669408 : Nat := 118140960795 + 669408 * 2 ^ 59
def prefixEnd_669408 : Nat := 4983230072969 + 3 ^ 40 * 669408 * 2
def baseEnd_669408 : Nat := 152768025762232076365091

theorem tailTrace_669408 : CollatzResearch.WordTrace tailWord_669408 prefixEnd_669408 152768025762232076365091 := by
  unfold tailWord_669408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207657779428308314784439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16276877039237744419712585 12207657779428308314784439)
  ·
    refine ⟨18311486669142462472176659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12207657779428308314784439 18311486669142462472176659)
    ·
      refine ⟨27467230003713693708264989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18311486669142462472176659 27467230003713693708264989)
      ·
        refine ⟨10300211251392635140599371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27467230003713693708264989 10300211251392635140599371)
        ·
          refine ⟨15450316877088952710899057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10300211251392635140599371 15450316877088952710899057)
          ·
            refine ⟨11587737657816714533174293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15450316877088952710899057 11587737657816714533174293)
            ·
              refine ⟨543175202710158493742545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11587737657816714533174293 543175202710158493742545)
              ·
                refine ⟨407381402032618870306909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543175202710158493742545 407381402032618870306909)
                ·
                  refine ⟨152768025762232076365091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407381402032618870306909 152768025762232076365091)
                  ·
                    rfl

theorem cell21_669408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_669408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669408 prefixEnd_669408 := by exact prefixLift 669408
  have htrace : WordTrace (prefixWord ++ tailWord_669408) baseStart_669408 baseEnd_669408 := by
    simpa [prefixWord, tailWord_669408, baseEnd_669408] using wordTrace_append hprefix tailTrace_669408
  have hstable : (prefixWord ++ tailWord_669408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669408).length < 2 ^ (prefixWord ++ tailWord_669408).sum := by decide
  have hdescent : baseEnd_669408 < baseStart_669408 := by decide
  rcases family_descends (prefixWord ++ tailWord_669408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669419 : List Nat := [1, 1, 1, 1, 2, 4, 5, 6]
def baseStart_669419 : Nat := 118140960795 + 669419 * 2 ^ 59
def prefixEnd_669419 : Nat := 4983230072969 + 3 ^ 40 * 669419 * 2
def baseEnd_669419 : Nat := 50923512037366167227245

theorem tailTrace_669419 : CollatzResearch.WordTrace tailWord_669419 prefixEnd_669419 50923512037366167227245 := by
  unfold tailWord_669419
  simp only [CollatzResearch.WordTrace]
  refine ⟨24415716761816765508219311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16277144507877843672146207 24415716761816765508219311)
  ·
    refine ⟨36623575142725148262328967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24415716761816765508219311 36623575142725148262328967)
    ·
      refine ⟨54935362714087722393493451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36623575142725148262328967 54935362714087722393493451)
      ·
        refine ⟨82403044071131583590240177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54935362714087722393493451 82403044071131583590240177)
        ·
          refine ⟨61802283053348687692680133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82403044071131583590240177 61802283053348687692680133)
          ·
            refine ⟨11587928072502878942377525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61802283053348687692680133 11587928072502878942377525)
            ·
              refine ⟨1086368256797144900847893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11587928072502878942377525 1086368256797144900847893)
              ·
                refine ⟨50923512037366167227245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1086368256797144900847893 50923512037366167227245)
                ·
                  rfl

theorem cell21_669419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_669419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669419 prefixEnd_669419 := by exact prefixLift 669419
  have htrace : WordTrace (prefixWord ++ tailWord_669419) baseStart_669419 baseEnd_669419 := by
    simpa [prefixWord, tailWord_669419, baseEnd_669419] using wordTrace_append hprefix tailTrace_669419
  have hstable : (prefixWord ++ tailWord_669419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669419).length < 2 ^ (prefixWord ++ tailWord_669419).sum := by decide
  have hdescent : baseEnd_669419 < baseStart_669419 := by decide
  rcases family_descends (prefixWord ++ tailWord_669419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669436 : List Nat := [2, 2, 2, 1, 3, 1, 5, 5]
def baseStart_669436 : Nat := 118140960795 + 669436 * 2 ^ 59
def prefixEnd_669436 : Nat := 4983230072969 + 3 ^ 40 * 669436 * 2
def baseEnd_669436 : Nat := 50924805247903416632789

theorem tailTrace_669436 : CollatzResearch.WordTrace tailWord_669436 prefixEnd_669436 50924805247903416632789 := by
  unfold tailWord_669436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208168401377588705794081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16277557868503451607725441 12208168401377588705794081)
  ·
    refine ⟨9156126301033191529345561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12208168401377588705794081 9156126301033191529345561)
    ·
      refine ⟨6867094725774893647009171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9156126301033191529345561 6867094725774893647009171)
      ·
        refine ⟨10300642088662340470513757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6867094725774893647009171 10300642088662340470513757)
        ·
          refine ⟨3862740783248377676442659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10300642088662340470513757 3862740783248377676442659)
          ·
            refine ⟨5794111174872566514663989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862740783248377676442659 5794111174872566514663989)
            ·
              refine ⟨543197922644303110749749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5794111174872566514663989 543197922644303110749749)
              ·
                refine ⟨50924805247903416632789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 543197922644303110749749 50924805247903416632789)
                ·
                  rfl

theorem cell21_669436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_669436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669436 prefixEnd_669436 := by exact prefixLift 669436
  have htrace : WordTrace (prefixWord ++ tailWord_669436) baseStart_669436 baseEnd_669436 := by
    simpa [prefixWord, tailWord_669436, baseEnd_669436] using wordTrace_append hprefix tailTrace_669436
  have hstable : (prefixWord ++ tailWord_669436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669436).length < 2 ^ (prefixWord ++ tailWord_669436).sum := by decide
  have hdescent : baseEnd_669436 < baseStart_669436 := by decide
  rcases family_descends (prefixWord ++ tailWord_669436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669501 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 3]
def baseStart_669501 : Nat := 118140960795 + 669501 * 2 ^ 59
def prefixEnd_669501 : Nat := 4983230072969 + 3 ^ 40 * 669501 * 2
def baseEnd_669501 : Nat := 152789249629284581314901

theorem tailTrace_669501 : CollatzResearch.WordTrace tailWord_669501 prefixEnd_669501 152789249629284581314901 := by
  unfold tailWord_669501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24418707547519693512704357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16279138365013129008469571 24418707547519693512704357)
  ·
    refine ⟨4578507665159942533632067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24418707547519693512704357 4578507665159942533632067)
    ·
      refine ⟨6867761497739913800448101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4578507665159942533632067 6867761497739913800448101)
      ·
        refine ⟨1287705280826233837584019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6867761497739913800448101 1287705280826233837584019)
        ·
          refine ⟨1931557921239350756376029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287705280826233837584019 1931557921239350756376029)
          ·
            refine ⟨724334220464756533641011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1931557921239350756376029 724334220464756533641011)
            ·
              refine ⟨1086501330697134800461517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724334220464756533641011 1086501330697134800461517)
              ·
                refine ⟨407437999011425550173069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1086501330697134800461517 407437999011425550173069)
                ·
                  refine ⟨152789249629284581314901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407437999011425550173069 152789249629284581314901)
                  ·
                    rfl

theorem cell21_669501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_669501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669501 prefixEnd_669501 := by exact prefixLift 669501
  have htrace : WordTrace (prefixWord ++ tailWord_669501) baseStart_669501 baseEnd_669501 := by
    simpa [prefixWord, tailWord_669501, baseEnd_669501] using wordTrace_append hprefix tailTrace_669501
  have hstable : (prefixWord ++ tailWord_669501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669501).length < 2 ^ (prefixWord ++ tailWord_669501).sum := by decide
  have hdescent : baseEnd_669501 < baseStart_669501 := by decide
  rcases family_descends (prefixWord ++ tailWord_669501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669532 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_669532 : Nat := 118140960795 + 669532 * 2 ^ 59
def prefixEnd_669532 : Nat := 4983230072969 + 3 ^ 40 * 669532 * 2
def baseEnd_669532 : Nat := 152796324251635416298171

theorem tailTrace_669532 : CollatzResearch.WordTrace tailWord_669532 prefixEnd_669532 152796324251635416298171 := by
  unfold tailWord_669532
  simp only [CollatzResearch.WordTrace]
  refine ⟨12209919105203692903541425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16279892140271590538055233 12209919105203692903541425)
  ·
    refine ⟨9157439328902769677656069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12209919105203692903541425 9157439328902769677656069)
    ·
      refine ⟨1717019874169269314560513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9157439328902769677656069 1717019874169269314560513)
      ·
        refine ⟨1287764905626951985920385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717019874169269314560513 1287764905626951985920385)
        ·
          refine ⟨965823679220213989440289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1287764905626951985920385 965823679220213989440289)
          ·
            refine ⟨724367759415160492080217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965823679220213989440289 724367759415160492080217)
            ·
              refine ⟨543275819561370369060163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724367759415160492080217 543275819561370369060163)
              ·
                refine ⟨814913729342055553590245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543275819561370369060163 814913729342055553590245)
                ·
                  refine ⟨152796324251635416298171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814913729342055553590245 152796324251635416298171)
                  ·
                    rfl

theorem cell21_669532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_669532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669532 prefixEnd_669532 := by exact prefixLift 669532
  have htrace : WordTrace (prefixWord ++ tailWord_669532) baseStart_669532 baseEnd_669532 := by
    simpa [prefixWord, tailWord_669532, baseEnd_669532] using wordTrace_append hprefix tailTrace_669532
  have hstable : (prefixWord ++ tailWord_669532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669532).length < 2 ^ (prefixWord ++ tailWord_669532).sum := by decide
  have hdescent : baseEnd_669532 < baseStart_669532 := by decide
  rcases family_descends (prefixWord ++ tailWord_669532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669588 : List Nat := [2, 4, 2, 1, 1, 2, 3, 6]
def baseStart_669588 : Nat := 118140960795 + 669588 * 2 ^ 59
def prefixEnd_669588 : Nat := 4983230072969 + 3 ^ 40 * 669588 * 2
def baseEnd_669588 : Nat := 50936368071530587788241

theorem tailTrace_669588 : CollatzResearch.WordTrace tailWord_669588 prefixEnd_669588 50936368071530587788241 := by
  unfold tailWord_669588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12210940349102253685560709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16281253798803004914080945 12210940349102253685560709)
  ·
    refine ⟨2289551315456672566042633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12210940349102253685560709 2289551315456672566042633)
    ·
      refine ⟨1717163486592504424531975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2289551315456672566042633 1717163486592504424531975)
      ·
        refine ⟨2575745229888756636797963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717163486592504424531975 2575745229888756636797963)
        ·
          refine ⟨3863617844833134955196945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575745229888756636797963 3863617844833134955196945)
          ·
            refine ⟨2897713383624851216397709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3863617844833134955196945 2897713383624851216397709)
            ·
              refine ⟨1086642518859319206149141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2897713383624851216397709 1086642518859319206149141)
              ·
                refine ⟨50936368071530587788241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1086642518859319206149141 50936368071530587788241)
                ·
                  rfl

theorem cell21_669588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_669588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669588 prefixEnd_669588 := by exact prefixLift 669588
  have htrace : WordTrace (prefixWord ++ tailWord_669588) baseStart_669588 baseEnd_669588 := by
    simpa [prefixWord, tailWord_669588, baseEnd_669588] using wordTrace_append hprefix tailTrace_669588
  have hstable : (prefixWord ++ tailWord_669588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669588).length < 2 ^ (prefixWord ++ tailWord_669588).sum := by decide
  have hdescent : baseEnd_669588 < baseStart_669588 := by decide
  rcases family_descends (prefixWord ++ tailWord_669588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669619 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 3]
def baseStart_669619 : Nat := 118140960795 + 669619 * 2 ^ 59
def prefixEnd_669619 : Nat := 4983230072969 + 3 ^ 40 * 669619 * 2
def baseEnd_669619 : Nat := 152816178836942598347993

theorem tailTrace_669619 : CollatzResearch.WordTrace tailWord_669619 prefixEnd_669619 152816178836942598347993 := by
  unfold tailWord_669619
  simp only [CollatzResearch.WordTrace]
  refine ⟨24423011361092199665499911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16282007574061466443666607 24423011361092199665499911)
  ·
    refine ⟨36634517041638299498249867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24423011361092199665499911 36634517041638299498249867)
    ·
      refine ⟨54951775562457449247374801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36634517041638299498249867 54951775562457449247374801)
      ·
        refine ⟨41213831671843086935531101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54951775562457449247374801 41213831671843086935531101)
        ·
          refine ⟨15455186876941157600824163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41213831671843086935531101 15455186876941157600824163)
          ·
            refine ⟨23182780315411736401236245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15455186876941157600824163 23182780315411736401236245)
            ·
              refine ⟨1086692827284925143807949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23182780315411736401236245 1086692827284925143807949)
              ·
                refine ⟨407509810231846928927981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1086692827284925143807949 407509810231846928927981)
                ·
                  refine ⟨152816178836942598347993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407509810231846928927981 152816178836942598347993)
                  ·
                    rfl

theorem cell21_669619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 3].length) (baseStart_669619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669619 prefixEnd_669619 := by exact prefixLift 669619
  have htrace : WordTrace (prefixWord ++ tailWord_669619) baseStart_669619 baseEnd_669619 := by
    simpa [prefixWord, tailWord_669619, baseEnd_669619] using wordTrace_append hprefix tailTrace_669619
  have hstable : (prefixWord ++ tailWord_669619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669619).length < 2 ^ (prefixWord ++ tailWord_669619).sum := by decide
  have hdescent : baseEnd_669619 < baseStart_669619 := by decide
  rcases family_descends (prefixWord ++ tailWord_669619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669692 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_669692 : Nat := 118140960795 + 669692 * 2 ^ 59
def prefixEnd_669692 : Nat := 4983230072969 + 3 ^ 40 * 669692 * 2
def baseEnd_669692 : Nat := 152832838431510693631177

theorem tailTrace_669692 : CollatzResearch.WordTrace tailWord_669692 prefixEnd_669692 152832838431510693631177 := by
  unfold tailWord_669692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12212836944913866566453665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16283782593218488755271553 12212836944913866566453665)
  ·
    refine ⟨9159627708685399924840249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12212836944913866566453665 9159627708685399924840249)
    ·
      refine ⟨6869720781514049943630187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9159627708685399924840249 6869720781514049943630187)
      ·
        refine ⟨10304581172271074915445281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869720781514049943630187 10304581172271074915445281)
        ·
          refine ⟨7728435879203306186583961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10304581172271074915445281 7728435879203306186583961)
          ·
            refine ⟨5796326909402479639937971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7728435879203306186583961 5796326909402479639937971)
            ·
              refine ⟨8694490364103719459906957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796326909402479639937971 8694490364103719459906957)
              ·
                refine ⟨3260433886538894797465109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8694490364103719459906957 3260433886538894797465109)
                ·
                  refine ⟨152832838431510693631177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3260433886538894797465109 152832838431510693631177)
                  ·
                    rfl

theorem cell21_669692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_669692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669692 prefixEnd_669692 := by exact prefixLift 669692
  have htrace : WordTrace (prefixWord ++ tailWord_669692) baseStart_669692 baseEnd_669692 := by
    simpa [prefixWord, tailWord_669692, baseEnd_669692] using wordTrace_append hprefix tailTrace_669692
  have hstable : (prefixWord ++ tailWord_669692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669692).length < 2 ^ (prefixWord ++ tailWord_669692).sum := by decide
  have hdescent : baseEnd_669692 < baseStart_669692 := by decide
  rcases family_descends (prefixWord ++ tailWord_669692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669788 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_669788 : Nat := 118140960795 + 669788 * 2 ^ 59
def prefixEnd_669788 : Nat := 4983230072969 + 3 ^ 40 * 669788 * 2
def baseEnd_669788 : Nat := 152854746939435860030981

theorem tailTrace_669788 : CollatzResearch.WordTrace tailWord_669788 prefixEnd_669788 152854746939435860030981 := by
  unfold tailWord_669788
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214587648739970764201009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16286116864986627685601345 12214587648739970764201009)
  ·
    refine ⟨9160940736554978073150757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12214587648739970764201009 9160940736554978073150757)
    ·
      refine ⟨1717676388104058388715767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9160940736554978073150757 1717676388104058388715767)
      ·
        refine ⟨2576514582156087583073651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717676388104058388715767 2576514582156087583073651)
        ·
          refine ⟨3864771873234131374610477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576514582156087583073651 3864771873234131374610477)
          ·
            refine ⟨1449289452462799265478929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3864771873234131374610477 1449289452462799265478929)
            ·
              refine ⟨1086967089347099449109197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449289452462799265478929 1086967089347099449109197)
              ·
                refine ⟨407612658505162293415949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1086967089347099449109197 407612658505162293415949)
                ·
                  refine ⟨152854746939435860030981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407612658505162293415949 152854746939435860030981)
                  ·
                    rfl

theorem cell21_669788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_669788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669788 prefixEnd_669788 := by exact prefixLift 669788
  have htrace : WordTrace (prefixWord ++ tailWord_669788) baseStart_669788 baseEnd_669788 := by
    simpa [prefixWord, tailWord_669788, baseEnd_669788] using wordTrace_append hprefix tailTrace_669788
  have hstable : (prefixWord ++ tailWord_669788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669788).length < 2 ^ (prefixWord ++ tailWord_669788).sum := by decide
  have hdescent : baseEnd_669788 < baseStart_669788 := by decide
  rcases family_descends (prefixWord ++ tailWord_669788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669951 : List Nat := [1, 1, 2, 2, 1, 4, 5, 5]
def baseStart_669951 : Nat := 118140960795 + 669951 * 2 ^ 59
def prefixEnd_669951 : Nat := 4983230072969 + 3 ^ 40 * 669951 * 2
def baseEnd_669951 : Nat := 50963981920061266271327

theorem tailTrace_669951 : CollatzResearch.WordTrace tailWord_669951 prefixEnd_669951 50963981920061266271327 := by
  unfold tailWord_669951
  simp only [CollatzResearch.WordTrace]
  refine ⟨24435120395889420366585707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16290080263926280244390471 24435120395889420366585707)
  ·
    refine ⟨36652680593834130549878561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24435120395889420366585707 36652680593834130549878561)
    ·
      refine ⟨27489510445375597912408921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36652680593834130549878561 27489510445375597912408921)
      ·
        refine ⟨20617132834031698434306691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27489510445375597912408921 20617132834031698434306691)
        ·
          refine ⟨30925699251047547651460037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20617132834031698434306691 30925699251047547651460037)
          ·
            refine ⟨5798568609571415184648757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30925699251047547651460037 5798568609571415184648757)
            ·
              refine ⟨543615807147320173560821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5798568609571415184648757 543615807147320173560821)
              ·
                refine ⟨50963981920061266271327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 543615807147320173560821 50963981920061266271327)
                ·
                  rfl

theorem cell21_669951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 5].length) (baseStart_669951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669951 prefixEnd_669951 := by exact prefixLift 669951
  have htrace : WordTrace (prefixWord ++ tailWord_669951) baseStart_669951 baseEnd_669951 := by
    simpa [prefixWord, tailWord_669951, baseEnd_669951] using wordTrace_append hprefix tailTrace_669951
  have hstable : (prefixWord ++ tailWord_669951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669951).length < 2 ^ (prefixWord ++ tailWord_669951).sum := by decide
  have hdescent : baseEnd_669951 < baseStart_669951 := by decide
  rcases family_descends (prefixWord ++ tailWord_669951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669996 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_669996 : Nat := 118140960795 + 669996 * 2 ^ 59
def prefixEnd_669996 : Nat := 4983230072969 + 3 ^ 40 * 669996 * 2
def baseEnd_669996 : Nat := 152902215373273720563889

theorem tailTrace_669996 : CollatzResearch.WordTrace tailWord_669996 prefixEnd_669996 152902215373273720563889 := by
  unfold tailWord_669996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12218380840363196525986921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16291174453817595367982561 12218380840363196525986921)
  ·
    refine ⟨9163785630272397394490191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12218380840363196525986921 9163785630272397394490191)
    ·
      refine ⟨13745678445408596091735287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9163785630272397394490191 13745678445408596091735287)
      ·
        refine ⟨20618517668112894137602931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13745678445408596091735287 20618517668112894137602931)
        ·
          refine ⟨30927776502169341206404397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20618517668112894137602931 30927776502169341206404397)
          ·
            refine ⟨11597916188313502952401649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30927776502169341206404397 11597916188313502952401649)
            ·
              refine ⟨8698437141235127214301237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11597916188313502952401649 8698437141235127214301237)
              ·
                refine ⟨815478481990793176340741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8698437141235127214301237 815478481990793176340741)
                ·
                  refine ⟨152902215373273720563889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 815478481990793176340741 152902215373273720563889)
                  ·
                    rfl

theorem cell21_669996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_669996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_669996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_669996 prefixEnd_669996 := by exact prefixLift 669996
  have htrace : WordTrace (prefixWord ++ tailWord_669996) baseStart_669996 baseEnd_669996 := by
    simpa [prefixWord, tailWord_669996, baseEnd_669996] using wordTrace_append hprefix tailTrace_669996
  have hstable : (prefixWord ++ tailWord_669996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669996).length < 2 ^ (prefixWord ++ tailWord_669996).sum := by decide
  have hdescent : baseEnd_669996 < baseStart_669996 := by decide
  rcases family_descends (prefixWord ++ tailWord_669996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670089 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 4]
def baseStart_670089 : Nat := 118140960795 + 670089 * 2 ^ 59
def prefixEnd_670089 : Nat := 4983230072969 + 3 ^ 40 * 670089 * 2
def baseEnd_670089 : Nat := 152923439240326225513699

theorem tailTrace_670089 : CollatzResearch.WordTrace tailWord_670089 prefixEnd_670089 152923439240326225513699 := by
  unfold tailWord_670089
  simp only [CollatzResearch.WordTrace]
  refine ⟨24440153669389469935109321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16293435779592979956739547 24440153669389469935109321)
  ·
    refine ⟨18330115252042102451331991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24440153669389469935109321 18330115252042102451331991)
    ·
      refine ⟨27495172878063153676997987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18330115252042102451331991 27495172878063153676997987)
      ·
        refine ⟨41242759317094730515496981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27495172878063153676997987 41242759317094730515496981)
        ·
          refine ⟨1933254342988815492913921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41242759317094730515496981 1933254342988815492913921)
          ·
            refine ⟨1449940757241611619685441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1933254342988815492913921 1449940757241611619685441)
            ·
              refine ⟨1087455567931208714764081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449940757241611619685441 1087455567931208714764081)
              ·
                refine ⟨815591675948406536073061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087455567931208714764081 815591675948406536073061)
                ·
                  refine ⟨152923439240326225513699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 815591675948406536073061 152923439240326225513699)
                  ·
                    rfl

theorem cell21_670089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_670089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670089 prefixEnd_670089 := by exact prefixLift 670089
  have htrace : WordTrace (prefixWord ++ tailWord_670089) baseStart_670089 baseEnd_670089 := by
    simpa [prefixWord, tailWord_670089, baseEnd_670089] using wordTrace_append hprefix tailTrace_670089
  have hstable : (prefixWord ++ tailWord_670089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670089).length < 2 ^ (prefixWord ++ tailWord_670089).sum := by decide
  have hdescent : baseEnd_670089 < baseStart_670089 := by decide
  rcases family_descends (prefixWord ++ tailWord_670089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670092 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_670092 : Nat := 118140960795 + 670092 * 2 ^ 59
def prefixEnd_670092 : Nat := 4983230072969 + 3 ^ 40 * 670092 * 2
def baseEnd_670092 : Nat := 152924123881198886963693

theorem tailTrace_670092 : CollatzResearch.WordTrace tailWord_670092 prefixEnd_670092 152924123881198886963693 := by
  unfold tailWord_670092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12220131544189300723734265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16293508725585734298312353 12220131544189300723734265)
  ·
    refine ⟨9165098658141975542800699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12220131544189300723734265 9165098658141975542800699)
    ·
      refine ⟨13747647987212963314201049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9165098658141975542800699 13747647987212963314201049)
      ·
        refine ⟨10310735990409722485650787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13747647987212963314201049 10310735990409722485650787)
        ·
          refine ⟨15466103985614583728476181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310735990409722485650787 15466103985614583728476181)
          ·
            refine ⟨724973624325683612272321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15466103985614583728476181 724973624325683612272321)
            ·
              refine ⟨543730218244262709204241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724973624325683612272321 543730218244262709204241)
              ·
                refine ⟨407797663683197031903181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543730218244262709204241 407797663683197031903181)
                ·
                  refine ⟨152924123881198886963693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407797663683197031903181 152924123881198886963693)
                  ·
                    rfl

theorem cell21_670092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_670092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670092 prefixEnd_670092 := by exact prefixLift 670092
  have htrace : WordTrace (prefixWord ++ tailWord_670092) baseStart_670092 baseEnd_670092 := by
    simpa [prefixWord, tailWord_670092, baseEnd_670092] using wordTrace_append hprefix tailTrace_670092
  have hstable : (prefixWord ++ tailWord_670092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670092).length < 2 ^ (prefixWord ++ tailWord_670092).sum := by decide
  have hdescent : baseEnd_670092 < baseStart_670092 := by decide
  rcases family_descends (prefixWord ++ tailWord_670092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670117 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_670117 : Nat := 118140960795 + 670117 * 2 ^ 59
def prefixEnd_670117 : Nat := 4983230072969 + 3 ^ 40 * 670117 * 2
def baseEnd_670117 : Nat := 152929829221804399046975

theorem tailTrace_670117 : CollatzResearch.WordTrace tailWord_670117 prefixEnd_670117 152929829221804399046975 := by
  unfold tailWord_670117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441174913288030717128605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16294116608858687144752403 24441174913288030717128605)
  ·
    refine ⟨9165440592483011518923227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24441174913288030717128605 9165440592483011518923227)
    ·
      refine ⟨13748160888724517278384841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9165440592483011518923227 13748160888724517278384841)
      ·
        refine ⟨10311120666543387958788631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13748160888724517278384841 10311120666543387958788631)
        ·
          refine ⟨15466680999815081938182947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10311120666543387958788631 15466680999815081938182947)
          ·
            refine ⟨23200021499722622907274421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15466680999815081938182947 23200021499722622907274421)
            ·
              refine ⟨2175002015598995897556977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23200021499722622907274421 2175002015598995897556977)
              ·
                refine ⟨1631251511699246923167733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2175002015598995897556977 1631251511699246923167733)
                ·
                  refine ⟨152929829221804399046975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1631251511699246923167733 152929829221804399046975)
                  ·
                    rfl

theorem cell21_670117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_670117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670117 prefixEnd_670117 := by exact prefixLift 670117
  have htrace : WordTrace (prefixWord ++ tailWord_670117) baseStart_670117 baseEnd_670117 := by
    simpa [prefixWord, tailWord_670117, baseEnd_670117] using wordTrace_append hprefix tailTrace_670117
  have hstable : (prefixWord ++ tailWord_670117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670117).length < 2 ^ (prefixWord ++ tailWord_670117).sum := by decide
  have hdescent : baseEnd_670117 < baseStart_670117 := by decide
  rcases family_descends (prefixWord ++ tailWord_670117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670179 : List Nat := [1, 1, 1, 6, 3, 1, 1, 7]
def baseStart_670179 : Nat := 118140960795 + 670179 * 2 ^ 59
def prefixEnd_670179 : Nat := 4983230072969 + 3 ^ 40 * 670179 * 2
def baseEnd_670179 : Nat := 50981326155502023004505

theorem tailTrace_670179 : CollatzResearch.WordTrace tailWord_670179 prefixEnd_670179 50981326155502023004505 := by
  unfold tailWord_670179
  simp only [CollatzResearch.WordTrace]
  refine ⟨24443436239063415305885591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16295624159375610203923727 24443436239063415305885591)
  ·
    refine ⟨36665154358595122958828387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24443436239063415305885591 36665154358595122958828387)
    ·
      refine ⟨54997731537892684438242581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36665154358595122958828387 54997731537892684438242581)
      ·
        refine ⟨2578018665838719583042621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54997731537892684438242581 2578018665838719583042621)
        ·
          refine ⟨966756999689519843640983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2578018665838719583042621 966756999689519843640983)
          ·
            refine ⟨1450135499534279765461475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966756999689519843640983 1450135499534279765461475)
            ·
              refine ⟨2175203249301419648192213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450135499534279765461475 2175203249301419648192213)
              ·
                refine ⟨50981326155502023004505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2175203249301419648192213 50981326155502023004505)
                ·
                  rfl

theorem cell21_670179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_670179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670179 prefixEnd_670179 := by exact prefixLift 670179
  have htrace : WordTrace (prefixWord ++ tailWord_670179) baseStart_670179 baseEnd_670179 := by
    simpa [prefixWord, tailWord_670179, baseEnd_670179] using wordTrace_append hprefix tailTrace_670179
  have hstable : (prefixWord ++ tailWord_670179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670179).length < 2 ^ (prefixWord ++ tailWord_670179).sum := by decide
  have hdescent : baseEnd_670179 < baseStart_670179 := by decide
  rcases family_descends (prefixWord ++ tailWord_670179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670207 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_670207 : Nat := 118140960795 + 670207 * 2 ^ 59
def prefixEnd_670207 : Nat := 4983230072969 + 3 ^ 40 * 670207 * 2
def baseEnd_670207 : Nat := 152950368447984242546791

theorem tailTrace_670207 : CollatzResearch.WordTrace tailWord_670207 prefixEnd_670207 152950368447984242546791 := by
  unfold tailWord_670207
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444457482961976087904875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16296304988641317391936583 24444457482961976087904875)
  ·
    refine ⟨36666686224442964131857313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24444457482961976087904875 36666686224442964131857313)
    ·
      refine ⟨27500014668332223098892985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36666686224442964131857313 27500014668332223098892985)
      ·
        refine ⟨20625011001249167324169739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27500014668332223098892985 20625011001249167324169739)
        ·
          refine ⟨30937516501873750986254609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20625011001249167324169739 30937516501873750986254609)
          ·
            refine ⟨23203137376405313239690957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30937516501873750986254609 23203137376405313239690957)
            ·
              refine ⟨8701176516151992464884109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23203137376405313239690957 8701176516151992464884109)
              ·
                refine ⟨3262941193556997174331541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8701176516151992464884109 3262941193556997174331541)
                ·
                  refine ⟨152950368447984242546791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3262941193556997174331541 152950368447984242546791)
                  ·
                    rfl

theorem cell21_670207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_670207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670207 prefixEnd_670207 := by exact prefixLift 670207
  have htrace : WordTrace (prefixWord ++ tailWord_670207) baseStart_670207 baseEnd_670207 := by
    simpa [prefixWord, tailWord_670207, baseEnd_670207] using wordTrace_append hprefix tailTrace_670207
  have hstable : (prefixWord ++ tailWord_670207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670207).length < 2 ^ (prefixWord ++ tailWord_670207).sum := by decide
  have hdescent : baseEnd_670207 < baseStart_670207 := by decide
  rcases family_descends (prefixWord ++ tailWord_670207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670314 : List Nat := [3, 1, 3, 2, 1, 1, 10]
def baseStart_670314 : Nat := 118140960795 + 670314 * 2 ^ 59
def prefixEnd_670314 : Nat := 4983230072969 + 3 ^ 40 * 670314 * 2
def baseEnd_670314 : Nat := 16997198589530648251471

theorem tailTrace_670314 : CollatzResearch.WordTrace tailWord_670314 prefixEnd_670314 16997198589530648251471 := by
  unfold tailWord_670314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6112090023393583340512499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16298906729049555574699997 6112090023393583340512499)
  ·
    refine ⟨9168135035090375010768749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6112090023393583340512499 9168135035090375010768749)
    ·
      refine ⟨3438050638158890629038281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9168135035090375010768749 3438050638158890629038281)
      ·
        refine ⟨2578537978619167971778711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3438050638158890629038281 2578537978619167971778711)
        ·
          refine ⟨3867806967928751957668067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578537978619167971778711 3867806967928751957668067)
          ·
            refine ⟨5801710451893127936502101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867806967928751957668067 5801710451893127936502101)
            ·
              refine ⟨16997198589530648251471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5801710451893127936502101 16997198589530648251471)
              ·
                rfl

theorem cell21_670314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 10].length) (baseStart_670314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670314 prefixEnd_670314 := by exact prefixLift 670314
  have htrace : WordTrace (prefixWord ++ tailWord_670314) baseStart_670314 baseEnd_670314 := by
    simpa [prefixWord, tailWord_670314, baseEnd_670314] using wordTrace_append hprefix tailTrace_670314
  have hstable : (prefixWord ++ tailWord_670314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670314).length < 2 ^ (prefixWord ++ tailWord_670314).sum := by decide
  have hdescent : baseEnd_670314 < baseStart_670314 := by decide
  rcases family_descends (prefixWord ++ tailWord_670314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670317 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 4]
def baseStart_670317 : Nat := 118140960795 + 670317 * 2 ^ 59
def prefixEnd_670317 : Nat := 4983230072969 + 3 ^ 40 * 670317 * 2
def baseEnd_670317 : Nat := 152975471946648495713233

theorem tailTrace_670317 : CollatzResearch.WordTrace tailWord_670317 prefixEnd_670317 152975471946648495713233 := by
  unfold tailWord_670317
  simp only [CollatzResearch.WordTrace]
  refine ⟨24448469512563464874409205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16298979675042309916272803 24448469512563464874409205)
  ·
    refine ⟨2292044016802824831975863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24448469512563464874409205 2292044016802824831975863)
    ·
      refine ⟨3438066025204237247963795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2292044016802824831975863 3438066025204237247963795)
      ·
        refine ⟨5157099037806355871945693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3438066025204237247963795 5157099037806355871945693)
        ·
          refine ⟨1933912139177383451979635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5157099037806355871945693 1933912139177383451979635)
          ·
            refine ⟨2900868208766075177969453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933912139177383451979635 2900868208766075177969453)
            ·
              refine ⟨1087825578287278191738545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2900868208766075177969453 1087825578287278191738545)
              ·
                refine ⟨815869183715458643803909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087825578287278191738545 815869183715458643803909)
                ·
                  refine ⟨152975471946648495713233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 815869183715458643803909 152975471946648495713233)
                  ·
                    rfl

theorem cell21_670317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_670317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670317 prefixEnd_670317 := by exact prefixLift 670317
  have htrace : WordTrace (prefixWord ++ tailWord_670317) baseStart_670317 baseEnd_670317 := by
    simpa [prefixWord, tailWord_670317, baseEnd_670317] using wordTrace_append hprefix tailTrace_670317
  have hstable : (prefixWord ++ tailWord_670317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670317).length < 2 ^ (prefixWord ++ tailWord_670317).sum := by decide
  have hdescent : baseEnd_670317 < baseStart_670317 := by decide
  rcases family_descends (prefixWord ++ tailWord_670317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670328 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_670328 : Nat := 118140960795 + 670328 * 2 ^ 59
def prefixEnd_670328 : Nat := 4983230072969 + 3 ^ 40 * 670328 * 2
def baseEnd_670328 : Nat := 152977982296514921029877

theorem tailTrace_670328 : CollatzResearch.WordTrace tailWord_670328 prefixEnd_670328 152977982296514921029877 := by
  unfold tailWord_670328
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224435357761806876529819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16299247143682409168706425 12224435357761806876529819)
  ·
    refine ⟨18336653036642710314794729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12224435357761806876529819 18336653036642710314794729)
    ·
      refine ⟨13752489777482032736096047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18336653036642710314794729 13752489777482032736096047)
      ·
        refine ⟨20628734666223049104144071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13752489777482032736096047 20628734666223049104144071)
        ·
          refine ⟨30943101999334573656216107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20628734666223049104144071 30943101999334573656216107)
          ·
            refine ⟨46414652999001860484324161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30943101999334573656216107 46414652999001860484324161)
            ·
              refine ⟨34810989749251395363243121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46414652999001860484324161 34810989749251395363243121)
              ·
                refine ⟨26108242311938546522432341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34810989749251395363243121 26108242311938546522432341)
                ·
                  refine ⟨152977982296514921029877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26108242311938546522432341 152977982296514921029877)
                  ·
                    rfl

theorem cell21_670328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_670328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670328 prefixEnd_670328 := by exact prefixLift 670328
  have htrace : WordTrace (prefixWord ++ tailWord_670328) baseStart_670328 baseEnd_670328 := by
    simpa [prefixWord, tailWord_670328, baseEnd_670328] using wordTrace_append hprefix tailTrace_670328
  have hstable : (prefixWord ++ tailWord_670328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670328).length < 2 ^ (prefixWord ++ tailWord_670328).sum := by decide
  have hdescent : baseEnd_670328 < baseStart_670328 := by decide
  rcases family_descends (prefixWord ++ tailWord_670328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670359 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_670359 : Nat := 118140960795 + 670359 * 2 ^ 59
def prefixEnd_670359 : Nat := 4983230072969 + 3 ^ 40 * 670359 * 2
def baseEnd_670359 : Nat := 152985056918865756013147

theorem tailTrace_670359 : CollatzResearch.WordTrace tailWord_670359 prefixEnd_670359 152985056918865756013147 := by
  unfold tailWord_670359
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450001378411306047438131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16300000918940870698292087 24450001378411306047438131)
  ·
    refine ⟨36675002067616959071157197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24450001378411306047438131 36675002067616959071157197)
    ·
      refine ⟨13753125775356359651683949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36675002067616959071157197 13753125775356359651683949)
      ·
        refine ⟨5157422165758634869381481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13753125775356359651683949 5157422165758634869381481)
        ·
          refine ⟨3868066624318976152036111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5157422165758634869381481 3868066624318976152036111)
          ·
            refine ⟨5802099936478464228054167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868066624318976152036111 5802099936478464228054167)
            ·
              refine ⟨8703149904717696342081251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802099936478464228054167 8703149904717696342081251)
              ·
                refine ⟨13054724857076544513121877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8703149904717696342081251 13054724857076544513121877)
                ·
                  refine ⟨152985056918865756013147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13054724857076544513121877 152985056918865756013147)
                  ·
                    rfl

theorem cell21_670359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_670359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670359 prefixEnd_670359 := by exact prefixLift 670359
  have htrace : WordTrace (prefixWord ++ tailWord_670359) baseStart_670359 baseEnd_670359 := by
    simpa [prefixWord, tailWord_670359, baseEnd_670359] using wordTrace_append hprefix tailTrace_670359
  have hstable : (prefixWord ++ tailWord_670359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670359).length < 2 ^ (prefixWord ++ tailWord_670359).sum := by decide
  have hdescent : baseEnd_670359 < baseStart_670359 := by decide
  rcases family_descends (prefixWord ++ tailWord_670359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670497 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 5]
def baseStart_670497 : Nat := 118140960795 + 670497 * 2 ^ 59
def prefixEnd_670497 : Nat := 4983230072969 + 3 ^ 40 * 670497 * 2
def baseEnd_670497 : Nat := 153016550399008182712865

theorem tailTrace_670497 : CollatzResearch.WordTrace tailWord_670497 prefixEnd_670497 153016550399008182712865 := by
  unfold tailWord_670497
  simp only [CollatzResearch.WordTrace]
  refine ⟨24455034651911355615961745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16303356434607570410641163 24455034651911355615961745)
  ·
    refine ⟨18341275988933516711971309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24455034651911355615961745 18341275988933516711971309)
    ·
      refine ⟨6877978495850068766989241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18341275988933516711971309 6877978495850068766989241)
      ·
        refine ⟨5158483871887551575241931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6877978495850068766989241 5158483871887551575241931)
        ·
          refine ⟨7737725807831327362862897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158483871887551575241931 7737725807831327362862897)
          ·
            refine ⟨5803294355873495522147173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737725807831327362862897 5803294355873495522147173)
            ·
              refine ⟨1088117691726280410402595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5803294355873495522147173 1088117691726280410402595)
              ·
                refine ⟨1632176537589420615603893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088117691726280410402595 1632176537589420615603893)
                ·
                  refine ⟨153016550399008182712865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1632176537589420615603893 153016550399008182712865)
                  ·
                    rfl

theorem cell21_670497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_670497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670497 prefixEnd_670497 := by exact prefixLift 670497
  have htrace : WordTrace (prefixWord ++ tailWord_670497) baseStart_670497 baseEnd_670497 := by
    simpa [prefixWord, tailWord_670497, baseEnd_670497] using wordTrace_append hprefix tailTrace_670497
  have hstable : (prefixWord ++ tailWord_670497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670497).length < 2 ^ (prefixWord ++ tailWord_670497).sum := by decide
  have hdescent : baseEnd_670497 < baseStart_670497 := by decide
  rcases family_descends (prefixWord ++ tailWord_670497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670548 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_670548 : Nat := 118140960795 + 670548 * 2 ^ 59
def prefixEnd_670548 : Nat := 4983230072969 + 3 ^ 40 * 670548 * 2
def baseEnd_670548 : Nat := 153028189293843427362761

theorem tailTrace_670548 : CollatzResearch.WordTrace tailWord_670548 prefixEnd_670548 153028189293843427362761 := by
  unfold tailWord_670548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228447387363295663034149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16304596516484394217378865 12228447387363295663034149)
  ·
    refine ⟨2292833885130617936818903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12228447387363295663034149 2292833885130617936818903)
    ·
      refine ⟨3439250827695926905228355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2292833885130617936818903 3439250827695926905228355)
      ·
        refine ⟨5158876241543890357842533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3439250827695926905228355 5158876241543890357842533)
        ·
          refine ⟨967289295289479442095475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5158876241543890357842533 967289295289479442095475)
          ·
            refine ⟨1450933942934219163143213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967289295289479442095475 1450933942934219163143213)
            ·
              refine ⟨544100228600332186178705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1450933942934219163143213 544100228600332186178705)
              ·
                refine ⟨408075171450249139634029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544100228600332186178705 408075171450249139634029)
                ·
                  refine ⟨153028189293843427362761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408075171450249139634029 153028189293843427362761)
                  ·
                    rfl

theorem cell21_670548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_670548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670548 prefixEnd_670548 := by exact prefixLift 670548
  have htrace : WordTrace (prefixWord ++ tailWord_670548) baseStart_670548 baseEnd_670548 := by
    simpa [prefixWord, tailWord_670548, baseEnd_670548] using wordTrace_append hprefix tailTrace_670548
  have hstable : (prefixWord ++ tailWord_670548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670548).length < 2 ^ (prefixWord ++ tailWord_670548).sum := by decide
  have hdescent : baseEnd_670548 < baseStart_670548 := by decide
  rcases family_descends (prefixWord ++ tailWord_670548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670601 : List Nat := [1, 2, 1, 1, 5, 11]
def baseStart_670601 : Nat := 118140960795 + 670601 * 2 ^ 59
def prefixEnd_670601 : Nat := 4983230072969 + 3 ^ 40 * 670601 * 2
def baseEnd_670601 : Nat := 5668158689478781962197

theorem tailTrace_670601 : CollatzResearch.WordTrace tailWord_670601 prefixEnd_670601 5668158689478781962197 := by
  unfold tailWord_670601
  simp only [CollatzResearch.WordTrace]
  refine ⟨24458827843534581377747657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16305885229023054251831771 24458827843534581377747657)
  ·
    refine ⟨18344120882650936033310743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24458827843534581377747657 18344120882650936033310743)
    ·
      refine ⟨27516181323976404049966115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18344120882650936033310743 27516181323976404049966115)
      ·
        refine ⟨41274271985964606074949173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27516181323976404049966115 41274271985964606074949173)
        ·
          refine ⟨3869462998684181819526485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41274271985964606074949173 3869462998684181819526485)
          ·
            refine ⟨5668158689478781962197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3869462998684181819526485 5668158689478781962197)
            ·
              rfl

theorem cell21_670601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 11].length) (baseStart_670601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670601 prefixEnd_670601 := by exact prefixLift 670601
  have htrace : WordTrace (prefixWord ++ tailWord_670601) baseStart_670601 baseEnd_670601 := by
    simpa [prefixWord, tailWord_670601, baseEnd_670601] using wordTrace_append hprefix tailTrace_670601
  have hstable : (prefixWord ++ tailWord_670601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670601).length < 2 ^ (prefixWord ++ tailWord_670601).sum := by decide
  have hdescent : baseEnd_670601 < baseStart_670601 := by decide
  rcases family_descends (prefixWord ++ tailWord_670601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670784 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_670784 : Nat := 118140960795 + 670784 * 2 ^ 59
def prefixEnd_670784 : Nat := 4983230072969 + 3 ^ 40 * 670784 * 2
def baseEnd_670784 : Nat := 153082047709159461428945

theorem tailTrace_670784 : CollatzResearch.WordTrace tailWord_670784 prefixEnd_670784 153082047709159461428945 := by
  unfold tailWord_670784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12232751200935801815829703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16310334934581069087772937 12232751200935801815829703)
  ·
    refine ⟨18349126801403702723744555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12232751200935801815829703 18349126801403702723744555)
    ·
      refine ⟨27523690202105554085616833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18349126801403702723744555 27523690202105554085616833)
      ·
        refine ⟨20642767651579165564212625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27523690202105554085616833 20642767651579165564212625)
        ·
          refine ⟨15482075738684374173159469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20642767651579165564212625 15482075738684374173159469)
          ·
            refine ⟨5805778402006640314934801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15482075738684374173159469 5805778402006640314934801)
            ·
              refine ⟨4354333801504980236201101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805778402006640314934801 4354333801504980236201101)
              ·
                refine ⟨1632875175564367588575413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4354333801504980236201101 1632875175564367588575413)
                ·
                  refine ⟨153082047709159461428945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1632875175564367588575413 153082047709159461428945)
                  ·
                    rfl

theorem cell21_670784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_670784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670784 prefixEnd_670784 := by exact prefixLift 670784
  have htrace : WordTrace (prefixWord ++ tailWord_670784) baseStart_670784 baseEnd_670784 := by
    simpa [prefixWord, tailWord_670784, baseEnd_670784] using wordTrace_append hprefix tailTrace_670784
  have hstable : (prefixWord ++ tailWord_670784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670784).length < 2 ^ (prefixWord ++ tailWord_670784).sum := by decide
  have hdescent : baseEnd_670784 < baseStart_670784 := by decide
  rcases family_descends (prefixWord ++ tailWord_670784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670849 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 4]
def baseStart_670849 : Nat := 118140960795 + 670849 * 2 ^ 59
def prefixEnd_670849 : Nat := 4983230072969 + 3 ^ 40 * 670849 * 2
def baseEnd_670849 : Nat := 153096881594733792845479

theorem tailTrace_670849 : CollatzResearch.WordTrace tailWord_670849 prefixEnd_670849 153096881594733792845479 := by
  unfold tailWord_670849
  simp only [CollatzResearch.WordTrace]
  refine ⟨24467873146636119732775601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16311915431090746488517067 24467873146636119732775601)
  ·
    refine ⟨18350904859977089799581701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24467873146636119732775601 18350904859977089799581701)
    ·
      refine ⟨3440794661245704337421569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18350904859977089799581701 3440794661245704337421569)
      ·
        refine ⟨2580595995934278253066177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3440794661245704337421569 2580595995934278253066177)
        ·
          refine ⟨1935446996950708689799633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580595995934278253066177 1935446996950708689799633)
          ·
            refine ⟨1451585247713031517349725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935446996950708689799633 1451585247713031517349725)
            ·
              refine ⟨544344467892386819006147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451585247713031517349725 544344467892386819006147)
              ·
                refine ⟨816516701838580228509221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544344467892386819006147 816516701838580228509221)
                ·
                  refine ⟨153096881594733792845479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816516701838580228509221 153096881594733792845479)
                  ·
                    rfl

theorem cell21_670849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_670849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670849 prefixEnd_670849 := by exact prefixLift 670849
  have htrace : WordTrace (prefixWord ++ tailWord_670849) baseStart_670849 baseEnd_670849 := by
    simpa [prefixWord, tailWord_670849, baseEnd_670849] using wordTrace_append hprefix tailTrace_670849
  have hstable : (prefixWord ++ tailWord_670849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670849).length < 2 ^ (prefixWord ++ tailWord_670849).sum := by decide
  have hdescent : baseEnd_670849 < baseStart_670849 := by decide
  rcases family_descends (prefixWord ++ tailWord_670849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670905 : List Nat := [1, 2, 1, 4, 1, 3, 1, 8]
def baseStart_670905 : Nat := 118140960795 + 670905 * 2 ^ 59
def prefixEnd_670905 : Nat := 4983230072969 + 3 ^ 40 * 670905 * 2
def baseEnd_670905 : Nat := 51036553852563379970677

theorem tailTrace_670905 : CollatzResearch.WordTrace tailWord_670905 prefixEnd_670905 51036553852563379970677 := by
  unfold tailWord_670905
  simp only [CollatzResearch.WordTrace]
  refine ⟨24469915634433241296814169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16313277089622160864542779 24469915634433241296814169)
  ·
    refine ⟨18352436725824930972610627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24469915634433241296814169 18352436725824930972610627)
    ·
      refine ⟨27528655088737396458915941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18352436725824930972610627 27528655088737396458915941)
      ·
        refine ⟨5161622829138261836046739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27528655088737396458915941 5161622829138261836046739)
        ·
          refine ⟨7742434243707392754070109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161622829138261836046739 7742434243707392754070109)
          ·
            refine ⟨2903412841390272282776291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7742434243707392754070109 2903412841390272282776291)
            ·
              refine ⟨4355119262085408424164437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903412841390272282776291 4355119262085408424164437)
              ·
                refine ⟨51036553852563379970677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4355119262085408424164437 51036553852563379970677)
                ·
                  rfl

theorem cell21_670905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_670905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670905 prefixEnd_670905 := by exact prefixLift 670905
  have htrace : WordTrace (prefixWord ++ tailWord_670905) baseStart_670905 baseEnd_670905 := by
    simpa [prefixWord, tailWord_670905, baseEnd_670905] using wordTrace_append hprefix tailTrace_670905
  have hstable : (prefixWord ++ tailWord_670905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670905).length < 2 ^ (prefixWord ++ tailWord_670905).sum := by decide
  have hdescent : baseEnd_670905 < baseStart_670905 := by decide
  rcases family_descends (prefixWord ++ tailWord_670905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670908 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_670908 : Nat := 118140960795 + 670908 * 2 ^ 59
def prefixEnd_670908 : Nat := 4983230072969 + 3 ^ 40 * 670908 * 2
def baseEnd_670908 : Nat := 153110346198562801362025

theorem tailTrace_670908 : CollatzResearch.WordTrace tailWord_670908 prefixEnd_670908 153110346198562801362025 := by
  unfold tailWord_670908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12235012526711186404586689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16313350035614915206115585 12235012526711186404586689)
  ·
    refine ⟨9176259395033389803440017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12235012526711186404586689 9176259395033389803440017)
    ·
      refine ⟨6882194546275042352580013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9176259395033389803440017 6882194546275042352580013)
      ·
        refine ⟨2580822954853140882217505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6882194546275042352580013 2580822954853140882217505)
        ·
          refine ⟨1935617216139855661663129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580822954853140882217505 1935617216139855661663129)
          ·
            refine ⟨1451712912104891746247347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935617216139855661663129 1451712912104891746247347)
            ·
              refine ⟨2177569368157337619371021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451712912104891746247347 2177569368157337619371021)
              ·
                refine ⟨816588513059001607264133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2177569368157337619371021 816588513059001607264133)
                ·
                  refine ⟨153110346198562801362025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816588513059001607264133 153110346198562801362025)
                  ·
                    rfl

theorem cell21_670908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_670908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_670908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_670908 prefixEnd_670908 := by exact prefixLift 670908
  have htrace : WordTrace (prefixWord ++ tailWord_670908) baseStart_670908 baseEnd_670908 := by
    simpa [prefixWord, tailWord_670908, baseEnd_670908] using wordTrace_append hprefix tailTrace_670908
  have hstable : (prefixWord ++ tailWord_670908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670908).length < 2 ^ (prefixWord ++ tailWord_670908).sum := by decide
  have hdescent : baseEnd_670908 < baseStart_670908 := by decide
  rcases family_descends (prefixWord ++ tailWord_670908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671074 : List Nat := [3, 3, 2, 1, 1, 1, 4, 6]
def baseStart_671074 : Nat := 118140960795 + 671074 * 2 ^ 59
def prefixEnd_671074 : Nat := 4983230072969 + 3 ^ 40 * 671074 * 2
def baseEnd_671074 : Nat := 51049409886727800531673

theorem tailTrace_671074 : CollatzResearch.WordTrace tailWord_671074 prefixEnd_671074 51049409886727800531673 := by
  unfold tailWord_671074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119019892705245789929069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16317386380547322106477517 6119019892705245789929069)
  ·
    refine ⟨2294632459764467171223401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6119019892705245789929069 2294632459764467171223401)
    ·
      refine ⟨1720974344823350378417551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2294632459764467171223401 1720974344823350378417551)
      ·
        refine ⟨2581461517235025567626327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720974344823350378417551 2581461517235025567626327)
        ·
          refine ⟨3872192275852538351439491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581461517235025567626327 3872192275852538351439491)
          ·
            refine ⟨5808288413778807527159237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872192275852538351439491 5808288413778807527159237)
            ·
              refine ⟨1089054077583526411342357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5808288413778807527159237 1089054077583526411342357)
              ·
                refine ⟨51049409886727800531673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1089054077583526411342357 51049409886727800531673)
                ·
                  rfl

theorem cell21_671074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_671074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671074 prefixEnd_671074 := by exact prefixLift 671074
  have htrace : WordTrace (prefixWord ++ tailWord_671074) baseStart_671074 baseEnd_671074 := by
    simpa [prefixWord, tailWord_671074, baseEnd_671074] using wordTrace_append hprefix tailTrace_671074
  have hstable : (prefixWord ++ tailWord_671074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671074).length < 2 ^ (prefixWord ++ tailWord_671074).sum := by decide
  have hdescent : baseEnd_671074 < baseStart_671074 := by decide
  rcases family_descends (prefixWord ++ tailWord_671074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671240 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_671240 : Nat := 118140960795 + 671240 * 2 ^ 59
def prefixEnd_671240 : Nat := 4983230072969 + 3 ^ 40 * 671240 * 2
def baseEnd_671240 : Nat := 153186113121804001828013

theorem tailTrace_671240 : CollatzResearch.WordTrace tailWord_671240 prefixEnd_671240 153186113121804001828013 := by
  unfold tailWord_671240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12241067044109796755129587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16321422725479729006839449 12241067044109796755129587)
  ·
    refine ⟨18361600566164695132694381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12241067044109796755129587 18361600566164695132694381)
    ·
      refine ⟨6885600212311760674760393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18361600566164695132694381 6885600212311760674760393)
      ·
        refine ⟨5164200159233820506070295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6885600212311760674760393 5164200159233820506070295)
        ·
          refine ⟨7746300238850730759105443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164200159233820506070295 7746300238850730759105443)
          ·
            refine ⟨11619450358276096138658165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746300238850730759105443 11619450358276096138658165)
            ·
              refine ⟨1089323471088384012999203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11619450358276096138658165 1089323471088384012999203)
              ·
                refine ⟨1633985206632576019498805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089323471088384012999203 1633985206632576019498805)
                ·
                  refine ⟨153186113121804001828013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1633985206632576019498805 153186113121804001828013)
                  ·
                    rfl

theorem cell21_671240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_671240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671240 prefixEnd_671240 := by exact prefixLift 671240
  have htrace : WordTrace (prefixWord ++ tailWord_671240) baseStart_671240 baseEnd_671240 := by
    simpa [prefixWord, tailWord_671240, baseEnd_671240] using wordTrace_append hprefix tailTrace_671240
  have hstable : (prefixWord ++ tailWord_671240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671240).length < 2 ^ (prefixWord ++ tailWord_671240).sum := by decide
  have hdescent : baseEnd_671240 < baseStart_671240 := by decide
  rcases family_descends (prefixWord ++ tailWord_671240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671246 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_671246 : Nat := 118140960795 + 671246 * 2 ^ 59
def prefixEnd_671246 : Nat := 4983230072969 + 3 ^ 40 * 671246 * 2
def baseEnd_671246 : Nat := 153187482403549324728001

theorem tailTrace_671246 : CollatzResearch.WordTrace tailWord_671246 prefixEnd_671246 153187482403549324728001 := by
  unfold tailWord_671246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060294115774732066872199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16321568617465237689985061 3060294115774732066872199)
  ·
    refine ⟨4590441173662098100308299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060294115774732066872199 4590441173662098100308299)
    ·
      refine ⟨6885661760493147150462449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590441173662098100308299 6885661760493147150462449)
      ·
        refine ⟨5164246320369860362846837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6885661760493147150462449 5164246320369860362846837)
        ·
          refine ⟨484148092534674409016891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5164246320369860362846837 484148092534674409016891)
          ·
            refine ⟨726222138802011613525337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484148092534674409016891 726222138802011613525337)
            ·
              refine ⟨544666604101508710144003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726222138802011613525337 544666604101508710144003)
              ·
                refine ⟨816999906152263065216005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544666604101508710144003 816999906152263065216005)
                ·
                  refine ⟨153187482403549324728001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816999906152263065216005 153187482403549324728001)
                  ·
                    rfl

theorem cell21_671246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_671246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671246 prefixEnd_671246 := by exact prefixLift 671246
  have htrace : WordTrace (prefixWord ++ tailWord_671246) baseStart_671246 baseEnd_671246 := by
    simpa [prefixWord, tailWord_671246, baseEnd_671246] using wordTrace_append hprefix tailTrace_671246
  have hstable : (prefixWord ++ tailWord_671246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671246).length < 2 ^ (prefixWord ++ tailWord_671246).sum := by decide
  have hdescent : baseEnd_671246 < baseStart_671246 := by decide
  rcases family_descends (prefixWord ++ tailWord_671246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671316 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_671316 : Nat := 118140960795 + 671316 * 2 ^ 59
def prefixEnd_671316 : Nat := 4983230072969 + 3 ^ 40 * 671316 * 2
def baseEnd_671316 : Nat := 153203457357244758561191

theorem tailTrace_671316 : CollatzResearch.WordTrace tailWord_671316 prefixEnd_671316 153203457357244758561191 := by
  unfold tailWord_671316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242453017972129245012901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16323270690629505660017201 12242453017972129245012901)
  ·
    refine ⟨2295459940869774233439919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12242453017972129245012901 2295459940869774233439919)
    ·
      refine ⟨3443189911304661350159879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295459940869774233439919 3443189911304661350159879)
      ·
        refine ⟨5164784866956992025239819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443189911304661350159879 5164784866956992025239819)
        ·
          refine ⟨7747177300435488037859729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164784866956992025239819 7747177300435488037859729)
          ·
            refine ⟨5810382975326616028394797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7747177300435488037859729 5810382975326616028394797)
            ·
              refine ⟨2178893615747481010648049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5810382975326616028394797 2178893615747481010648049)
              ·
                refine ⟨1634170211810610757986037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178893615747481010648049 1634170211810610757986037)
                ·
                  refine ⟨153203457357244758561191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1634170211810610757986037 153203457357244758561191)
                  ·
                    rfl

theorem cell21_671316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_671316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671316 prefixEnd_671316 := by exact prefixLift 671316
  have htrace : WordTrace (prefixWord ++ tailWord_671316) baseStart_671316 baseEnd_671316 := by
    simpa [prefixWord, tailWord_671316, baseEnd_671316] using wordTrace_append hprefix tailTrace_671316
  have hstable : (prefixWord ++ tailWord_671316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671316).length < 2 ^ (prefixWord ++ tailWord_671316).sum := by decide
  have hdescent : baseEnd_671316 < baseStart_671316 := by decide
  rcases family_descends (prefixWord ++ tailWord_671316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671333 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 3]
def baseStart_671333 : Nat := 118140960795 + 671333 * 2 ^ 59
def prefixEnd_671333 : Nat := 4983230072969 + 3 ^ 40 * 671333 * 2
def baseEnd_671333 : Nat := 153207336988856506777823

theorem tailTrace_671333 : CollatzResearch.WordTrace tailWord_671333 prefixEnd_671333 153207336988856506777823 := by
  unfold tailWord_671333
  simp only [CollatzResearch.WordTrace]
  refine ⟨24485526076882670393394653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16323684051255113595596435 24485526076882670393394653)
  ·
    refine ⟨9182072278831001397522995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24485526076882670393394653 9182072278831001397522995)
    ·
      refine ⟨13773108418246502096284493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9182072278831001397522995 13773108418246502096284493)
      ·
        refine ⟨5164915656842438286106685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13773108418246502096284493 5164915656842438286106685)
        ·
          refine ⟨1936843371315914357290007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5164915656842438286106685 1936843371315914357290007)
          ·
            refine ⟨2905265056973871535935011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936843371315914357290007 2905265056973871535935011)
            ·
              refine ⟨4357897585460807303902517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905265056973871535935011 4357897585460807303902517)
              ·
                refine ⟨408552898636950684740861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4357897585460807303902517 408552898636950684740861)
                ·
                  refine ⟨153207336988856506777823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408552898636950684740861 153207336988856506777823)
                  ·
                    rfl

theorem cell21_671333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_671333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671333 prefixEnd_671333 := by exact prefixLift 671333
  have htrace : WordTrace (prefixWord ++ tailWord_671333) baseStart_671333 baseEnd_671333 := by
    simpa [prefixWord, tailWord_671333, baseEnd_671333] using wordTrace_append hprefix tailTrace_671333
  have hstable : (prefixWord ++ tailWord_671333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671333).length < 2 ^ (prefixWord ++ tailWord_671333).sum := by decide
  have hdescent : baseEnd_671333 < baseStart_671333 := by decide
  rcases family_descends (prefixWord ++ tailWord_671333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671350 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_671350 : Nat := 118140960795 + 671350 * 2 ^ 59
def prefixEnd_671350 : Nat := 4983230072969 + 3 ^ 40 * 671350 * 2
def baseEnd_671350 : Nat := 153211216620468254994455

theorem tailTrace_671350 : CollatzResearch.WordTrace tailWord_671350 prefixEnd_671350 153211216620468254994455 := by
  unfold tailWord_671350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530384132363817643547719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16324097411880721531175669 1530384132363817643547719)
  ·
    refine ⟨2295576198545726465321579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530384132363817643547719 2295576198545726465321579)
    ·
      refine ⟨3443364297818589697982369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295576198545726465321579 3443364297818589697982369)
      ·
        refine ⟨2582523223363942273486777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3443364297818589697982369 2582523223363942273486777)
        ·
          refine ⟨1936892417522956705115083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2582523223363942273486777 1936892417522956705115083)
          ·
            refine ⟨2905338626284435057672625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936892417522956705115083 2905338626284435057672625)
            ·
              refine ⟨2179003969713326293254469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905338626284435057672625 2179003969713326293254469)
              ·
                refine ⟨408563244321248679985213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2179003969713326293254469 408563244321248679985213)
                ·
                  refine ⟨153211216620468254994455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408563244321248679985213 153211216620468254994455)
                  ·
                    rfl

theorem cell21_671350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_671350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671350 prefixEnd_671350 := by exact prefixLift 671350
  have htrace : WordTrace (prefixWord ++ tailWord_671350) baseStart_671350 baseEnd_671350 := by
    simpa [prefixWord, tailWord_671350, baseEnd_671350] using wordTrace_append hprefix tailTrace_671350
  have hstable : (prefixWord ++ tailWord_671350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671350).length < 2 ^ (prefixWord ++ tailWord_671350).sum := by decide
  have hdescent : baseEnd_671350 < baseStart_671350 := by decide
  rcases family_descends (prefixWord ++ tailWord_671350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671378 : List Nat := [3, 2, 3, 1, 3, 1, 1, 7]
def baseStart_671378 : Nat := 118140960795 + 671378 * 2 ^ 59
def prefixEnd_671378 : Nat := 4983230072969 + 3 ^ 40 * 671378 * 2
def baseEnd_671378 : Nat := 51072535533982142842577

theorem tailTrace_671378 : CollatzResearch.WordTrace tailWord_671378 prefixEnd_671378 51072535533982142842577 := by
  unfold tailWord_671378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121791840429910769695697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16324778241146428719188525 6121791840429910769695697)
  ·
    refine ⟨4591343880322433077271773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6121791840429910769695697 4591343880322433077271773)
    ·
      refine ⟨1721753955120912403976915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4591343880322433077271773 1721753955120912403976915)
      ·
        refine ⟨2582630932681368605965373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721753955120912403976915 2582630932681368605965373)
        ·
          refine ⟨968486599755513227237015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2582630932681368605965373 968486599755513227237015)
          ·
            refine ⟨1452729899633269840855523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968486599755513227237015 1452729899633269840855523)
            ·
              refine ⟨2179094849449904761283285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452729899633269840855523 2179094849449904761283285)
              ·
                refine ⟨51072535533982142842577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2179094849449904761283285 51072535533982142842577)
                ·
                  rfl

theorem cell21_671378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_671378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671378 prefixEnd_671378 := by exact prefixLift 671378
  have htrace : WordTrace (prefixWord ++ tailWord_671378) baseStart_671378 baseEnd_671378 := by
    simpa [prefixWord, tailWord_671378, baseEnd_671378] using wordTrace_append hprefix tailTrace_671378
  have hstable : (prefixWord ++ tailWord_671378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671378).length < 2 ^ (prefixWord ++ tailWord_671378).sum := by decide
  have hdescent : baseEnd_671378 < baseStart_671378 := by decide
  rcases family_descends (prefixWord ++ tailWord_671378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671494 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_671494 : Nat := 118140960795 + 671494 * 2 ^ 59
def prefixEnd_671494 : Nat := 4983230072969 + 3 ^ 40 * 671494 * 2
def baseEnd_671494 : Nat := 153244079382356004594161

theorem tailTrace_671494 : CollatzResearch.WordTrace tailWord_671494 prefixEnd_671494 153244079382356004594161 := by
  unfold tailWord_671494
  simp only [CollatzResearch.WordTrace]
  refine ⟨765356194665606090312673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16327598819532929926670357 765356194665606090312673)
  ·
    refine ⟨574017145999204567734505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 765356194665606090312673 574017145999204567734505)
    ·
      refine ⟨430512859499403425800879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574017145999204567734505 430512859499403425800879)
      ·
        refine ⟨645769289249105138701319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430512859499403425800879 645769289249105138701319)
        ·
          refine ⟨968653933873657708051979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645769289249105138701319 968653933873657708051979)
          ·
            refine ⟨1452980900810486562077969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968653933873657708051979 1452980900810486562077969)
            ·
              refine ⟨1089735675607864921558477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452980900810486562077969 1089735675607864921558477)
              ·
                refine ⟨408650878352949345584429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089735675607864921558477 408650878352949345584429)
                ·
                  refine ⟨153244079382356004594161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408650878352949345584429 153244079382356004594161)
                  ·
                    rfl

theorem cell21_671494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_671494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671494 prefixEnd_671494 := by exact prefixLift 671494
  have htrace : WordTrace (prefixWord ++ tailWord_671494) baseStart_671494 baseEnd_671494 := by
    simpa [prefixWord, tailWord_671494, baseEnd_671494] using wordTrace_append hprefix tailTrace_671494
  have hstable : (prefixWord ++ tailWord_671494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671494).length < 2 ^ (prefixWord ++ tailWord_671494).sum := by decide
  have hdescent : baseEnd_671494 < baseStart_671494 := by decide
  rcases family_descends (prefixWord ++ tailWord_671494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671696 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_671696 : Nat := 118140960795 + 671696 * 2 ^ 59
def prefixEnd_671696 : Nat := 4983230072969 + 3 ^ 40 * 671696 * 2
def baseEnd_671696 : Nat := 153290178534448542227081

theorem tailTrace_671696 : CollatzResearch.WordTrace tailWord_671696 prefixEnd_671696 153290178534448542227081 := by
  unfold tailWord_671696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12249382887283791694429471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16332510516378388925905961 12249382887283791694429471)
  ·
    refine ⟨18374074330925687541644207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12249382887283791694429471 18374074330925687541644207)
    ·
      refine ⟨27561111496388531312466311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18374074330925687541644207 27561111496388531312466311)
      ·
        refine ⟨41341667244582796968699467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27561111496388531312466311 41341667244582796968699467)
        ·
          refine ⟨62012500866874195453049201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41341667244582796968699467 62012500866874195453049201)
          ·
            refine ⟨46509375650155646589786901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62012500866874195453049201 46509375650155646589786901)
            ·
              refine ⟨2180126983601045933896261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46509375650155646589786901 2180126983601045933896261)
              ·
                refine ⟨408773809425196112605549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2180126983601045933896261 408773809425196112605549)
                ·
                  refine ⟨153290178534448542227081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408773809425196112605549 153290178534448542227081)
                  ·
                    rfl

theorem cell21_671696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_671696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671696 prefixEnd_671696 := by exact prefixLift 671696
  have htrace : WordTrace (prefixWord ++ tailWord_671696) baseStart_671696 baseEnd_671696 := by
    simpa [prefixWord, tailWord_671696, baseEnd_671696] using wordTrace_append hprefix tailTrace_671696
  have hstable : (prefixWord ++ tailWord_671696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671696).length < 2 ^ (prefixWord ++ tailWord_671696).sum := by decide
  have hdescent : baseEnd_671696 < baseStart_671696 := by decide
  rcases family_descends (prefixWord ++ tailWord_671696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671800 : List Nat := [2, 1, 2, 1, 6, 9]
def baseStart_671800 : Nat := 118140960795 + 671800 * 2 ^ 59
def prefixEnd_671800 : Nat := 4983230072969 + 3 ^ 40 * 671800 * 2
def baseEnd_671800 : Nat := 5678293064865461944205

theorem tailTrace_671800 : CollatzResearch.WordTrace tailWord_671800 prefixEnd_671800 5678293064865461944205 := by
  unfold tailWord_671800
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251279483095404575322427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16335039310793872767096569 12251279483095404575322427)
  ·
    refine ⟨18376919224643106862983641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12251279483095404575322427 18376919224643106862983641)
    ·
      refine ⟨13782689418482330147237731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18376919224643106862983641 13782689418482330147237731)
      ·
        refine ⟨20674034127723495220856597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13782689418482330147237731 20674034127723495220856597)
        ·
          refine ⟨969095349737038838477653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20674034127723495220856597 969095349737038838477653)
          ·
            refine ⟨5678293064865461944205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 969095349737038838477653 5678293064865461944205)
            ·
              rfl

theorem cell21_671800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 9].length) (baseStart_671800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671800 prefixEnd_671800 := by exact prefixLift 671800
  have htrace : WordTrace (prefixWord ++ tailWord_671800) baseStart_671800 baseEnd_671800 := by
    simpa [prefixWord, tailWord_671800, baseEnd_671800] using wordTrace_append hprefix tailTrace_671800
  have hstable : (prefixWord ++ tailWord_671800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671800).length < 2 ^ (prefixWord ++ tailWord_671800).sum := by decide
  have hdescent : baseEnd_671800 < baseStart_671800 := by decide
  rcases family_descends (prefixWord ++ tailWord_671800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671806 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_671806 : Nat := 118140960795 + 671806 * 2 ^ 59
def prefixEnd_671806 : Nat := 4983230072969 + 3 ^ 40 * 671806 * 2
def baseEnd_671806 : Nat := 153315282033112795393523

theorem tailTrace_671806 : CollatzResearch.WordTrace tailWord_671806 prefixEnd_671806 153315282033112795393523 := by
  unfold tailWord_671806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062847225521134021920409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16335185202779381450242181 3062847225521134021920409)
  ·
    refine ⟨2297135419140850516440307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3062847225521134021920409 2297135419140850516440307)
    ·
      refine ⟨3445703128711275774660461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297135419140850516440307 3445703128711275774660461)
      ·
        refine ⟨1292138673266728415497673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3445703128711275774660461 1292138673266728415497673)
        ·
          refine ⟨969104004950046311623255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1292138673266728415497673 969104004950046311623255)
          ·
            refine ⟨1453656007425069467434883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969104004950046311623255 1453656007425069467434883)
            ·
              refine ⟨2180484011137604201152325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453656007425069467434883 2180484011137604201152325)
              ·
                refine ⟨408840752088300787716061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2180484011137604201152325 408840752088300787716061)
                ·
                  refine ⟨153315282033112795393523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408840752088300787716061 153315282033112795393523)
                  ·
                    rfl

theorem cell21_671806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_671806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671806 prefixEnd_671806 := by exact prefixLift 671806
  have htrace : WordTrace (prefixWord ++ tailWord_671806) baseStart_671806 baseEnd_671806 := by
    simpa [prefixWord, tailWord_671806, baseEnd_671806] using wordTrace_append hprefix tailTrace_671806
  have hstable : (prefixWord ++ tailWord_671806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671806).length < 2 ^ (prefixWord ++ tailWord_671806).sum := by decide
  have hdescent : baseEnd_671806 < baseStart_671806 := by decide
  rcases family_descends (prefixWord ++ tailWord_671806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671876 : List Nat := [2, 3, 2, 1, 2, 1, 2, 8]
def baseStart_671876 : Nat := 118140960795 + 671876 * 2 ^ 59
def prefixEnd_671876 : Nat := 4983230072969 + 3 ^ 40 * 671876 * 2
def baseEnd_671876 : Nat := 51110418995602743075571

theorem tailTrace_671876 : CollatzResearch.WordTrace tailWord_671876 prefixEnd_671876 51110418995602743075571 := by
  unfold tailWord_671876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12252665456957737065205741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16336887275943649420274321 12252665456957737065205741)
  ·
    refine ⟨4594749546359151399452153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12252665456957737065205741 4594749546359151399452153)
    ·
      refine ⟨3446062159769363549589115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4594749546359151399452153 3446062159769363549589115)
      ·
        refine ⟨5169093239654045324383673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446062159769363549589115 5169093239654045324383673)
        ·
          refine ⟨3876819929740533993287755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5169093239654045324383673 3876819929740533993287755)
          ·
            refine ⟨5815229894610800989931633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876819929740533993287755 5815229894610800989931633)
            ·
              refine ⟨4361422420958100742448725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5815229894610800989931633 4361422420958100742448725)
              ·
                refine ⟨51110418995602743075571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4361422420958100742448725 51110418995602743075571)
                ·
                  rfl

theorem cell21_671876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_671876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_671876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_671876 prefixEnd_671876 := by exact prefixLift 671876
  have htrace : WordTrace (prefixWord ++ tailWord_671876) baseStart_671876 baseEnd_671876 := by
    simpa [prefixWord, tailWord_671876, baseEnd_671876] using wordTrace_append hprefix tailTrace_671876
  have hstable : (prefixWord ++ tailWord_671876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671876).length < 2 ^ (prefixWord ++ tailWord_671876).sum := by decide
  have hdescent : baseEnd_671876 < baseStart_671876 := by decide
  rcases family_descends (prefixWord ++ tailWord_671876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672031 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 4]
def baseStart_672031 : Nat := 118140960795 + 672031 * 2 ^ 59
def prefixEnd_672031 : Nat := 4983230072969 + 3 ^ 40 * 672031 * 2
def baseEnd_672031 : Nat := 153366630098562404143063

theorem tailTrace_672031 : CollatzResearch.WordTrace tailWord_672031 prefixEnd_672031 153366630098562404143063 := by
  unfold tailWord_672031
  simp only [CollatzResearch.WordTrace]
  refine ⟨24510984228353935602303947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16340656152235957068202631 24510984228353935602303947)
  ·
    refine ⟨36766476342530903403455921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24510984228353935602303947 36766476342530903403455921)
    ·
      refine ⟨27574857256898177552591941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36766476342530903403455921 27574857256898177552591941)
      ·
        refine ⟨5170285735668408291110989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27574857256898177552591941 5170285735668408291110989)
        ·
          refine ⟨1938857150875653109166621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5170285735668408291110989 1938857150875653109166621)
          ·
            refine ⟨727071431578369915937483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1938857150875653109166621 727071431578369915937483)
            ·
              refine ⟨1090607147367554873906225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727071431578369915937483 1090607147367554873906225)
              ·
                refine ⟨817955360525666155429669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1090607147367554873906225 817955360525666155429669)
                ·
                  refine ⟨153366630098562404143063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817955360525666155429669 153366630098562404143063)
                  ·
                    rfl

theorem cell21_672031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].length) (baseStart_672031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672031 prefixEnd_672031 := by exact prefixLift 672031
  have htrace : WordTrace (prefixWord ++ tailWord_672031) baseStart_672031 baseEnd_672031 := by
    simpa [prefixWord, tailWord_672031, baseEnd_672031] using wordTrace_append hprefix tailTrace_672031
  have hstable : (prefixWord ++ tailWord_672031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672031).length < 2 ^ (prefixWord ++ tailWord_672031).sum := by decide
  have hdescent : baseEnd_672031 < baseStart_672031 := by decide
  rcases family_descends (prefixWord ++ tailWord_672031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672062 : List Nat := [4, 2, 1, 2, 1, 4, 2, 5]
def baseStart_672062 : Nat := 118140960795 + 672062 * 2 ^ 59
def prefixEnd_672062 : Nat := 4983230072969 + 3 ^ 40 * 672062 * 2
def baseEnd_672062 : Nat := 51124568240304413042111

theorem tailTrace_672062 : CollatzResearch.WordTrace tailWord_672062 prefixEnd_672062 51124568240304413042111 := by
  unfold tailWord_672062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064014361405203487085305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16341409927494418597788293 3064014361405203487085305)
  ·
    refine ⟨2298010771053902615313979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3064014361405203487085305 2298010771053902615313979)
    ·
      refine ⟨3447016156580853922970969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2298010771053902615313979 3447016156580853922970969)
      ·
        refine ⟨2585262117435640442228227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3447016156580853922970969 2585262117435640442228227)
        ·
          refine ⟨3877893176153460663342341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585262117435640442228227 3877893176153460663342341)
          ·
            refine ⟨727104970528773874376689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3877893176153460663342341 727104970528773874376689)
            ·
              refine ⟨545328727896580405782517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727104970528773874376689 545328727896580405782517)
              ·
                refine ⟨51124568240304413042111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 545328727896580405782517 51124568240304413042111)
                ·
                  rfl

theorem cell21_672062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_672062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672062 prefixEnd_672062 := by exact prefixLift 672062
  have htrace : WordTrace (prefixWord ++ tailWord_672062) baseStart_672062 baseEnd_672062 := by
    simpa [prefixWord, tailWord_672062, baseEnd_672062] using wordTrace_append hprefix tailTrace_672062
  have hstable : (prefixWord ++ tailWord_672062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672062).length < 2 ^ (prefixWord ++ tailWord_672062).sum := by decide
  have hdescent : baseEnd_672062 < baseStart_672062 := by decide
  rcases family_descends (prefixWord ++ tailWord_672062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672104 : List Nat := [2, 1, 4, 2, 2, 1, 1, 8]
def baseStart_672104 : Nat := 118140960795 + 672104 * 2 ^ 59
def prefixEnd_672104 : Nat := 4983230072969 + 3 ^ 40 * 672104 * 2
def baseEnd_672104 : Nat := 51127763231043499808749

theorem tailTrace_672104 : CollatzResearch.WordTrace tailWord_672104 prefixEnd_672104 51127763231043499808749 := by
  unfold tailWord_672104
  simp only [CollatzResearch.WordTrace]
  refine ⟨12256823378544734534855683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16342431171392979379807577 12256823378544734534855683)
  ·
    refine ⟨18385235067817101802283525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12256823378544734534855683 18385235067817101802283525)
    ·
      refine ⟨3447231575215706587928161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18385235067817101802283525 3447231575215706587928161)
      ·
        refine ⟨2585423681411779940946121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3447231575215706587928161 2585423681411779940946121)
        ·
          refine ⟨1939067761058834955709591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2585423681411779940946121 1939067761058834955709591)
          ·
            refine ⟨2908601641588252433564387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939067761058834955709591 2908601641588252433564387)
            ·
              refine ⟨4362902462382378650346581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908601641588252433564387 4362902462382378650346581)
              ·
                refine ⟨51127763231043499808749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4362902462382378650346581 51127763231043499808749)
                ·
                  rfl

theorem cell21_672104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_672104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672104 prefixEnd_672104 := by exact prefixLift 672104
  have htrace : WordTrace (prefixWord ++ tailWord_672104) baseStart_672104 baseEnd_672104 := by
    simpa [prefixWord, tailWord_672104, baseEnd_672104] using wordTrace_append hprefix tailTrace_672104
  have hstable : (prefixWord ++ tailWord_672104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672104).length < 2 ^ (prefixWord ++ tailWord_672104).sum := by decide
  have hdescent : baseEnd_672104 < baseStart_672104 := by decide
  rcases family_descends (prefixWord ++ tailWord_672104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672262 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_672262 : Nat := 118140960795 + 672262 * 2 ^ 59
def prefixEnd_672262 : Nat := 4983230072969 + 3 ^ 40 * 672262 * 2
def baseEnd_672262 : Nat := 153419347445757335792591

theorem tailTrace_672262 : CollatzResearch.WordTrace tailWord_672262 prefixEnd_672262 153419347445757335792591 := by
  unfold tailWord_672262
  simp only [CollatzResearch.WordTrace]
  refine ⟨766231546578658189186345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16346272993678041369308693 766231546578658189186345)
  ·
    refine ⟨574673659933993641889759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 766231546578658189186345 574673659933993641889759)
    ·
      refine ⟨862010489900990462834639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574673659933993641889759 862010489900990462834639)
      ·
        refine ⟨1293015734851485694251959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862010489900990462834639 1293015734851485694251959)
        ·
          refine ⟨1939523602277228541377939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293015734851485694251959 1939523602277228541377939)
          ·
            refine ⟨2909285403415842812066909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939523602277228541377939 2909285403415842812066909)
            ·
              refine ⟨1090982026280941054525091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2909285403415842812066909 1090982026280941054525091)
              ·
                refine ⟨1636473039421411581787637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090982026280941054525091 1636473039421411581787637)
                ·
                  refine ⟨153419347445757335792591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1636473039421411581787637 153419347445757335792591)
                  ·
                    rfl

theorem cell21_672262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_672262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672262 prefixEnd_672262 := by exact prefixLift 672262
  have htrace : WordTrace (prefixWord ++ tailWord_672262) baseStart_672262 baseEnd_672262 := by
    simpa [prefixWord, tailWord_672262, baseEnd_672262] using wordTrace_append hprefix tailTrace_672262
  have hstable : (prefixWord ++ tailWord_672262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672262).length < 2 ^ (prefixWord ++ tailWord_672262).sum := by decide
  have hdescent : baseEnd_672262 < baseStart_672262 := by decide
  rcases family_descends (prefixWord ++ tailWord_672262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672276 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_672276 : Nat := 118140960795 + 672276 * 2 ^ 59
def prefixEnd_672276 : Nat := 4983230072969 + 3 ^ 40 * 672276 * 2
def baseEnd_672276 : Nat := 153422542436496422559229

theorem tailTrace_672276 : CollatzResearch.WordTrace tailWord_672276 prefixEnd_672276 153422542436496422559229 := by
  unfold tailWord_672276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259960056233171222486341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16346613408310894963315121 12259960056233171222486341)
  ·
    refine ⟨2298742510543719604216189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12259960056233171222486341 2298742510543719604216189)
    ·
      refine ⟨862028441453894851581071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2298742510543719604216189 862028441453894851581071)
      ·
        refine ⟨1293042662180842277371607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862028441453894851581071 1293042662180842277371607)
        ·
          refine ⟨1939563993271263416057411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293042662180842277371607 1939563993271263416057411)
          ·
            refine ⟨2909345989906895124086117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939563993271263416057411 2909345989906895124086117)
            ·
              refine ⟨545502373107542835766147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2909345989906895124086117 545502373107542835766147)
              ·
                refine ⟨818253559661314253649221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545502373107542835766147 818253559661314253649221)
                ·
                  refine ⟨153422542436496422559229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818253559661314253649221 153422542436496422559229)
                  ·
                    rfl

theorem cell21_672276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_672276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672276 prefixEnd_672276 := by exact prefixLift 672276
  have htrace : WordTrace (prefixWord ++ tailWord_672276) baseStart_672276 baseEnd_672276 := by
    simpa [prefixWord, tailWord_672276, baseEnd_672276] using wordTrace_append hprefix tailTrace_672276
  have hstable : (prefixWord ++ tailWord_672276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672276).length < 2 ^ (prefixWord ++ tailWord_672276).sum := by decide
  have hdescent : baseEnd_672276 < baseStart_672276 := by decide
  rcases family_descends (prefixWord ++ tailWord_672276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672321 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 3]
def baseStart_672321 : Nat := 118140960795 + 672321 * 2 ^ 59
def prefixEnd_672321 : Nat := 4983230072969 + 3 ^ 40 * 672321 * 2
def baseEnd_672321 : Nat := 153432812049586344309137

theorem tailTrace_672321 : CollatzResearch.WordTrace tailWord_672321 prefixEnd_672321 153432812049586344309137 := by
  unfold tailWord_672321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521561397303315130360817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16347707598202210086907211 24521561397303315130360817)
  ·
    refine ⟨18391171047977486347770613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24521561397303315130360817 18391171047977486347770613)
    ·
      refine ⟨1724172285747889345103495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18391171047977486347770613 1724172285747889345103495)
      ·
        refine ⟨2586258428621834017655243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724172285747889345103495 2586258428621834017655243)
        ·
          refine ⟨3879387642932751026482865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586258428621834017655243 3879387642932751026482865)
          ·
            refine ⟨2909540732199563269862149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879387642932751026482865 2909540732199563269862149)
            ·
              refine ⟨545538887287418113099153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2909540732199563269862149 545538887287418113099153)
              ·
                refine ⟨409154165465563584824365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545538887287418113099153 409154165465563584824365)
                ·
                  refine ⟨153432812049586344309137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409154165465563584824365 153432812049586344309137)
                  ·
                    rfl

theorem cell21_672321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_672321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672321 prefixEnd_672321 := by exact prefixLift 672321
  have htrace : WordTrace (prefixWord ++ tailWord_672321) baseStart_672321 baseEnd_672321 := by
    simpa [prefixWord, tailWord_672321, baseEnd_672321] using wordTrace_append hprefix tailTrace_672321
  have hstable : (prefixWord ++ tailWord_672321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672321).length < 2 ^ (prefixWord ++ tailWord_672321).sum := by decide
  have hdescent : baseEnd_672321 < baseStart_672321 := by decide
  rcases family_descends (prefixWord ++ tailWord_672321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672324 : List Nat := [2, 3, 5, 1, 2, 1, 1, 6]
def baseStart_672324 : Nat := 118140960795 + 672324 * 2 ^ 59
def prefixEnd_672324 : Nat := 4983230072969 + 3 ^ 40 * 672324 * 2
def baseEnd_672324 : Nat := 51144498896819668586377

theorem tailTrace_672324 : CollatzResearch.WordTrace tailWord_672324 prefixEnd_672324 51144498896819668586377 := by
  unfold tailWord_672324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260835408146223321360013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16347780544194964428480017 12260835408146223321360013)
  ·
    refine ⟨4597813278054833745510005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12260835408146223321360013 4597813278054833745510005)
    ·
      refine ⟨431044994817640663641563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4597813278054833745510005 431044994817640663641563)
      ·
        refine ⟨646567492226460995462345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431044994817640663641563 646567492226460995462345)
        ·
          refine ⟨484925619169845746596759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646567492226460995462345 484925619169845746596759)
          ·
            refine ⟨727388428754768619895139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484925619169845746596759 727388428754768619895139)
            ·
              refine ⟨1091082643132152929842709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727388428754768619895139 1091082643132152929842709)
              ·
                refine ⟨51144498896819668586377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1091082643132152929842709 51144498896819668586377)
                ·
                  rfl

theorem cell21_672324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_672324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672324 prefixEnd_672324 := by exact prefixLift 672324
  have htrace : WordTrace (prefixWord ++ tailWord_672324) baseStart_672324 baseEnd_672324 := by
    simpa [prefixWord, tailWord_672324, baseEnd_672324] using wordTrace_append hprefix tailTrace_672324
  have hstable : (prefixWord ++ tailWord_672324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672324).length < 2 ^ (prefixWord ++ tailWord_672324).sum := by decide
  have hdescent : baseEnd_672324 < baseStart_672324 := by decide
  rcases family_descends (prefixWord ++ tailWord_672324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672377 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 6]
def baseStart_672377 : Nat := 118140960795 + 672377 * 2 ^ 59
def prefixEnd_672377 : Nat := 4983230072969 + 3 ^ 40 * 672377 * 2
def baseEnd_672377 : Nat := 153445592012542691375689

theorem tailTrace_672377 : CollatzResearch.WordTrace tailWord_672377 prefixEnd_672377 153445592012542691375689 := by
  unfold tailWord_672377
  simp only [CollatzResearch.WordTrace]
  refine ⟨24523603885100436694399385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16349069256733624462932923 24523603885100436694399385)
  ·
    refine ⟨18392702913825327520799539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24523603885100436694399385 18392702913825327520799539)
    ·
      refine ⟨27589054370737991281199309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18392702913825327520799539 27589054370737991281199309)
      ·
        refine ⟨10345895389026746730449741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27589054370737991281199309 10345895389026746730449741)
        ·
          refine ⟨3879710770885030023918653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10345895389026746730449741 3879710770885030023918653)
          ·
            refine ⟨1454891539081886258969495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3879710770885030023918653 1454891539081886258969495)
            ·
              refine ⟨2182337308622829388454243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454891539081886258969495 2182337308622829388454243)
              ·
                refine ⟨3273505962934244082681365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182337308622829388454243 3273505962934244082681365)
                ·
                  refine ⟨153445592012542691375689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3273505962934244082681365 153445592012542691375689)
                  ·
                    rfl

theorem cell21_672377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_672377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672377 prefixEnd_672377 := by exact prefixLift 672377
  have htrace : WordTrace (prefixWord ++ tailWord_672377) baseStart_672377 baseEnd_672377 := by
    simpa [prefixWord, tailWord_672377, baseEnd_672377] using wordTrace_append hprefix tailTrace_672377
  have hstable : (prefixWord ++ tailWord_672377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672377).length < 2 ^ (prefixWord ++ tailWord_672377).sum := by decide
  have hdescent : baseEnd_672377 < baseStart_672377 := by decide
  rcases family_descends (prefixWord ++ tailWord_672377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672386 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_672386 : Nat := 118140960795 + 672386 * 2 ^ 59
def prefixEnd_672386 : Nat := 4983230072969 + 3 ^ 40 * 672386 * 2
def baseEnd_672386 : Nat := 153447645935160675725671

theorem tailTrace_672386 : CollatzResearch.WordTrace tailWord_672386 prefixEnd_672386 153447645935160675725671 := by
  unfold tailWord_672386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130983035516957807869253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16349288094711887487651341 6130983035516957807869253)
  ·
    refine ⟨1149559319159429588975485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6130983035516957807869253 1149559319159429588975485)
    ·
      refine ⟨431084744684786095865807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1149559319159429588975485 431084744684786095865807)
      ·
        refine ⟨646627117027179143798711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431084744684786095865807 646627117027179143798711)
        ·
          refine ⟨969940675540768715698067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646627117027179143798711 969940675540768715698067)
          ·
            refine ⟨1454911013311153073547101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969940675540768715698067 1454911013311153073547101)
            ·
              refine ⟨545591629991682402580163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1454911013311153073547101 545591629991682402580163)
              ·
                refine ⟨818387444987523603870245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545591629991682402580163 818387444987523603870245)
                ·
                  refine ⟨153447645935160675725671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818387444987523603870245 153447645935160675725671)
                  ·
                    rfl

theorem cell21_672386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_672386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672386 prefixEnd_672386 := by exact prefixLift 672386
  have htrace : WordTrace (prefixWord ++ tailWord_672386) baseStart_672386 baseEnd_672386 := by
    simpa [prefixWord, tailWord_672386, baseEnd_672386] using wordTrace_append hprefix tailTrace_672386
  have hstable : (prefixWord ++ tailWord_672386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672386).length < 2 ^ (prefixWord ++ tailWord_672386).sum := by decide
  have hdescent : baseEnd_672386 < baseStart_672386 := by decide
  rcases family_descends (prefixWord ++ tailWord_672386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672391 : List Nat := [1, 1, 4, 2, 1, 2, 2, 8]
def baseStart_672391 : Nat := 118140960795 + 672391 * 2 ^ 59
def prefixEnd_672391 : Nat := 4983230072969 + 3 ^ 40 * 672391 * 2
def baseEnd_672391 : Nat := 51149595667760592714109

theorem tailTrace_672391 : CollatzResearch.WordTrace tailWord_672391 prefixEnd_672391 51149595667760592714109 := by
  unfold tailWord_672391
  simp only [CollatzResearch.WordTrace]
  refine ⟨24524114507049717085409027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16349409671366478056939351 24524114507049717085409027)
  ·
    refine ⟨36786171760574575628113541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24524114507049717085409027 36786171760574575628113541)
    ·
      refine ⟨6897407205107732930271289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36786171760574575628113541 6897407205107732930271289)
      ·
        refine ⟨5173055403830799697703467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6897407205107732930271289 5173055403830799697703467)
        ·
          refine ⟨7759583105746199546555201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5173055403830799697703467 7759583105746199546555201)
          ·
            refine ⟨5819687329309649659916401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7759583105746199546555201 5819687329309649659916401)
            ·
              refine ⟨4364765496982237244937301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5819687329309649659916401 4364765496982237244937301)
              ·
                refine ⟨51149595667760592714109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4364765496982237244937301 51149595667760592714109)
                ·
                  rfl

theorem cell21_672391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_672391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672391 prefixEnd_672391 := by exact prefixLift 672391
  have htrace : WordTrace (prefixWord ++ tailWord_672391) baseStart_672391 baseEnd_672391 := by
    simpa [prefixWord, tailWord_672391, baseEnd_672391] using wordTrace_append hprefix tailTrace_672391
  have hstable : (prefixWord ++ tailWord_672391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672391).length < 2 ^ (prefixWord ++ tailWord_672391).sum := by decide
  have hdescent : baseEnd_672391 < baseStart_672391 := by decide
  rcases family_descends (prefixWord ++ tailWord_672391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672543 : List Nat := [1, 1, 2, 4, 2, 3, 8]
def baseStart_672543 : Nat := 118140960795 + 672543 * 2 ^ 59
def prefixEnd_672543 : Nat := 4983230072969 + 3 ^ 40 * 672543 * 2
def baseEnd_672543 : Nat := 17053719497129254623187

theorem tailTrace_672543 : CollatzResearch.WordTrace tailWord_672543 prefixEnd_672543 17053719497129254623187 := by
  unfold tailWord_672543
  simp only [CollatzResearch.WordTrace]
  refine ⟨24529658402499047044942283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16353105601666031363294855 24529658402499047044942283)
  ·
    refine ⟨36794487603748570567413425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24529658402499047044942283 36794487603748570567413425)
    ·
      refine ⟨27595865702811427925560069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36794487603748570567413425 27595865702811427925560069)
      ·
        refine ⟨5174224819277142736042513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27595865702811427925560069 5174224819277142736042513)
        ·
          refine ⟨3880668614457857052031885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5174224819277142736042513 3880668614457857052031885)
          ·
            refine ⟨1455250730421696394511957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3880668614457857052031885 1455250730421696394511957)
            ·
              refine ⟨17053719497129254623187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1455250730421696394511957 17053719497129254623187)
              ·
                rfl

theorem cell21_672543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 8].length) (baseStart_672543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672543 prefixEnd_672543 := by exact prefixLift 672543
  have htrace : WordTrace (prefixWord ++ tailWord_672543) baseStart_672543 baseEnd_672543 := by
    simpa [prefixWord, tailWord_672543, baseEnd_672543] using wordTrace_append hprefix tailTrace_672543
  have hstable : (prefixWord ++ tailWord_672543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672543).length < 2 ^ (prefixWord ++ tailWord_672543).sum := by decide
  have hdescent : baseEnd_672543 < baseStart_672543 := by decide
  rcases family_descends (prefixWord ++ tailWord_672543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672546 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_672546 : Nat := 118140960795 + 672546 * 2 ^ 59
def prefixEnd_672546 : Nat := 4983230072969 + 3 ^ 40 * 672546 * 2
def baseEnd_672546 : Nat := 153484160115035953058677

theorem tailTrace_672546 : CollatzResearch.WordTrace tailWord_672546 prefixEnd_672546 153484160115035953058677 := by
  unfold tailWord_672546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132441955372044639325373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16353178547658785704867661 6132441955372044639325373)
  ·
    refine ⟨2299665733264516739747015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6132441955372044639325373 2299665733264516739747015)
    ·
      refine ⟨3449498599896775109620523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299665733264516739747015 3449498599896775109620523)
      ·
        refine ⟨5174247899845162664430785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449498599896775109620523 5174247899845162664430785)
        ·
          refine ⟨3880685924883871998323089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5174247899845162664430785 3880685924883871998323089)
          ·
            refine ⟨2910514443662903998742317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3880685924883871998323089 2910514443662903998742317)
            ·
              refine ⟨1091442916373588999528369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2910514443662903998742317 1091442916373588999528369)
              ·
                refine ⟨818582187280191749646277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091442916373588999528369 818582187280191749646277)
                ·
                  refine ⟨153484160115035953058677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818582187280191749646277 153484160115035953058677)
                  ·
                    rfl

theorem cell21_672546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_672546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672546 prefixEnd_672546 := by exact prefixLift 672546
  have htrace : WordTrace (prefixWord ++ tailWord_672546) baseStart_672546 baseEnd_672546 := by
    simpa [prefixWord, tailWord_672546, baseEnd_672546] using wordTrace_append hprefix tailTrace_672546
  have hstable : (prefixWord ++ tailWord_672546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672546).length < 2 ^ (prefixWord ++ tailWord_672546).sum := by decide
  have hdescent : baseEnd_672546 < baseStart_672546 := by decide
  rcases family_descends (prefixWord ++ tailWord_672546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672577 : List Nat := [1, 2, 5, 3, 1, 1, 1, 7]
def baseStart_672577 : Nat := 118140960795 + 672577 * 2 ^ 59
def prefixEnd_672577 : Nat := 4983230072969 + 3 ^ 40 * 672577 * 2
def baseEnd_672577 : Nat := 51163744912462262680649

theorem tailTrace_672577 : CollatzResearch.WordTrace tailWord_672577 prefixEnd_672577 51163744912462262680649 := by
  unfold tailWord_672577
  simp only [CollatzResearch.WordTrace]
  refine ⟨24530898484375870851679985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16353932322917247234453323 24530898484375870851679985)
  ·
    refine ⟨18398173863281903138759989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24530898484375870851679985 18398173863281903138759989)
    ·
      refine ⟨1724828799682678419258749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18398173863281903138759989 1724828799682678419258749)
      ·
        refine ⟨646810799881004407222031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1724828799682678419258749 646810799881004407222031)
        ·
          refine ⟨970216199821506610833047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646810799881004407222031 970216199821506610833047)
          ·
            refine ⟨1455324299732259916249571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970216199821506610833047 1455324299732259916249571)
            ·
              refine ⟨2182986449598389874374357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455324299732259916249571 2182986449598389874374357)
              ·
                refine ⟨51163744912462262680649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2182986449598389874374357 51163744912462262680649)
                ·
                  rfl

theorem cell21_672577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 7].length) (baseStart_672577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672577 prefixEnd_672577 := by exact prefixLift 672577
  have htrace : WordTrace (prefixWord ++ tailWord_672577) baseStart_672577 baseEnd_672577 := by
    simpa [prefixWord, tailWord_672577, baseEnd_672577] using wordTrace_append hprefix tailTrace_672577
  have hstable : (prefixWord ++ tailWord_672577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672577).length < 2 ^ (prefixWord ++ tailWord_672577).sum := by decide
  have hdescent : baseEnd_672577 < baseStart_672577 := by decide
  rcases family_descends (prefixWord ++ tailWord_672577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672608 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_672608 : Nat := 118140960795 + 672608 * 2 ^ 59
def prefixEnd_672608 : Nat := 4983230072969 + 3 ^ 40 * 672608 * 2
def baseEnd_672608 : Nat := 153498309359737623025217

theorem tailTrace_672608 : CollatzResearch.WordTrace tailWord_672608 prefixEnd_672608 153498309359737623025217 := by
  unfold tailWord_672608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12266014573631781573029239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16354686098175708764038985 12266014573631781573029239)
  ·
    refine ⟨18399021860447672359543859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12266014573631781573029239 18399021860447672359543859)
    ·
      refine ⟨27598532790671508539315789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18399021860447672359543859 27598532790671508539315789)
      ·
        refine ⟨10349449796501815702243421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27598532790671508539315789 10349449796501815702243421)
        ·
          refine ⟨3881043673688180888341283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10349449796501815702243421 3881043673688180888341283)
          ·
            refine ⟨5821565510532271332511925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881043673688180888341283 5821565510532271332511925)
            ·
              refine ⟨545771766612400437422993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5821565510532271332511925 545771766612400437422993)
              ·
                refine ⟨409328824959300328067245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545771766612400437422993 409328824959300328067245)
                ·
                  refine ⟨153498309359737623025217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409328824959300328067245 153498309359737623025217)
                  ·
                    rfl

theorem cell21_672608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_672608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672608 prefixEnd_672608 := by exact prefixLift 672608
  have htrace : WordTrace (prefixWord ++ tailWord_672608) baseStart_672608 baseEnd_672608 := by
    simpa [prefixWord, tailWord_672608, baseEnd_672608] using wordTrace_append hprefix tailTrace_672608
  have hstable : (prefixWord ++ tailWord_672608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672608).length < 2 ^ (prefixWord ++ tailWord_672608).sum := by decide
  have hdescent : baseEnd_672608 < baseStart_672608 := by decide
  rcases family_descends (prefixWord ++ tailWord_672608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672791 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 4]
def baseStart_672791 : Nat := 118140960795 + 672791 * 2 ^ 59
def prefixEnd_672791 : Nat := 4983230072969 + 3 ^ 40 * 672791 * 2
def baseEnd_672791 : Nat := 153540072452969971474843

theorem tailTrace_672791 : CollatzResearch.WordTrace tailWord_672791 prefixEnd_672791 153540072452969971474843 := by
  unfold tailWord_672791
  simp only [CollatzResearch.WordTrace]
  refine ⟨24538703705600585399970227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16359135803733723599980151 24538703705600585399970227)
  ·
    refine ⟨36808055558400878099955341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24538703705600585399970227 36808055558400878099955341)
    ·
      refine ⟨13803020834400329287483253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36808055558400878099955341 13803020834400329287483253)
      ·
        refine ⟨1294033203225030870701555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13803020834400329287483253 1294033203225030870701555)
        ·
          refine ⟨1941049804837546306052333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294033203225030870701555 1941049804837546306052333)
          ·
            refine ⟨727893676814079864769625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1941049804837546306052333 727893676814079864769625)
            ·
              refine ⟨545920257610559898577219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727893676814079864769625 545920257610559898577219)
              ·
                refine ⟨818880386415839847865829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545920257610559898577219 818880386415839847865829)
                ·
                  refine ⟨153540072452969971474843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818880386415839847865829 153540072452969971474843)
                  ·
                    rfl

theorem cell21_672791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 4].length) (baseStart_672791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672791 prefixEnd_672791 := by exact prefixLift 672791
  have htrace : WordTrace (prefixWord ++ tailWord_672791) baseStart_672791 baseEnd_672791 := by
    simpa [prefixWord, tailWord_672791, baseEnd_672791] using wordTrace_append hprefix tailTrace_672791
  have hstable : (prefixWord ++ tailWord_672791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672791).length < 2 ^ (prefixWord ++ tailWord_672791).sum := by decide
  have hdescent : baseEnd_672791 < baseStart_672791 := by decide
  rcases family_descends (prefixWord ++ tailWord_672791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672892 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_672892 : Nat := 118140960795 + 672892 * 2 ^ 59
def prefixEnd_672892 : Nat := 4983230072969 + 3 ^ 40 * 672892 * 2
def baseEnd_672892 : Nat := 153563122029016240291303

theorem tailTrace_672892 : CollatzResearch.WordTrace tailWord_672892 prefixEnd_672892 153563122029016240291303 := by
  unfold tailWord_672892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12271193739117339824698465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16361591652156453099597953 12271193739117339824698465)
  ·
    refine ⟨9203395304338004868523849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12271193739117339824698465 9203395304338004868523849)
    ·
      refine ⟨6902546478253503651392887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9203395304338004868523849 6902546478253503651392887)
      ·
        refine ⟨10353819717380255477089331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6902546478253503651392887 10353819717380255477089331)
        ·
          refine ⟨15530729576070383215633997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10353819717380255477089331 15530729576070383215633997)
          ·
            refine ⟨5824023591026393705862749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15530729576070383215633997 5824023591026393705862749)
            ·
              refine ⟨2184008846634897639698531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5824023591026393705862749 2184008846634897639698531)
              ·
                refine ⟨3276013269952346459547797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184008846634897639698531 3276013269952346459547797)
                ·
                  refine ⟨153563122029016240291303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3276013269952346459547797 153563122029016240291303)
                  ·
                    rfl

theorem cell21_672892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_672892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672892 prefixEnd_672892 := by exact prefixLift 672892
  have htrace : WordTrace (prefixWord ++ tailWord_672892) baseStart_672892 baseEnd_672892 := by
    simpa [prefixWord, tailWord_672892, baseEnd_672892] using wordTrace_append hprefix tailTrace_672892
  have hstable : (prefixWord ++ tailWord_672892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672892).length < 2 ^ (prefixWord ++ tailWord_672892).sum := by decide
  have hdescent : baseEnd_672892 < baseStart_672892 := by decide
  rcases family_descends (prefixWord ++ tailWord_672892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672999 : List Nat := [1, 1, 5, 3, 2, 9]
def baseStart_672999 : Nat := 118140960795 + 672999 * 2 ^ 59
def prefixEnd_672999 : Nat := 4983230072969 + 3 ^ 40 * 672999 * 2
def baseEnd_672999 : Nat := 5688427440252141926213

theorem tailTrace_672999 : CollatzResearch.WordTrace tailWord_672999 prefixEnd_672999 5688427440252141926213 := by
  unfold tailWord_672999
  simp only [CollatzResearch.WordTrace]
  refine ⟨24546290088847036923542051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16364193392564691282361367 24546290088847036923542051)
  ·
    refine ⟨36819435133270555385313077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24546290088847036923542051 36819435133270555385313077)
    ·
      refine ⟨3451822043744114567373101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36819435133270555385313077 3451822043744114567373101)
      ·
        refine ⟨1294433266404042962764913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3451822043744114567373101 1294433266404042962764913)
        ·
          refine ⟨970824949803032222073685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294433266404042962764913 970824949803032222073685)
          ·
            refine ⟨5688427440252141926213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 970824949803032222073685 5688427440252141926213)
            ·
              rfl

theorem cell21_672999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 9].length) (baseStart_672999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_672999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_672999 prefixEnd_672999 := by exact prefixLift 672999
  have htrace : WordTrace (prefixWord ++ tailWord_672999) baseStart_672999 baseEnd_672999 := by
    simpa [prefixWord, tailWord_672999, baseEnd_672999] using wordTrace_append hprefix tailTrace_672999
  have hstable : (prefixWord ++ tailWord_672999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672999).length < 2 ^ (prefixWord ++ tailWord_672999).sum := by decide
  have hdescent : baseEnd_672999 < baseStart_672999 := by decide
  rcases family_descends (prefixWord ++ tailWord_672999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673005 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 3]
def baseStart_673005 : Nat := 118140960795 + 673005 * 2 ^ 59
def prefixEnd_673005 : Nat := 4983230072969 + 3 ^ 40 * 673005 * 2
def baseEnd_673005 : Nat := 153588910168553154907739

theorem tailTrace_673005 : CollatzResearch.WordTrace tailWord_673005 prefixEnd_673005 153588910168553154907739 := by
  unfold tailWord_673005
  simp only [CollatzResearch.WordTrace]
  refine ⟨24546508926825299948260469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16364339284550199965506979 24546508926825299948260469)
  ·
    refine ⟨2301235211889871870149419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24546508926825299948260469 2301235211889871870149419)
    ·
      refine ⟨3451852817834807805224129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301235211889871870149419 3451852817834807805224129)
      ·
        refine ⟨2588889613376105853918097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3451852817834807805224129 2588889613376105853918097)
        ·
          refine ⟨1941667210032079390438573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588889613376105853918097 1941667210032079390438573)
          ·
            refine ⟨728125203762029771414465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1941667210032079390438573 728125203762029771414465)
            ·
              refine ⟨546093902821522328560849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728125203762029771414465 546093902821522328560849)
              ·
                refine ⟨409570427116141746420637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546093902821522328560849 409570427116141746420637)
                ·
                  refine ⟨153588910168553154907739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409570427116141746420637 153588910168553154907739)
                  ·
                    rfl

theorem cell21_673005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_673005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673005 prefixEnd_673005 := by exact prefixLift 673005
  have htrace : WordTrace (prefixWord ++ tailWord_673005) baseStart_673005 baseEnd_673005 := by
    simpa [prefixWord, tailWord_673005, baseEnd_673005] using wordTrace_append hprefix tailTrace_673005
  have hstable : (prefixWord ++ tailWord_673005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673005).length < 2 ^ (prefixWord ++ tailWord_673005).sum := by decide
  have hdescent : baseEnd_673005 < baseStart_673005 := by decide
  rcases family_descends (prefixWord ++ tailWord_673005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673047 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 3]
def baseStart_673047 : Nat := 118140960795 + 673047 * 2 ^ 59
def prefixEnd_673047 : Nat := 4983230072969 + 3 ^ 40 * 673047 * 2
def baseEnd_673047 : Nat := 153598495140770415207653

theorem tailTrace_673047 : CollatzResearch.WordTrace tailWord_673047 prefixEnd_673047 153598495140770415207653 := by
  unfold tailWord_673047
  simp only [CollatzResearch.WordTrace]
  refine ⟨24548040792673141121289395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16365360528448760747526263 24548040792673141121289395)
  ·
    refine ⟨36822061189009711681934093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24548040792673141121289395 36822061189009711681934093)
    ·
      refine ⟨13808272945878641880725285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36822061189009711681934093 13808272945878641880725285)
      ·
        refine ⟨2589051177352245352635991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13808272945878641880725285 2589051177352245352635991)
        ·
          refine ⟨3883576766028368028953987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589051177352245352635991 3883576766028368028953987)
          ·
            refine ⟨5825365149042552043430981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883576766028368028953987 5825365149042552043430981)
            ·
              refine ⟨1092255965445478508143309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5825365149042552043430981 1092255965445478508143309)
              ·
                refine ⟨409595987042054440553741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1092255965445478508143309 409595987042054440553741)
                ·
                  refine ⟨153598495140770415207653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409595987042054440553741 153598495140770415207653)
                  ·
                    rfl

theorem cell21_673047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 3].length) (baseStart_673047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673047 prefixEnd_673047 := by exact prefixLift 673047
  have htrace : WordTrace (prefixWord ++ tailWord_673047) baseStart_673047 baseEnd_673047 := by
    simpa [prefixWord, tailWord_673047, baseEnd_673047] using wordTrace_append hprefix tailTrace_673047
  have hstable : (prefixWord ++ tailWord_673047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673047).length < 2 ^ (prefixWord ++ tailWord_673047).sum := by decide
  have hdescent : baseEnd_673047 < baseStart_673047 := by decide
  rcases family_descends (prefixWord ++ tailWord_673047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673061 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 4]
def baseStart_673061 : Nat := 118140960795 + 673061 * 2 ^ 59
def prefixEnd_673061 : Nat := 4983230072969 + 3 ^ 40 * 673061 * 2
def baseEnd_673061 : Nat := 153601690131509501974291

theorem tailTrace_673061 : CollatzResearch.WordTrace tailWord_673061 prefixEnd_673061 153601690131509501974291 := by
  unfold tailWord_673061
  simp only [CollatzResearch.WordTrace]
  refine ⟨24548551414622421512299037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16365700943081614341532691 24548551414622421512299037)
  ·
    refine ⟨9205706780483408067112139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24548551414622421512299037 9205706780483408067112139)
    ·
      refine ⟨13808560170725112100668209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9205706780483408067112139 13808560170725112100668209)
      ·
        refine ⟨10356420128043834075501157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13808560170725112100668209 10356420128043834075501157)
        ·
          refine ⟨1941828774008218889156467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10356420128043834075501157 1941828774008218889156467)
          ·
            refine ⟨2912743161012328333734701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941828774008218889156467 2912743161012328333734701)
            ·
              refine ⟨1092278685379623125150513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2912743161012328333734701 1092278685379623125150513)
              ·
                refine ⟨819209014034717343862885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092278685379623125150513 819209014034717343862885)
                ·
                  refine ⟨153601690131509501974291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819209014034717343862885 153601690131509501974291)
                  ·
                    rfl

theorem cell21_673061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_673061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673061 prefixEnd_673061 := by exact prefixLift 673061
  have htrace : WordTrace (prefixWord ++ tailWord_673061) baseStart_673061 baseEnd_673061 := by
    simpa [prefixWord, tailWord_673061, baseEnd_673061] using wordTrace_append hprefix tailTrace_673061
  have hstable : (prefixWord ++ tailWord_673061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673061).length < 2 ^ (prefixWord ++ tailWord_673061).sum := by decide
  have hdescent : baseEnd_673061 < baseStart_673061 := by decide
  rcases family_descends (prefixWord ++ tailWord_673061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673092 : List Nat := [2, 3, 4, 1, 1, 2, 1, 7]
def baseStart_673092 : Nat := 118140960795 + 673092 * 2 ^ 59
def prefixEnd_673092 : Nat := 4983230072969 + 3 ^ 40 * 673092 * 2
def baseEnd_673092 : Nat := 51202921584620112319187

theorem tailTrace_673092 : CollatzResearch.WordTrace tailWord_673092 prefixEnd_673092 51202921584620112319187 := by
  unfold tailWord_673092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274841038755056903338765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16366454718340075871118353 12274841038755056903338765)
  ·
    refine ⟨4603065389533146338752037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12274841038755056903338765 4603065389533146338752037)
    ·
      refine ⟨863074760537464938516007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4603065389533146338752037 863074760537464938516007)
      ·
        refine ⟨1294612140806197407774011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863074760537464938516007 1294612140806197407774011)
        ·
          refine ⟨1941918211209296111661017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294612140806197407774011 1941918211209296111661017)
          ·
            refine ⟨1456438658406972083745763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941918211209296111661017 1456438658406972083745763)
            ·
              refine ⟨2184657987610458125618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456438658406972083745763 2184657987610458125618645)
              ·
                refine ⟨51202921584620112319187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2184657987610458125618645 51202921584620112319187)
                ·
                  rfl

theorem cell21_673092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_673092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673092 prefixEnd_673092 := by exact prefixLift 673092
  have htrace : WordTrace (prefixWord ++ tailWord_673092) baseStart_673092 baseEnd_673092 := by
    simpa [prefixWord, tailWord_673092, baseEnd_673092] using wordTrace_append hprefix tailTrace_673092
  have hstable : (prefixWord ++ tailWord_673092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673092).length < 2 ^ (prefixWord ++ tailWord_673092).sum := by decide
  have hdescent : baseEnd_673092 < baseStart_673092 := by decide
  rcases family_descends (prefixWord ++ tailWord_673092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673120 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_673120 : Nat := 118140960795 + 673120 * 2 ^ 59
def prefixEnd_673120 : Nat := 4983230072969 + 3 ^ 40 * 673120 * 2
def baseEnd_673120 : Nat := 153615154735338510490837

theorem tailTrace_673120 : CollatzResearch.WordTrace tailWord_673120 prefixEnd_673120 153615154735338510490837 := by
  unfold tailWord_673120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12275351660704337294348407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16367135547605783059131209 12275351660704337294348407)
  ·
    refine ⟨18413027491056505941522611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12275351660704337294348407 18413027491056505941522611)
    ·
      refine ⟨27619541236584758912283917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18413027491056505941522611 27619541236584758912283917)
      ·
        refine ⟨10357327963719284592106469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27619541236584758912283917 10357327963719284592106469)
        ·
          refine ⟨1941998993197365861019963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10357327963719284592106469 1941998993197365861019963)
          ·
            refine ⟨2912998489796048791529945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941998993197365861019963 2912998489796048791529945)
            ·
              refine ⟨2184748867347036593647459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2912998489796048791529945 2184748867347036593647459)
              ·
                refine ⟨3277123301020554890471189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184748867347036593647459 3277123301020554890471189)
                ·
                  refine ⟨153615154735338510490837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3277123301020554890471189 153615154735338510490837)
                  ·
                    rfl

theorem cell21_673120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_673120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673120 prefixEnd_673120 := by exact prefixLift 673120
  have htrace : WordTrace (prefixWord ++ tailWord_673120) baseStart_673120 baseEnd_673120 := by
    simpa [prefixWord, tailWord_673120, baseEnd_673120] using wordTrace_append hprefix tailTrace_673120
  have hstable : (prefixWord ++ tailWord_673120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673120).length < 2 ^ (prefixWord ++ tailWord_673120).sum := by decide
  have hdescent : baseEnd_673120 < baseStart_673120 := by decide
  rcases family_descends (prefixWord ++ tailWord_673120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673137 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 4]
def baseStart_673137 : Nat := 118140960795 + 673137 * 2 ^ 59
def prefixEnd_673137 : Nat := 4983230072969 + 3 ^ 40 * 673137 * 2
def baseEnd_673137 : Nat := 153619034366950258707469

theorem tailTrace_673137 : CollatzResearch.WordTrace tailWord_673137 prefixEnd_673137 153619034366950258707469 := by
  unfold tailWord_673137
  simp only [CollatzResearch.WordTrace]
  refine ⟨24551323362347086492065665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16367548908231390994710443 24551323362347086492065665)
  ·
    refine ⟨18413492521760314869049249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24551323362347086492065665 18413492521760314869049249)
    ·
      refine ⟨13810119391320236151786937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18413492521760314869049249 13810119391320236151786937)
      ·
        refine ⟨10357589543490177113840203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13810119391320236151786937 10357589543490177113840203)
        ·
          refine ⟨15536384315235265670760305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357589543490177113840203 15536384315235265670760305)
          ·
            refine ⟨11652288236426449253070229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15536384315235265670760305 11652288236426449253070229)
            ·
              refine ⟨546201011082489808737667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11652288236426449253070229 546201011082489808737667)
              ·
                refine ⟨819301516623734713106501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546201011082489808737667 819301516623734713106501)
                ·
                  refine ⟨153619034366950258707469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819301516623734713106501 153619034366950258707469)
                  ·
                    rfl

theorem cell21_673137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_673137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673137 prefixEnd_673137 := by exact prefixLift 673137
  have htrace : WordTrace (prefixWord ++ tailWord_673137) baseStart_673137 baseEnd_673137 := by
    simpa [prefixWord, tailWord_673137, baseEnd_673137] using wordTrace_append hprefix tailTrace_673137
  have hstable : (prefixWord ++ tailWord_673137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673137).length < 2 ^ (prefixWord ++ tailWord_673137).sum := by decide
  have hdescent : baseEnd_673137 < baseStart_673137 := by decide
  rcases family_descends (prefixWord ++ tailWord_673137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673196 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_673196 : Nat := 118140960795 + 673196 * 2 ^ 59
def prefixEnd_673196 : Nat := 4983230072969 + 3 ^ 40 * 673196 * 2
def baseEnd_673196 : Nat := 153632498970779267224015

theorem tailTrace_673196 : CollatzResearch.WordTrace tailWord_673196 prefixEnd_673196 153632498970779267224015 := by
  unfold tailWord_673196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12276737634566669784231721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16368983512755559712308961 12276737634566669784231721)
  ·
    refine ⟨9207553225925002338173791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12276737634566669784231721 9207553225925002338173791)
    ·
      refine ⟨13811329838887503507260687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9207553225925002338173791 13811329838887503507260687)
      ·
        refine ⟨20716994758331255260891031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13811329838887503507260687 20716994758331255260891031)
        ·
          refine ⟨31075492137496882891336547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20716994758331255260891031 31075492137496882891336547)
          ·
            refine ⟨46613238206245324337004821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31075492137496882891336547 46613238206245324337004821)
            ·
              refine ⟨2184995540917749578297101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46613238206245324337004821 2184995540917749578297101)
              ·
                refine ⟨819373327844156091861413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184995540917749578297101 819373327844156091861413)
                ·
                  refine ⟨153632498970779267224015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819373327844156091861413 153632498970779267224015)
                  ·
                    rfl

theorem cell21_673196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_673196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673196 prefixEnd_673196 := by exact prefixLift 673196
  have htrace : WordTrace (prefixWord ++ tailWord_673196) baseStart_673196 baseEnd_673196 := by
    simpa [prefixWord, tailWord_673196, baseEnd_673196] using wordTrace_append hprefix tailTrace_673196
  have hstable : (prefixWord ++ tailWord_673196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673196).length < 2 ^ (prefixWord ++ tailWord_673196).sum := by decide
  have hdescent : baseEnd_673196 < baseStart_673196 := by decide
  rcases family_descends (prefixWord ++ tailWord_673196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673241 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_673241 : Nat := 118140960795 + 673241 * 2 ^ 59
def prefixEnd_673241 : Nat := 4983230072969 + 3 ^ 40 * 673241 * 2
def baseEnd_673241 : Nat := 153642768583869188973923

theorem tailTrace_673241 : CollatzResearch.WordTrace tailWord_673241 prefixEnd_673241 153642768583869188973923 := by
  unfold tailWord_673241
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555116553970312253851577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16370077702646874835901051 24555116553970312253851577)
  ·
    refine ⟨18416337415477734190388683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24555116553970312253851577 18416337415477734190388683)
    ·
      refine ⟨27624506123216601285583025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18416337415477734190388683 27624506123216601285583025)
      ·
        refine ⟨20718379592412450964187269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27624506123216601285583025 20718379592412450964187269)
        ·
          refine ⟨3884696173577334555785113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20718379592412450964187269 3884696173577334555785113)
          ·
            refine ⟨2913522130183000916838835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884696173577334555785113 2913522130183000916838835)
            ·
              refine ⟨4370283195274501375258253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913522130183000916838835 4370283195274501375258253)
              ·
                refine ⟨1638856198227938015721845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4370283195274501375258253 1638856198227938015721845)
                ·
                  refine ⟨153642768583869188973923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1638856198227938015721845 153642768583869188973923)
                  ·
                    rfl

theorem cell21_673241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_673241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673241 prefixEnd_673241 := by exact prefixLift 673241
  have htrace : WordTrace (prefixWord ++ tailWord_673241) baseStart_673241 baseEnd_673241 := by
    simpa [prefixWord, tailWord_673241, baseEnd_673241] using wordTrace_append hprefix tailTrace_673241
  have hstable : (prefixWord ++ tailWord_673241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673241).length < 2 ^ (prefixWord ++ tailWord_673241).sum := by decide
  have hdescent : baseEnd_673241 < baseStart_673241 := by decide
  rcases family_descends (prefixWord ++ tailWord_673241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673261 : List Nat := [1, 5, 1, 3, 2, 2, 2, 5]
def baseStart_673261 : Nat := 118140960795 + 673261 * 2 ^ 59
def prefixEnd_673261 : Nat := 4983230072969 + 3 ^ 40 * 673261 * 2
def baseEnd_673261 : Nat := 51215777618784532880183

theorem tailTrace_673261 : CollatzResearch.WordTrace tailWord_673261 prefixEnd_673261 51215777618784532880183 := by
  unfold tailWord_673261
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555846013897855669579637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16370564009265237113053091 24555846013897855669579637)
  ·
    refine ⟨2302110563802923969023091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24555846013897855669579637 2302110563802923969023091)
    ·
      refine ⟨3453165845704385953534637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302110563802923969023091 3453165845704385953534637)
      ·
        refine ⟨1294937192139144732575489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3453165845704385953534637 1294937192139144732575489)
        ·
          refine ⟨971202894104358549431617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294937192139144732575489 971202894104358549431617)
          ·
            refine ⟨728402170578268912073713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971202894104358549431617 728402170578268912073713)
            ·
              refine ⟨546301627933701684055285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728402170578268912073713 546301627933701684055285)
              ·
                refine ⟨51215777618784532880183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546301627933701684055285 51215777618784532880183)
                ·
                  rfl

theorem cell21_673261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 5].length) (baseStart_673261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673261 prefixEnd_673261 := by exact prefixLift 673261
  have htrace : WordTrace (prefixWord ++ tailWord_673261) baseStart_673261 baseEnd_673261 := by
    simpa [prefixWord, tailWord_673261, baseEnd_673261] using wordTrace_append hprefix tailTrace_673261
  have hstable : (prefixWord ++ tailWord_673261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673261).length < 2 ^ (prefixWord ++ tailWord_673261).sum := by decide
  have hdescent : baseEnd_673261 < baseStart_673261 := by decide
  rcases family_descends (prefixWord ++ tailWord_673261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673292 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_673292 : Nat := 118140960795 + 673292 * 2 ^ 59
def prefixEnd_673292 : Nat := 4983230072969 + 3 ^ 40 * 673292 * 2
def baseEnd_673292 : Nat := 153654407478704433623819

theorem tailTrace_673292 : CollatzResearch.WordTrace tailWord_673292 prefixEnd_673292 153654407478704433623819 := by
  unfold tailWord_673292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12278488338392773981979065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16371317784523698642638753 12278488338392773981979065)
  ·
    refine ⟨9208866253794580486484299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12278488338392773981979065 9208866253794580486484299)
    ·
      refine ⟨13813299380691870729726449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9208866253794580486484299 13813299380691870729726449)
      ·
        refine ⟨10359974535518903047294837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13813299380691870729726449 10359974535518903047294837)
        ·
          refine ⟨971247612704897160683891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10359974535518903047294837 971247612704897160683891)
          ·
            refine ⟨1456871419057345741025837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971247612704897160683891 1456871419057345741025837)
            ·
              refine ⟨546326782146504652884689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1456871419057345741025837 546326782146504652884689)
              ·
                refine ⟨409745086609878489663517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546326782146504652884689 409745086609878489663517)
                ·
                  refine ⟨153654407478704433623819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409745086609878489663517 153654407478704433623819)
                  ·
                    rfl

theorem cell21_673292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_673292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673292 prefixEnd_673292 := by exact prefixLift 673292
  have htrace : WordTrace (prefixWord ++ tailWord_673292) baseStart_673292 baseEnd_673292 := by
    simpa [prefixWord, tailWord_673292, baseEnd_673292] using wordTrace_append hprefix tailTrace_673292
  have hstable : (prefixWord ++ tailWord_673292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673292).length < 2 ^ (prefixWord ++ tailWord_673292).sum := by decide
  have hdescent : baseEnd_673292 < baseStart_673292 := by decide
  rcases family_descends (prefixWord ++ tailWord_673292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673351 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 3]
def baseStart_673351 : Nat := 118140960795 + 673351 * 2 ^ 59
def prefixEnd_673351 : Nat := 4983230072969 + 3 ^ 40 * 673351 * 2
def baseEnd_673351 : Nat := 153667872082533442140365

theorem tailTrace_673351 : CollatzResearch.WordTrace tailWord_673351 prefixEnd_673351 153667872082533442140365 := by
  unfold tailWord_673351
  simp only [CollatzResearch.WordTrace]
  refine ⟨24559128583571801040355907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16372752389047867360237271 24559128583571801040355907)
  ·
    refine ⟨36838692875357701560533861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24559128583571801040355907 36838692875357701560533861)
    ·
      refine ⟨6907254914129569042600099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36838692875357701560533861 6907254914129569042600099)
      ·
        refine ⟨10360882371194353563900149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907254914129569042600099 10360882371194353563900149)
        ·
          refine ⟨971332722299470646615639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10360882371194353563900149 971332722299470646615639)
          ·
            refine ⟨1456999083449205969923459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971332722299470646615639 1456999083449205969923459)
            ·
              refine ⟨2185498625173808954885189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456999083449205969923459 2185498625173808954885189)
              ·
                refine ⟨409780992220089179040973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2185498625173808954885189 409780992220089179040973)
                ·
                  refine ⟨153667872082533442140365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409780992220089179040973 153667872082533442140365)
                  ·
                    rfl

theorem cell21_673351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 3].length) (baseStart_673351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673351 prefixEnd_673351 := by exact prefixLift 673351
  have htrace : WordTrace (prefixWord ++ tailWord_673351) baseStart_673351 baseEnd_673351 := by
    simpa [prefixWord, tailWord_673351, baseEnd_673351] using wordTrace_append hprefix tailTrace_673351
  have hstable : (prefixWord ++ tailWord_673351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673351).length < 2 ^ (prefixWord ++ tailWord_673351).sum := by decide
  have hdescent : baseEnd_673351 < baseStart_673351 := by decide
  rcases family_descends (prefixWord ++ tailWord_673351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673379 : List Nat := [1, 1, 1, 5, 1, 4, 3, 5]
def baseStart_673379 : Nat := 118140960795 + 673379 * 2 ^ 59
def prefixEnd_673379 : Nat := 4983230072969 + 3 ^ 40 * 673379 * 2
def baseEnd_673379 : Nat := 51224754021337205224547

theorem tailTrace_673379 : CollatzResearch.WordTrace tailWord_673379 prefixEnd_673379 51224754021337205224547 := by
  unfold tailWord_673379
  simp only [CollatzResearch.WordTrace]
  refine ⟨24560149827470361822375191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16373433218313574548250127 24560149827470361822375191)
  ·
    refine ⟨36840224741205542733562787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24560149827470361822375191 36840224741205542733562787)
    ·
      refine ⟨55260337111808314100344181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36840224741205542733562787 55260337111808314100344181)
      ·
        refine ⟨5180656604232029446907267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55260337111808314100344181 5180656604232029446907267)
        ·
          refine ⟨7770984906348044170360901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180656604232029446907267 7770984906348044170360901)
          ·
            refine ⟨1457059669940258281942669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7770984906348044170360901 1457059669940258281942669)
            ·
              refine ⟨546397376227596855728501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1457059669940258281942669 546397376227596855728501)
              ·
                refine ⟨51224754021337205224547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546397376227596855728501 51224754021337205224547)
                ·
                  rfl

theorem cell21_673379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 5].length) (baseStart_673379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673379 prefixEnd_673379 := by exact prefixLift 673379
  have htrace : WordTrace (prefixWord ++ tailWord_673379) baseStart_673379 baseEnd_673379 := by
    simpa [prefixWord, tailWord_673379, baseEnd_673379] using wordTrace_append hprefix tailTrace_673379
  have hstable : (prefixWord ++ tailWord_673379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673379).length < 2 ^ (prefixWord ++ tailWord_673379).sum := by decide
  have hdescent : baseEnd_673379 < baseStart_673379 := by decide
  rcases family_descends (prefixWord ++ tailWord_673379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673517 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 4]
def baseStart_673517 : Nat := 118140960795 + 673517 * 2 ^ 59
def prefixEnd_673517 : Nat := 4983230072969 + 3 ^ 40 * 673517 * 2
def baseEnd_673517 : Nat := 153705755544154042373359

theorem tailTrace_673517 : CollatzResearch.WordTrace tailWord_673517 prefixEnd_673517 153705755544154042373359 := by
  unfold tailWord_673517
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565183100970411390898805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16376788733980274260599203 24565183100970411390898805)
  ·
    refine ⟨2302985915715976067896763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24565183100970411390898805 2302985915715976067896763)
    ·
      refine ⟨3454478873573964101845145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302985915715976067896763 3454478873573964101845145)
      ·
        refine ⟨2590859155180473076383859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3454478873573964101845145 2590859155180473076383859)
        ·
          refine ⟨3886288732770709614575789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590859155180473076383859 3886288732770709614575789)
          ·
            refine ⟨1457358274789016105465921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3886288732770709614575789 1457358274789016105465921)
            ·
              refine ⟨1093018706091762079099441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457358274789016105465921 1093018706091762079099441)
              ·
                refine ⟨819764029568821559324581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093018706091762079099441 819764029568821559324581)
                ·
                  refine ⟨153705755544154042373359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819764029568821559324581 153705755544154042373359)
                  ·
                    rfl

theorem cell21_673517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_673517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673517 prefixEnd_673517 := by exact prefixLift 673517
  have htrace : WordTrace (prefixWord ++ tailWord_673517) baseStart_673517 baseEnd_673517 := by
    simpa [prefixWord, tailWord_673517, baseEnd_673517] using wordTrace_append hprefix tailTrace_673517
  have hstable : (prefixWord ++ tailWord_673517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673517).length < 2 ^ (prefixWord ++ tailWord_673517).sum := by decide
  have hdescent : baseEnd_673517 < baseStart_673517 := by decide
  rcases family_descends (prefixWord ++ tailWord_673517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673562 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_673562 : Nat := 118140960795 + 673562 * 2 ^ 59
def prefixEnd_673562 : Nat := 4983230072969 + 3 ^ 40 * 673562 * 2
def baseEnd_673562 : Nat := 153716025157243964123267

theorem tailTrace_673562 : CollatzResearch.WordTrace tailWord_673562 prefixEnd_673562 153716025157243964123267 := by
  unfold tailWord_673562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141706096451846019071735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16377882923871589384191293 6141706096451846019071735)
  ·
    refine ⟨9212559144677769028607603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6141706096451846019071735 9212559144677769028607603)
    ·
      refine ⟨13818838717016653542911405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9212559144677769028607603 13818838717016653542911405)
      ·
        refine ⟨5182064518881245078591777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13818838717016653542911405 5182064518881245078591777)
        ·
          refine ⟨3886548389160933808943833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5182064518881245078591777 3886548389160933808943833)
          ·
            refine ⟨2914911291870700356707875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3886548389160933808943833 2914911291870700356707875)
            ·
              refine ⟨4372366937806050535061813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914911291870700356707875 4372366937806050535061813)
              ·
                refine ⟨409909400419317237662045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4372366937806050535061813 409909400419317237662045)
                ·
                  refine ⟨153716025157243964123267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409909400419317237662045 153716025157243964123267)
                  ·
                    rfl

theorem cell21_673562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_673562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673562 prefixEnd_673562 := by exact prefixLift 673562
  have htrace : WordTrace (prefixWord ++ tailWord_673562) baseStart_673562 baseEnd_673562 := by
    simpa [prefixWord, tailWord_673562, baseEnd_673562] using wordTrace_append hprefix tailTrace_673562
  have hstable : (prefixWord ++ tailWord_673562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673562).length < 2 ^ (prefixWord ++ tailWord_673562).sum := by decide
  have hdescent : baseEnd_673562 < baseStart_673562 := by decide
  rcases family_descends (prefixWord ++ tailWord_673562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673576 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_673576 : Nat := 118140960795 + 673576 * 2 ^ 59
def prefixEnd_673576 : Nat := 4983230072969 + 3 ^ 40 * 673576 * 2
def baseEnd_673576 : Nat := 153719220147983050889905

theorem tailTrace_673576 : CollatzResearch.WordTrace tailWord_673576 prefixEnd_673576 153719220147983050889905 := by
  unfold tailWord_673576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12283667503878332233648291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16378223338504442978197721 12283667503878332233648291)
  ·
    refine ⟨18425501255817498350472437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12283667503878332233648291 18425501255817498350472437)
    ·
      refine ⟨1727390742732890470356791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18425501255817498350472437 1727390742732890470356791)
      ·
        refine ⟨2591086114099335705535187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727390742732890470356791 2591086114099335705535187)
        ·
          refine ⟨3886629171149003558302781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591086114099335705535187 3886629171149003558302781)
          ·
            refine ⟨1457485939180876334363543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3886629171149003558302781 1457485939180876334363543)
            ·
              refine ⟨2186228908771314501545315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457485939180876334363543 2186228908771314501545315)
              ·
                refine ⟨3279343363156971752317973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186228908771314501545315 3279343363156971752317973)
                ·
                  refine ⟨153719220147983050889905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3279343363156971752317973 153719220147983050889905)
                  ·
                    rfl

theorem cell21_673576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_673576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673576 prefixEnd_673576 := by exact prefixLift 673576
  have htrace : WordTrace (prefixWord ++ tailWord_673576) baseStart_673576 baseEnd_673576 := by
    simpa [prefixWord, tailWord_673576, baseEnd_673576] using wordTrace_append hprefix tailTrace_673576
  have hstable : (prefixWord ++ tailWord_673576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673576).length < 2 ^ (prefixWord ++ tailWord_673576).sum := by decide
  have hdescent : baseEnd_673576 < baseStart_673576 := by decide
  rcases family_descends (prefixWord ++ tailWord_673576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673711 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 4]
def baseStart_673711 : Nat := 118140960795 + 673711 * 2 ^ 59
def prefixEnd_673711 : Nat := 4983230072969 + 3 ^ 40 * 673711 * 2
def baseEnd_673711 : Nat := 153750028987252816139629

theorem tailTrace_673711 : CollatzResearch.WordTrace tailWord_673711 prefixEnd_673711 153750028987252816139629 := by
  unfold tailWord_673711
  simp only [CollatzResearch.WordTrace]
  refine ⟨24572258862267582523460987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16381505908178388348973991 24572258862267582523460987)
  ·
    refine ⟨36858388293401373785191481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24572258862267582523460987 36858388293401373785191481)
    ·
      refine ⟨27643791220051030338893611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36858388293401373785191481 27643791220051030338893611)
      ·
        refine ⟨41465686830076545508340417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27643791220051030338893611 41465686830076545508340417)
        ·
          refine ⟨31099265122557409131255313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41465686830076545508340417 31099265122557409131255313)
          ·
            refine ⟨23324448841918056848441485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31099265122557409131255313 23324448841918056848441485)
            ·
              refine ⟨8746668315719271318165557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23324448841918056848441485 8746668315719271318165557)
              ·
                refine ⟨820000154598681686078021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8746668315719271318165557 820000154598681686078021)
                ·
                  refine ⟨153750028987252816139629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820000154598681686078021 153750028987252816139629)
                  ·
                    rfl

theorem cell21_673711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_673711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673711 prefixEnd_673711 := by exact prefixLift 673711
  have htrace : WordTrace (prefixWord ++ tailWord_673711) baseStart_673711 baseEnd_673711 := by
    simpa [prefixWord, tailWord_673711, baseEnd_673711] using wordTrace_append hprefix tailTrace_673711
  have hstable : (prefixWord ++ tailWord_673711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673711).length < 2 ^ (prefixWord ++ tailWord_673711).sum := by decide
  have hdescent : baseEnd_673711 < baseStart_673711 := by decide
  rcases family_descends (prefixWord ++ tailWord_673711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673818 : List Nat := [3, 1, 1, 3, 1, 4, 2, 6]
def baseStart_673818 : Nat := 118140960795 + 673818 * 2 ^ 59
def prefixEnd_673818 : Nat := 4983230072969 + 3 ^ 40 * 673818 * 2
def baseEnd_673818 : Nat := 51258149281681469285359

theorem tailTrace_673818 : CollatzResearch.WordTrace tailWord_673818 prefixEnd_673818 51258149281681469285359 := by
  unfold tailWord_673818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144040368219984949401527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16384107648586626531737405 6144040368219984949401527)
  ·
    refine ⟨9216060552329977424102291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6144040368219984949401527 9216060552329977424102291)
    ·
      refine ⟨13824090828494966136153437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216060552329977424102291 13824090828494966136153437)
      ·
        refine ⟨5184034060685612301057539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13824090828494966136153437 5184034060685612301057539)
        ·
          refine ⟨7776051091028418451586309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184034060685612301057539 7776051091028418451586309)
          ·
            refine ⟨1458009579567828459672433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7776051091028418451586309 1458009579567828459672433)
            ·
              refine ⟨1093507184675871344754325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458009579567828459672433 1093507184675871344754325)
              ·
                refine ⟨51258149281681469285359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1093507184675871344754325 51258149281681469285359)
                ·
                  rfl

theorem cell21_673818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_673818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673818 prefixEnd_673818 := by exact prefixLift 673818
  have htrace : WordTrace (prefixWord ++ tailWord_673818) baseStart_673818 baseEnd_673818 := by
    simpa [prefixWord, tailWord_673818, baseEnd_673818] using wordTrace_append hprefix tailTrace_673818
  have hstable : (prefixWord ++ tailWord_673818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673818).length < 2 ^ (prefixWord ++ tailWord_673818).sum := by decide
  have hdescent : baseEnd_673818 < baseStart_673818 := by decide
  rcases family_descends (prefixWord ++ tailWord_673818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673821 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 4]
def baseStart_673821 : Nat := 118140960795 + 673821 * 2 ^ 59
def prefixEnd_673821 : Nat := 4983230072969 + 3 ^ 40 * 673821 * 2
def baseEnd_673821 : Nat := 153775132485917069306071

theorem tailTrace_673821 : CollatzResearch.WordTrace tailWord_673821 prefixEnd_673821 153775132485917069306071 := by
  unfold tailWord_673821
  simp only [CollatzResearch.WordTrace]
  refine ⟨24576270891869071309965317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16384180594579380873310211 24576270891869071309965317)
  ·
    refine ⟨4608050792225450870618497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24576270891869071309965317 4608050792225450870618497)
    ·
      refine ⟨3456038094169088152963873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4608050792225450870618497 3456038094169088152963873)
      ·
        refine ⟨2592028570626816114722905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3456038094169088152963873 2592028570626816114722905)
        ·
          refine ⟨1944021427970112086042179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592028570626816114722905 1944021427970112086042179)
          ·
            refine ⟨2916032141955168129063269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944021427970112086042179 2916032141955168129063269)
            ·
              refine ⟨546756026616594024199363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2916032141955168129063269 546756026616594024199363)
              ·
                refine ⟨820134039924891036299045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546756026616594024199363 820134039924891036299045)
                ·
                  refine ⟨153775132485917069306071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820134039924891036299045 153775132485917069306071)
                  ·
                    rfl

theorem cell21_673821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_673821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673821 prefixEnd_673821 := by exact prefixLift 673821
  have htrace : WordTrace (prefixWord ++ tailWord_673821) baseStart_673821 baseEnd_673821 := by
    simpa [prefixWord, tailWord_673821, baseEnd_673821] using wordTrace_append hprefix tailTrace_673821
  have hstable : (prefixWord ++ tailWord_673821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673821).length < 2 ^ (prefixWord ++ tailWord_673821).sum := by decide
  have hdescent : baseEnd_673821 < baseStart_673821 := by decide
  rcases family_descends (prefixWord ++ tailWord_673821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673925 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 5]
def baseStart_673925 : Nat := 118140960795 + 673925 * 2 ^ 59
def prefixEnd_673925 : Nat := 4983230072969 + 3 ^ 40 * 673925 * 2
def baseEnd_673925 : Nat := 153798866702835999572525

theorem tailTrace_673925 : CollatzResearch.WordTrace tailWord_673925 prefixEnd_673925 153798866702835999572525 := by
  unfold tailWord_673925
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580064083492297071751229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16386709388994864714500819 24580064083492297071751229)
  ·
    refine ⟨9217524031309611401906711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24580064083492297071751229 9217524031309611401906711)
    ·
      refine ⟨13826286046964417102860067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9217524031309611401906711 13826286046964417102860067)
      ·
        refine ⟨20739429070446625654290101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13826286046964417102860067 20739429070446625654290101)
        ·
          refine ⟨1944321475354371155089697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20739429070446625654290101 1944321475354371155089697)
          ·
            refine ⟨1458241106515778366317273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944321475354371155089697 1458241106515778366317273)
            ·
              refine ⟨1093680829886833774737955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458241106515778366317273 1093680829886833774737955)
              ·
                refine ⟨1640521244830250662106933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093680829886833774737955 1640521244830250662106933)
                ·
                  refine ⟨153798866702835999572525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1640521244830250662106933 153798866702835999572525)
                  ·
                    rfl

theorem cell21_673925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_673925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_673925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_673925 prefixEnd_673925 := by exact prefixLift 673925
  have htrace : WordTrace (prefixWord ++ tailWord_673925) baseStart_673925 baseEnd_673925 := by
    simpa [prefixWord, tailWord_673925, baseEnd_673925] using wordTrace_append hprefix tailTrace_673925
  have hstable : (prefixWord ++ tailWord_673925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673925).length < 2 ^ (prefixWord ++ tailWord_673925).sum := by decide
  have hdescent : baseEnd_673925 < baseStart_673925 := by decide
  rcases family_descends (prefixWord ++ tailWord_673925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674029 : List Nat := [1, 5, 1, 2, 12]
def baseStart_674029 : Nat := 118140960795 + 674029 * 2 ^ 59
def prefixEnd_674029 : Nat := 4983230072969 + 3 ^ 40 * 674029 * 2
def baseEnd_674029 : Nat := 1899044455799443578259

theorem tailTrace_674029 : CollatzResearch.WordTrace tailWord_674029 prefixEnd_674029 1899044455799443578259 := by
  unfold tailWord_674029
  simp only [CollatzResearch.WordTrace]
  refine ⟨24583857275115522833537141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16389238183410348555691427 24583857275115522833537141)
  ·
    refine ⟨2304736619542080265644107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24583857275115522833537141 2304736619542080265644107)
    ·
      refine ⟨3457104929313120398466161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304736619542080265644107 3457104929313120398466161)
      ·
        refine ⟨2592828696984840298849621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3457104929313120398466161 2592828696984840298849621)
        ·
          refine ⟨1899044455799443578259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2592828696984840298849621 1899044455799443578259)
          ·
            rfl

theorem cell21_674029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 12].length) (baseStart_674029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674029 prefixEnd_674029 := by exact prefixLift 674029
  have htrace : WordTrace (prefixWord ++ tailWord_674029) baseStart_674029 baseEnd_674029 := by
    simpa [prefixWord, tailWord_674029, baseEnd_674029] using wordTrace_append hprefix tailTrace_674029
  have hstable : (prefixWord ++ tailWord_674029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674029).length < 2 ^ (prefixWord ++ tailWord_674029).sum := by decide
  have hdescent : baseEnd_674029 < baseStart_674029 := by decide
  rcases family_descends (prefixWord ++ tailWord_674029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674043 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_674043 : Nat := 118140960795 + 674043 * 2 ^ 59
def prefixEnd_674043 : Nat := 4983230072969 + 3 ^ 40 * 674043 * 2
def baseEnd_674043 : Nat := 153825795910494016605617

theorem tailTrace_674043 : CollatzResearch.WordTrace tailWord_674043 prefixEnd_674043 153825795910494016605617 := by
  unfold tailWord_674043
  simp only [CollatzResearch.WordTrace]
  refine ⟨24584367897064803224546783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16389578598043202149697855 24584367897064803224546783)
  ·
    refine ⟨36876551845597204836820175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24584367897064803224546783 36876551845597204836820175)
    ·
      refine ⟨55314827768395807255230263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36876551845597204836820175 55314827768395807255230263)
      ·
        refine ⟨82972241652593710882845395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55314827768395807255230263 82972241652593710882845395)
        ·
          refine ⟨124458362478890566324268093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82972241652593710882845395 124458362478890566324268093)
          ·
            refine ⟨46671885929583962371600535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124458362478890566324268093 46671885929583962371600535)
            ·
              refine ⟨70007828894375943557400803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46671885929583962371600535 70007828894375943557400803)
              ·
                refine ⟨105011743341563915336101205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70007828894375943557400803 105011743341563915336101205)
                ·
                  refine ⟨153825795910494016605617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 105011743341563915336101205 153825795910494016605617)
                  ·
                    rfl

theorem cell21_674043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_674043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674043 prefixEnd_674043 := by exact prefixLift 674043
  have htrace : WordTrace (prefixWord ++ tailWord_674043) baseStart_674043 baseEnd_674043 := by
    simpa [prefixWord, tailWord_674043, baseEnd_674043] using wordTrace_append hprefix tailTrace_674043
  have hstable : (prefixWord ++ tailWord_674043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674043).length < 2 ^ (prefixWord ++ tailWord_674043).sum := by decide
  have hdescent : baseEnd_674043 < baseStart_674043 := by decide
  rcases family_descends (prefixWord ++ tailWord_674043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674060 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_674060 : Nat := 118140960795 + 674060 * 2 ^ 59
def prefixEnd_674060 : Nat := 4983230072969 + 3 ^ 40 * 674060 * 2
def baseEnd_674060 : Nat := 153829675542105764822249

theorem tailTrace_674060 : CollatzResearch.WordTrace tailWord_674060 prefixEnd_674060 153829675542105764822249 := by
  unfold tailWord_674060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12292493969001607563957817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16389991958668810085277089 12292493969001607563957817)
  ·
    refine ⟨9219370476751205672968363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12292493969001607563957817 9219370476751205672968363)
    ·
      refine ⟨13829055715126808509452545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219370476751205672968363 13829055715126808509452545)
      ·
        refine ⟨10371791786345106382089409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13829055715126808509452545 10371791786345106382089409)
        ·
          refine ⟨7778843839758829786567057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10371791786345106382089409 7778843839758829786567057)
          ·
            refine ⟨5834132879819122339925293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7778843839758829786567057 5834132879819122339925293)
            ·
              refine ⟨2187799829932170877471985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5834132879819122339925293 2187799829932170877471985)
              ·
                refine ⟨1640849872449128158103989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187799829932170877471985 1640849872449128158103989)
                ·
                  refine ⟨153829675542105764822249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1640849872449128158103989 153829675542105764822249)
                  ·
                    rfl

theorem cell21_674060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_674060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674060 prefixEnd_674060 := by exact prefixLift 674060
  have htrace : WordTrace (prefixWord ++ tailWord_674060) baseStart_674060 baseEnd_674060 := by
    simpa [prefixWord, tailWord_674060, baseEnd_674060] using wordTrace_append hprefix tailTrace_674060
  have hstable : (prefixWord ++ tailWord_674060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674060).length < 2 ^ (prefixWord ++ tailWord_674060).sum := by decide
  have hdescent : baseEnd_674060 < baseStart_674060 := by decide
  rcases family_descends (prefixWord ++ tailWord_674060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674108 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_674108 : Nat := 118140960795 + 674108 * 2 ^ 59
def prefixEnd_674108 : Nat := 4983230072969 + 3 ^ 40 * 674108 * 2
def baseEnd_674108 : Nat := 153840629796068348022151

theorem tailTrace_674108 : CollatzResearch.WordTrace tailWord_674108 prefixEnd_674108 153840629796068348022151 := by
  unfold tailWord_674108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293369320914659662831489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16391159094552879550441985 12293369320914659662831489)
  ·
    refine ⟨9220026990685994747123617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12293369320914659662831489 9220026990685994747123617)
    ·
      refine ⟨6915020243014496060342713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9220026990685994747123617 6915020243014496060342713)
      ·
        refine ⟨5186265182260872045257035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6915020243014496060342713 5186265182260872045257035)
        ·
          refine ⟨7779397773391308067885553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186265182260872045257035 7779397773391308067885553)
          ·
            refine ⟨5834548330043481050914165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7779397773391308067885553 5834548330043481050914165)
            ·
              refine ⟨546988905941576348523203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5834548330043481050914165 546988905941576348523203)
              ·
                refine ⟨820483358912364522784805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546988905941576348523203 820483358912364522784805)
                ·
                  refine ⟨153840629796068348022151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820483358912364522784805 153840629796068348022151)
                  ·
                    rfl

theorem cell21_674108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_674108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674108 prefixEnd_674108 := by exact prefixLift 674108
  have htrace : WordTrace (prefixWord ++ tailWord_674108) baseStart_674108 baseEnd_674108 := by
    simpa [prefixWord, tailWord_674108, baseEnd_674108] using wordTrace_append hprefix tailTrace_674108
  have hstable : (prefixWord ++ tailWord_674108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674108).length < 2 ^ (prefixWord ++ tailWord_674108).sum := by decide
  have hdescent : baseEnd_674108 < baseStart_674108 := by decide
  rcases family_descends (prefixWord ++ tailWord_674108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674229 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 5]
def baseStart_674229 : Nat := 118140960795 + 674229 * 2 ^ 59
def prefixEnd_674229 : Nat := 4983230072969 + 3 ^ 40 * 674229 * 2
def baseEnd_674229 : Nat := 153868243644599026505237

theorem tailTrace_674229 : CollatzResearch.WordTrace tailWord_674229 prefixEnd_674229 153868243644599026505237 := by
  unfold tailWord_674229
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591151874390956990817741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16394101249593971327211827 24591151874390956990817741)
  ·
    refine ⟨9221681952896608871556653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24591151874390956990817741 9221681952896608871556653)
    ·
      refine ⟨3458130732336228326833745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9221681952896608871556653 3458130732336228326833745)
      ·
        refine ⟨2593598049252171245125309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3458130732336228326833745 2593598049252171245125309)
        ·
          refine ⟨972599268469564216921991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2593598049252171245125309 972599268469564216921991)
          ·
            refine ⟨1458898902704346325382987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972599268469564216921991 1458898902704346325382987)
            ·
              refine ⟨2188348354056519488074481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458898902704346325382987 2188348354056519488074481)
              ·
                refine ⟨1641261265542389616055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188348354056519488074481 1641261265542389616055861)
                ·
                  refine ⟨153868243644599026505237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641261265542389616055861 153868243644599026505237)
                  ·
                    rfl

theorem cell21_674229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_674229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674229 prefixEnd_674229 := by exact prefixLift 674229
  have htrace : WordTrace (prefixWord ++ tailWord_674229) baseStart_674229 baseEnd_674229 := by
    simpa [prefixWord, tailWord_674229, baseEnd_674229] using wordTrace_append hprefix tailTrace_674229
  have hstable : (prefixWord ++ tailWord_674229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674229).length < 2 ^ (prefixWord ++ tailWord_674229).sum := by decide
  have hdescent : baseEnd_674229 < baseStart_674229 := by decide
  rcases family_descends (prefixWord ++ tailWord_674229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674260 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_674260 : Nat := 118140960795 + 674260 * 2 ^ 59
def prefixEnd_674260 : Nat := 4983230072969 + 3 ^ 40 * 674260 * 2
def baseEnd_674260 : Nat := 153875318266949861488507

theorem tailTrace_674260 : CollatzResearch.WordTrace tailWord_674260 prefixEnd_674260 153875318266949861488507 := by
  unfold tailWord_674260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296141268639324642598117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16394855024852432856797489 12296141268639324642598117)
  ·
    refine ⟨2305526487869873370487147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12296141268639324642598117 2305526487869873370487147)
    ·
      refine ⟨3458289731804810055730721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305526487869873370487147 3458289731804810055730721)
      ·
        refine ⟨2593717298853607541798041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3458289731804810055730721 2593717298853607541798041)
        ·
          refine ⟨1945287974140205656348531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2593717298853607541798041 1945287974140205656348531)
          ·
            refine ⟨2917931961210308484522797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945287974140205656348531 2917931961210308484522797)
            ·
              refine ⟨1094224485453865681696049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2917931961210308484522797 1094224485453865681696049)
              ·
                refine ⟨820668364090399261272037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094224485453865681696049 820668364090399261272037)
                ·
                  refine ⟨153875318266949861488507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820668364090399261272037 153875318266949861488507)
                  ·
                    rfl

theorem cell21_674260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_674260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674260 prefixEnd_674260 := by exact prefixLift 674260
  have htrace : WordTrace (prefixWord ++ tailWord_674260) baseStart_674260 baseEnd_674260 := by
    simpa [prefixWord, tailWord_674260, baseEnd_674260] using wordTrace_append hprefix tailTrace_674260
  have hstable : (prefixWord ++ tailWord_674260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674260).length < 2 ^ (prefixWord ++ tailWord_674260).sum := by decide
  have hdescent : baseEnd_674260 < baseStart_674260 := by decide
  rcases family_descends (prefixWord ++ tailWord_674260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674277 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 4]
def baseStart_674277 : Nat := 118140960795 + 674277 * 2 ^ 59
def prefixEnd_674277 : Nat := 4983230072969 + 3 ^ 40 * 674277 * 2
def baseEnd_674277 : Nat := 153879197898561609705139

theorem tailTrace_674277 : CollatzResearch.WordTrace tailWord_674277 prefixEnd_674277 153879197898561609705139 := by
  unfold tailWord_674277
  simp only [CollatzResearch.WordTrace]
  refine ⟨24592902578217061188565085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16395268385478040792376723 24592902578217061188565085)
  ·
    refine ⟨9222338466831397945711907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24592902578217061188565085 9222338466831397945711907)
    ·
      refine ⟨13833507700247096918567861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222338466831397945711907 13833507700247096918567861)
      ·
        refine ⟨1296891346898165336115737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13833507700247096918567861 1296891346898165336115737)
        ·
          refine ⟨972668510173624002086803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296891346898165336115737 972668510173624002086803)
          ·
            refine ⟨1459002765260436003130205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972668510173624002086803 1459002765260436003130205)
            ·
              refine ⟨547126036972663501173827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1459002765260436003130205 547126036972663501173827)
              ·
                refine ⟨820689055458995251760741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547126036972663501173827 820689055458995251760741)
                ·
                  refine ⟨153879197898561609705139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820689055458995251760741 153879197898561609705139)
                  ·
                    rfl

theorem cell21_674277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_674277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674277 prefixEnd_674277 := by exact prefixLift 674277
  have htrace : WordTrace (prefixWord ++ tailWord_674277) baseStart_674277 baseEnd_674277 := by
    simpa [prefixWord, tailWord_674277, baseEnd_674277] using wordTrace_append hprefix tailTrace_674277
  have hstable : (prefixWord ++ tailWord_674277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674277).length < 2 ^ (prefixWord ++ tailWord_674277).sum := by decide
  have hdescent : baseEnd_674277 < baseStart_674277 := by decide
  rcases family_descends (prefixWord ++ tailWord_674277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674333 : List Nat := [1, 4, 2, 2, 1, 2, 1, 8]
def baseStart_674333 : Nat := 118140960795 + 674333 * 2 ^ 59
def prefixEnd_674333 : Nat := 4983230072969 + 3 ^ 40 * 674333 * 2
def baseEnd_674333 : Nat := 51297325953839318923897

theorem tailTrace_674333 : CollatzResearch.WordTrace tailWord_674333 prefixEnd_674333 51297325953839318923897 := by
  unfold tailWord_674333
  simp only [CollatzResearch.WordTrace]
  refine ⟨24594945066014182752603653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16396630044009455168402435 24594945066014182752603653)
  ·
    refine ⟨4611552199877659266113185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24594945066014182752603653 4611552199877659266113185)
    ·
      refine ⟨3458664149908244449584889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4611552199877659266113185 3458664149908244449584889)
      ·
        refine ⟨2593998112431183337188667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3458664149908244449584889 2593998112431183337188667)
        ·
          refine ⟨3890997168646775005783001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593998112431183337188667 3890997168646775005783001)
          ·
            refine ⟨2918247876485081254337251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3890997168646775005783001 2918247876485081254337251)
            ·
              refine ⟨4377371814727621881505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918247876485081254337251 4377371814727621881505877)
              ·
                refine ⟨51297325953839318923897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4377371814727621881505877 51297325953839318923897)
                ·
                  rfl

theorem cell21_674333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_674333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674333 prefixEnd_674333 := by exact prefixLift 674333
  have htrace : WordTrace (prefixWord ++ tailWord_674333) baseStart_674333 baseEnd_674333 := by
    simpa [prefixWord, tailWord_674333, baseEnd_674333] using wordTrace_append hprefix tailTrace_674333
  have hstable : (prefixWord ++ tailWord_674333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674333).length < 2 ^ (prefixWord ++ tailWord_674333).sum := by decide
  have hdescent : baseEnd_674333 < baseStart_674333 := by decide
  rcases family_descends (prefixWord ++ tailWord_674333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674336 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_674336 : Nat := 118140960795 + 674336 * 2 ^ 59
def prefixEnd_674336 : Nat := 4983230072969 + 3 ^ 40 * 674336 * 2
def baseEnd_674336 : Nat := 153892662502390618221685

theorem tailTrace_674336 : CollatzResearch.WordTrace tailWord_674336 prefixEnd_674336 153892662502390618221685 := by
  unfold tailWord_674336
  simp only [CollatzResearch.WordTrace]
  refine ⟨12297527242501657132481431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16396702990002209509975241 12297527242501657132481431)
  ·
    refine ⟨18446290863752485698722147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12297527242501657132481431 18446290863752485698722147)
    ·
      refine ⟨27669436295628728548083221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18446290863752485698722147 27669436295628728548083221)
      ·
        refine ⟨1297004826357596650691401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27669436295628728548083221 1297004826357596650691401)
        ·
          refine ⟨972753619768197488018551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297004826357596650691401 972753619768197488018551)
          ·
            refine ⟨1459130429652296232027827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972753619768197488018551 1459130429652296232027827)
            ·
              refine ⟨2188695644478444348041741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459130429652296232027827 2188695644478444348041741)
              ·
                refine ⟨820760866679416630515653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2188695644478444348041741 820760866679416630515653)
                ·
                  refine ⟨153892662502390618221685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820760866679416630515653 153892662502390618221685)
                  ·
                    rfl

theorem cell21_674336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_674336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674336 prefixEnd_674336 := by exact prefixLift 674336
  have htrace : WordTrace (prefixWord ++ tailWord_674336) baseStart_674336 baseEnd_674336 := by
    simpa [prefixWord, tailWord_674336, baseEnd_674336] using wordTrace_append hprefix tailTrace_674336
  have hstable : (prefixWord ++ tailWord_674336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674336).length < 2 ^ (prefixWord ++ tailWord_674336).sum := by decide
  have hdescent : baseEnd_674336 < baseStart_674336 := by decide
  rcases family_descends (prefixWord ++ tailWord_674336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674347 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_674347 : Nat := 118140960795 + 674347 * 2 ^ 59
def prefixEnd_674347 : Nat := 4983230072969 + 3 ^ 40 * 674347 * 2
def baseEnd_674347 : Nat := 153895172852257043538329

theorem tailTrace_674347 : CollatzResearch.WordTrace tailWord_674347 prefixEnd_674347 153895172852257043538329 := by
  unfold tailWord_674347
  simp only [CollatzResearch.WordTrace]
  refine ⟨24595455687963463143613295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16396970458642308762408863 24595455687963463143613295)
  ·
    refine ⟨36893183531945194715419943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24595455687963463143613295 36893183531945194715419943)
    ·
      refine ⟨55339775297917792073129915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36893183531945194715419943 55339775297917792073129915)
      ·
        refine ⟨83009662946876688109694873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55339775297917792073129915 83009662946876688109694873)
        ·
          refine ⟨62257247210157516082271155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83009662946876688109694873 62257247210157516082271155)
          ·
            refine ⟨93385870815236274123406733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62257247210157516082271155 93385870815236274123406733)
            ·
              refine ⟨35019701555713602796277525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93385870815236274123406733 35019701555713602796277525)
              ·
                refine ⟨1641548510424075131075509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35019701555713602796277525 1641548510424075131075509)
                ·
                  refine ⟨153895172852257043538329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641548510424075131075509 153895172852257043538329)
                  ·
                    rfl

theorem cell21_674347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_674347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674347 prefixEnd_674347 := by exact prefixLift 674347
  have htrace : WordTrace (prefixWord ++ tailWord_674347) baseStart_674347 baseEnd_674347 := by
    simpa [prefixWord, tailWord_674347, baseEnd_674347] using wordTrace_append hprefix tailTrace_674347
  have hstable : (prefixWord ++ tailWord_674347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674347).length < 2 ^ (prefixWord ++ tailWord_674347).sum := by decide
  have hdescent : baseEnd_674347 < baseStart_674347 := by decide
  rcases family_descends (prefixWord ++ tailWord_674347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674429 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 4]
def baseStart_674429 : Nat := 118140960795 + 674429 * 2 ^ 59
def prefixEnd_674429 : Nat := 4983230072969 + 3 ^ 40 * 674429 * 2
def baseEnd_674429 : Nat := 153913886369443123171495

theorem tailTrace_674429 : CollatzResearch.WordTrace tailWord_674429 prefixEnd_674429 153913886369443123171495 := by
  unfold tailWord_674429
  simp only [CollatzResearch.WordTrace]
  refine ⟨24598446473666391148098341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16398964315777594098732227 24598446473666391148098341)
  ·
    refine ⟨4612208713812448340268439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24598446473666391148098341 4612208713812448340268439)
    ·
      refine ⟨6918313070718672510402659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4612208713812448340268439 6918313070718672510402659)
      ·
        refine ⟨10377469606078008765603989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6918313070718672510402659 10377469606078008765603989)
        ·
          refine ⟨486443887784906660887687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10377469606078008765603989 486443887784906660887687)
          ·
            refine ⟨729665831677359991331531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486443887784906660887687 729665831677359991331531)
            ·
              refine ⟨1094498747516039986997297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729665831677359991331531 1094498747516039986997297)
              ·
                refine ⟨820874060637029990247973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094498747516039986997297 820874060637029990247973)
                ·
                  refine ⟨153913886369443123171495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820874060637029990247973 153913886369443123171495)
                  ·
                    rfl

theorem cell21_674429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_674429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674429 prefixEnd_674429 := by exact prefixLift 674429
  have htrace : WordTrace (prefixWord ++ tailWord_674429) baseStart_674429 baseEnd_674429 := by
    simpa [prefixWord, tailWord_674429, baseEnd_674429] using wordTrace_append hprefix tailTrace_674429
  have hstable : (prefixWord ++ tailWord_674429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674429).length < 2 ^ (prefixWord ++ tailWord_674429).sum := by decide
  have hdescent : baseEnd_674429 < baseStart_674429 := by decide
  rcases family_descends (prefixWord ++ tailWord_674429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674485 : List Nat := [1, 3, 3, 3, 1, 1, 9]
def baseStart_674485 : Nat := 118140960795 + 674485 * 2 ^ 59
def prefixEnd_674485 : Nat := 4983230072969 + 3 ^ 40 * 674485 * 2
def baseEnd_674485 : Nat := 17102962925822163359783

theorem tailTrace_674485 : CollatzResearch.WordTrace tailWord_674485 prefixEnd_674485 17102962925822163359783 := by
  unfold tailWord_674485
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600488961463512712136909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16400325974309008474757939 24600488961463512712136909)
  ·
    refine ⟨9225183360548817267051341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24600488961463512712136909 9225183360548817267051341)
    ·
      refine ⟨3459443760205806475144253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9225183360548817267051341 3459443760205806475144253)
      ·
        refine ⟨1297291410077177428179095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3459443760205806475144253 1297291410077177428179095)
        ·
          refine ⟨1945937115115766142268643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297291410077177428179095 1945937115115766142268643)
          ·
            refine ⟨2918905672673649213402965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945937115115766142268643 2918905672673649213402965)
            ·
              refine ⟨17102962925822163359783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2918905672673649213402965 17102962925822163359783)
              ·
                rfl

theorem cell21_674485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 9].length) (baseStart_674485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674485 prefixEnd_674485 := by exact prefixLift 674485
  have htrace : WordTrace (prefixWord ++ tailWord_674485) baseStart_674485 baseEnd_674485 := by
    simpa [prefixWord, tailWord_674485, baseEnd_674485] using wordTrace_append hprefix tailTrace_674485
  have hstable : (prefixWord ++ tailWord_674485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674485).length < 2 ^ (prefixWord ++ tailWord_674485).sum := by decide
  have hdescent : baseEnd_674485 < baseStart_674485 := by decide
  rcases family_descends (prefixWord ++ tailWord_674485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674575 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_674575 : Nat := 118140960795 + 674575 * 2 ^ 59
def prefixEnd_674575 : Nat := 4983230072969 + 3 ^ 40 * 674575 * 2
def baseEnd_674575 : Nat := 153947205558579313737863

theorem tailTrace_674575 : CollatzResearch.WordTrace tailWord_674575 prefixEnd_674575 153947205558579313737863 := by
  unfold tailWord_674575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24603771531137458082913179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16402514354091638721942119 24603771531137458082913179)
  ·
    refine ⟨36905657296706187124369769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24603771531137458082913179 36905657296706187124369769)
    ·
      refine ⟨27679242972529640343277327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36905657296706187124369769 27679242972529640343277327)
      ·
        refine ⟨41518864458794460514915991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27679242972529640343277327 41518864458794460514915991)
        ·
          refine ⟨62278296688191690772373987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41518864458794460514915991 62278296688191690772373987)
          ·
            refine ⟨93417445032287536158560981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62278296688191690772373987 93417445032287536158560981)
            ·
              refine ⟨2189471367944239128716273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93417445032287536158560981 2189471367944239128716273)
              ·
                refine ⟨1642103525958179346537205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189471367944239128716273 1642103525958179346537205)
                ·
                  refine ⟨153947205558579313737863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1642103525958179346537205 153947205558579313737863)
                  ·
                    rfl

theorem cell21_674575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_674575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674575 prefixEnd_674575 := by exact prefixLift 674575
  have htrace : WordTrace (prefixWord ++ tailWord_674575) baseStart_674575 baseEnd_674575 := by
    simpa [prefixWord, tailWord_674575, baseEnd_674575] using wordTrace_append hprefix tailTrace_674575
  have hstable : (prefixWord ++ tailWord_674575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674575).length < 2 ^ (prefixWord ++ tailWord_674575).sum := by decide
  have hdescent : baseEnd_674575 < baseStart_674575 := by decide
  rcases family_descends (prefixWord ++ tailWord_674575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674620 : List Nat := [2, 2, 2, 2, 1, 1, 1, 10]
def baseStart_674620 : Nat := 118140960795 + 674620 * 2 ^ 59
def prefixEnd_674620 : Nat := 4983230072969 + 3 ^ 40 * 674620 * 2
def baseEnd_674620 : Nat := 51319158390556411829257

theorem tailTrace_674620 : CollatzResearch.WordTrace tailWord_674620 prefixEnd_674620 51319158390556411829257 := by
  unfold tailWord_674620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302706407987215384150657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16403608543982953845534209 12302706407987215384150657)
  ·
    refine ⟨9227029805990411538112993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12302706407987215384150657 9227029805990411538112993)
    ·
      refine ⟨6920272354492808653584745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9227029805990411538112993 6920272354492808653584745)
      ·
        refine ⟨5190204265869606490188559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6920272354492808653584745 5190204265869606490188559)
        ·
          refine ⟨7785306398804409735282839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190204265869606490188559 7785306398804409735282839)
          ·
            refine ⟨11677959598206614602924259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785306398804409735282839 11677959598206614602924259)
            ·
              refine ⟨17516939397309921904386389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11677959598206614602924259 17516939397309921904386389)
              ·
                refine ⟨51319158390556411829257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17516939397309921904386389 51319158390556411829257)
                ·
                  rfl

theorem cell21_674620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_674620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674620 prefixEnd_674620 := by exact prefixLift 674620
  have htrace : WordTrace (prefixWord ++ tailWord_674620) baseStart_674620 baseEnd_674620 := by
    simpa [prefixWord, tailWord_674620, baseEnd_674620] using wordTrace_append hprefix tailTrace_674620
  have hstable : (prefixWord ++ tailWord_674620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674620).length < 2 ^ (prefixWord ++ tailWord_674620).sum := by decide
  have hdescent : baseEnd_674620 < baseStart_674620 := by decide
  rcases family_descends (prefixWord ++ tailWord_674620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674716 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_674716 : Nat := 118140960795 + 674716 * 2 ^ 59
def prefixEnd_674716 : Nat := 4983230072969 + 3 ^ 40 * 674716 * 2
def baseEnd_674716 : Nat := 153979383679594401887575

theorem tailTrace_674716 : CollatzResearch.WordTrace tailWord_674716 prefixEnd_674716 153979383679594401887575 := by
  unfold tailWord_674716
  simp only [CollatzResearch.WordTrace]
  refine ⟨12304457111813319581898001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16405942815751092775864001 12304457111813319581898001)
  ·
    refine ⟨9228342833859989686423501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12304457111813319581898001 9228342833859989686423501)
    ·
      refine ⟨3460628562697496132408813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9228342833859989686423501 3460628562697496132408813)
      ·
        refine ⟨1297735711011561049653305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3460628562697496132408813 1297735711011561049653305)
        ·
          refine ⟨973301783258670787239979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297735711011561049653305 973301783258670787239979)
          ·
            refine ⟨1459952674888006180859969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973301783258670787239979 1459952674888006180859969)
            ·
              refine ⟨1094964506166004635644977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459952674888006180859969 1094964506166004635644977)
              ·
                refine ⟨821223379624503476733733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094964506166004635644977 821223379624503476733733)
                ·
                  refine ⟨153979383679594401887575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821223379624503476733733 153979383679594401887575)
                  ·
                    rfl

theorem cell21_674716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_674716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674716 prefixEnd_674716 := by exact prefixLift 674716
  have htrace : WordTrace (prefixWord ++ tailWord_674716) baseStart_674716 baseEnd_674716 := by
    simpa [prefixWord, tailWord_674716, baseEnd_674716] using wordTrace_append hprefix tailTrace_674716
  have hstable : (prefixWord ++ tailWord_674716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674716).length < 2 ^ (prefixWord ++ tailWord_674716).sum := by decide
  have hdescent : baseEnd_674716 < baseStart_674716 := by decide
  rcases family_descends (prefixWord ++ tailWord_674716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674806 : List Nat := [5, 1, 1, 1, 3, 1, 4, 5]
def baseStart_674806 : Nat := 118140960795 + 674806 * 2 ^ 59
def prefixEnd_674806 : Nat := 4983230072969 + 3 ^ 40 * 674806 * 2
def baseEnd_674806 : Nat := 51333307635258081795797

theorem tailTrace_674806 : CollatzResearch.WordTrace tailWord_674806 prefixEnd_674806 51333307635258081795797 := by
  unfold tailWord_674806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1538262299581286533410767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16408131195533723023048181 1538262299581286533410767)
  ·
    refine ⟨2307393449371929800116151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1538262299581286533410767 2307393449371929800116151)
    ·
      refine ⟨3461090174057894700174227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2307393449371929800116151 3461090174057894700174227)
      ·
        refine ⟨5191635261086842050261341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461090174057894700174227 5191635261086842050261341)
        ·
          refine ⟨1946863222907565768848003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5191635261086842050261341 1946863222907565768848003)
          ·
            refine ⟨2920294834361348653272005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946863222907565768848003 2920294834361348653272005)
            ·
              refine ⟨547555281442752872488501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2920294834361348653272005 547555281442752872488501)
              ·
                refine ⟨51333307635258081795797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547555281442752872488501 51333307635258081795797)
                ·
                  rfl

theorem cell21_674806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_674806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674806 prefixEnd_674806 := by exact prefixLift 674806
  have htrace : WordTrace (prefixWord ++ tailWord_674806) baseStart_674806 baseEnd_674806 := by
    simpa [prefixWord, tailWord_674806, baseEnd_674806] using wordTrace_append hprefix tailTrace_674806
  have hstable : (prefixWord ++ tailWord_674806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674806).length < 2 ^ (prefixWord ++ tailWord_674806).sum := by decide
  have hdescent : baseEnd_674806 < baseStart_674806 := by decide
  rcases family_descends (prefixWord ++ tailWord_674806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674851 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 4]
def baseStart_674851 : Nat := 118140960795 + 674851 * 2 ^ 59
def prefixEnd_674851 : Nat := 4983230072969 + 3 ^ 40 * 674851 * 2
def baseEnd_674851 : Nat := 154010192518864167137299

theorem tailTrace_674851 : CollatzResearch.WordTrace tailWord_674851 prefixEnd_674851 154010192518864167137299 := by
  unfold tailWord_674851
  simp only [CollatzResearch.WordTrace]
  refine ⟨24613838078137557219960407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16409225385425038146640271 24613838078137557219960407)
  ·
    refine ⟨36920757117206335829940611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24613838078137557219960407 36920757117206335829940611)
    ·
      refine ⟨55381135675809503744910917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36920757117206335829940611 55381135675809503744910917)
      ·
        refine ⟨10383962939214281952170797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55381135675809503744910917 10383962939214281952170797)
        ·
          refine ⟨3893986102205355732064049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10383962939214281952170797 3893986102205355732064049)
          ·
            refine ⟨2920489576654016799048037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3893986102205355732064049 2920489576654016799048037)
            ·
              refine ⟨547591795622628149821507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2920489576654016799048037 547591795622628149821507)
              ·
                refine ⟨821387693433942224732261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547591795622628149821507 821387693433942224732261)
                ·
                  refine ⟨154010192518864167137299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821387693433942224732261 154010192518864167137299)
                  ·
                    rfl

theorem cell21_674851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 4].length) (baseStart_674851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674851 prefixEnd_674851 := by exact prefixLift 674851
  have htrace : WordTrace (prefixWord ++ tailWord_674851) baseStart_674851 baseEnd_674851 := by
    simpa [prefixWord, tailWord_674851, baseEnd_674851] using wordTrace_append hprefix tailTrace_674851
  have hstable : (prefixWord ++ tailWord_674851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674851).length < 2 ^ (prefixWord ++ tailWord_674851).sum := by decide
  have hdescent : baseEnd_674851 < baseStart_674851 := by decide
  rcases family_descends (prefixWord ++ tailWord_674851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674975 : List Nat := [1, 1, 2, 6, 3, 1, 2, 5]
def baseStart_674975 : Nat := 118140960795 + 674975 * 2 ^ 59
def prefixEnd_674975 : Nat := 4983230072969 + 3 ^ 40 * 674975 * 2
def baseEnd_674975 : Nat := 51346163669422502356793

theorem tailTrace_674975 : CollatzResearch.WordTrace tailWord_674975 prefixEnd_674975 51346163669422502356793 := by
  unfold tailWord_674975
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618360729688326397474379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16412240486458884264982919 24618360729688326397474379)
  ·
    refine ⟨36927541094532489596211569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24618360729688326397474379 36927541094532489596211569)
    ·
      refine ⟨27695655820899367197158677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36927541094532489596211569 27695655820899367197158677)
      ·
        refine ⟨1298233866604657837366813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27695655820899367197158677 1298233866604657837366813)
        ·
          refine ⟨486837699976746689012555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298233866604657837366813 486837699976746689012555)
          ·
            refine ⟨730256549965120033518833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486837699976746689012555 730256549965120033518833)
            ·
              refine ⟨547692412473840025139125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730256549965120033518833 547692412473840025139125)
              ·
                refine ⟨51346163669422502356793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547692412473840025139125 51346163669422502356793)
                ·
                  rfl

theorem cell21_674975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 5].length) (baseStart_674975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_674975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_674975 prefixEnd_674975 := by exact prefixLift 674975
  have htrace : WordTrace (prefixWord ++ tailWord_674975) baseStart_674975 baseEnd_674975 := by
    simpa [prefixWord, tailWord_674975, baseEnd_674975] using wordTrace_append hprefix tailTrace_674975
  have hstable : (prefixWord ++ tailWord_674975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674975).length < 2 ^ (prefixWord ++ tailWord_674975).sum := by decide
  have hdescent : baseEnd_674975 < baseStart_674975 := by decide
  rcases family_descends (prefixWord ++ tailWord_674975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675006 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_675006 : Nat := 118140960795 + 675006 * 2 ^ 59
def prefixEnd_675006 : Nat := 4983230072969 + 3 ^ 40 * 675006 * 2
def baseEnd_675006 : Nat := 154045565630618342053649

theorem tailTrace_675006 : CollatzResearch.WordTrace tailWord_675006 prefixEnd_675006 154045565630618342053649 := by
  unfold tailWord_675006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077436424072002336481609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16412994261717345794568581 3077436424072002336481609)
  ·
    refine ⟨2308077318054001752361207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3077436424072002336481609 2308077318054001752361207)
    ·
      refine ⟨3462115977081002628541811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308077318054001752361207 3462115977081002628541811)
      ·
        refine ⟨5193173965621503942812717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462115977081002628541811 5193173965621503942812717)
        ·
          refine ⟨1947440237108063978554769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5193173965621503942812717 1947440237108063978554769)
          ·
            refine ⟨1460580177831047983916077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947440237108063978554769 1460580177831047983916077)
            ·
              refine ⟨547717566686642993968529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1460580177831047983916077 547717566686642993968529)
              ·
                refine ⟨410788175014982245476397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547717566686642993968529 410788175014982245476397)
                ·
                  refine ⟨154045565630618342053649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410788175014982245476397 154045565630618342053649)
                  ·
                    rfl

theorem cell21_675006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_675006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675006 prefixEnd_675006 := by exact prefixLift 675006
  have htrace : WordTrace (prefixWord ++ tailWord_675006) baseStart_675006 baseEnd_675006 := by
    simpa [prefixWord, tailWord_675006, baseEnd_675006] using wordTrace_append hprefix tailTrace_675006
  have hstable : (prefixWord ++ tailWord_675006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675006).length < 2 ^ (prefixWord ++ tailWord_675006).sum := by decide
  have hdescent : baseEnd_675006 < baseStart_675006 := by decide
  rcases family_descends (prefixWord ++ tailWord_675006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675048 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_675048 : Nat := 118140960795 + 675048 * 2 ^ 59
def prefixEnd_675048 : Nat := 4983230072969 + 3 ^ 40 * 675048 * 2
def baseEnd_675048 : Nat := 154055150602835602353563

theorem tailTrace_675048 : CollatzResearch.WordTrace tailWord_675048 prefixEnd_675048 154055150602835602353563 := by
  unfold tailWord_675048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12310511629211929932440899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16414015505615906576587865 12310511629211929932440899)
  ·
    refine ⟨18465767443817894898661349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12310511629211929932440899 18465767443817894898661349)
    ·
      refine ⟨3462331395715855293499003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18465767443817894898661349 3462331395715855293499003)
      ·
        refine ⟨5193497093573782940248505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462331395715855293499003 5193497093573782940248505)
        ·
          refine ⟨3895122820180337205186379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5193497093573782940248505 3895122820180337205186379)
          ·
            refine ⟨5842684230270505807779569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895122820180337205186379 5842684230270505807779569)
            ·
              refine ⟨4382013172702879355834677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5842684230270505807779569 4382013172702879355834677)
              ·
                refine ⟨410813734940894939609501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4382013172702879355834677 410813734940894939609501)
                ·
                  refine ⟨154055150602835602353563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410813734940894939609501 154055150602835602353563)
                  ·
                    rfl

theorem cell21_675048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_675048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675048 prefixEnd_675048 := by exact prefixLift 675048
  have htrace : WordTrace (prefixWord ++ tailWord_675048) baseStart_675048 baseEnd_675048 := by
    simpa [prefixWord, tailWord_675048, baseEnd_675048] using wordTrace_append hprefix tailTrace_675048
  have hstable : (prefixWord ++ tailWord_675048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675048).length < 2 ^ (prefixWord ++ tailWord_675048).sum := by decide
  have hdescent : baseEnd_675048 < baseStart_675048 := by decide
  rcases family_descends (prefixWord ++ tailWord_675048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675059 : List Nat := [1, 1, 1, 2, 2, 14]
def baseStart_675059 : Nat := 118140960795 + 675059 * 2 ^ 59
def prefixEnd_675059 : Nat := 4983230072969 + 3 ^ 40 * 675059 * 2
def baseEnd_675059 : Nat := 5705839294544519543341

theorem tailTrace_675059 : CollatzResearch.WordTrace tailWord_675059 prefixEnd_675059 5705839294544519543341 := by
  unfold tailWord_675059
  simp only [CollatzResearch.WordTrace]
  refine ⟨24621424461384008743532231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16414282974256005829021487 24621424461384008743532231)
  ·
    refine ⟨36932136692076013115298347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24621424461384008743532231 36932136692076013115298347)
    ·
      refine ⟨55398205038114019672947521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36932136692076013115298347 55398205038114019672947521)
      ·
        refine ⟨41548653778585514754710641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55398205038114019672947521 41548653778585514754710641)
        ·
          refine ⟨31161490333939136066032981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41548653778585514754710641 31161490333939136066032981)
          ·
            refine ⟨5705839294544519543341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 31161490333939136066032981 5705839294544519543341)
            ·
              rfl

theorem cell21_675059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 14].length) (baseStart_675059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675059 prefixEnd_675059 := by exact prefixLift 675059
  have htrace : WordTrace (prefixWord ++ tailWord_675059) baseStart_675059 baseEnd_675059 := by
    simpa [prefixWord, tailWord_675059, baseEnd_675059] using wordTrace_append hprefix tailTrace_675059
  have hstable : (prefixWord ++ tailWord_675059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675059).length < 2 ^ (prefixWord ++ tailWord_675059).sum := by decide
  have hdescent : baseEnd_675059 < baseStart_675059 := by decide
  rcases family_descends (prefixWord ++ tailWord_675059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675124 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_675124 : Nat := 118140960795 + 675124 * 2 ^ 59
def prefixEnd_675124 : Nat := 4983230072969 + 3 ^ 40 * 675124 * 2
def baseEnd_675124 : Nat := 154072494838276359086741

theorem tailTrace_675124 : CollatzResearch.WordTrace tailWord_675124 prefixEnd_675124 154072494838276359086741 := by
  unfold tailWord_675124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12311897603074262422324213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16415863470765683229765617 12311897603074262422324213)
  ·
    refine ⟨1154240400288212102092895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12311897603074262422324213 1154240400288212102092895)
    ·
      refine ⟨1731360600432318153139343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1154240400288212102092895 1731360600432318153139343)
      ·
        refine ⟨2597040900648477229709015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731360600432318153139343 2597040900648477229709015)
        ·
          refine ⟨3895561350972715844563523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597040900648477229709015 3895561350972715844563523)
          ·
            refine ⟨5843342026459073766845285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895561350972715844563523 5843342026459073766845285)
            ·
              refine ⟨1095626629961076331283491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5843342026459073766845285 1095626629961076331283491)
              ·
                refine ⟨1643439944941614496925237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095626629961076331283491 1643439944941614496925237)
                ·
                  refine ⟨154072494838276359086741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643439944941614496925237 154072494838276359086741)
                  ·
                    rfl

theorem cell21_675124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_675124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675124 prefixEnd_675124 := by exact prefixLift 675124
  have htrace : WordTrace (prefixWord ++ tailWord_675124) baseStart_675124 baseEnd_675124 := by
    simpa [prefixWord, tailWord_675124, baseEnd_675124] using wordTrace_append hprefix tailTrace_675124
  have hstable : (prefixWord ++ tailWord_675124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675124).length < 2 ^ (prefixWord ++ tailWord_675124).sum := by decide
  have hdescent : baseEnd_675124 < baseStart_675124 := by decide
  rcases family_descends (prefixWord ++ tailWord_675124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675189 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 4]
def baseStart_675189 : Nat := 118140960795 + 675189 * 2 ^ 59
def prefixEnd_675189 : Nat := 4983230072969 + 3 ^ 40 * 675189 * 2
def baseEnd_675189 : Nat := 154087328723850690503275

theorem tailTrace_675189 : CollatzResearch.WordTrace tailWord_675189 prefixEnd_675189 154087328723850690503275 := by
  unfold tailWord_675189
  simp only [CollatzResearch.WordTrace]
  refine ⟨24626165950913040945764621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16417443967275360630509747 24626165950913040945764621)
  ·
    refine ⟨9234812231592390354661733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24626165950913040945764621 9234812231592390354661733)
    ·
      refine ⟨1731527293423573191499075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9234812231592390354661733 1731527293423573191499075)
      ·
        refine ⟨2597290940135359787248613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731527293423573191499075 2597290940135359787248613)
        ·
          refine ⟨486992051275379960109115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2597290940135359787248613 486992051275379960109115)
          ·
            refine ⟨730488076913069940163673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486992051275379960109115 730488076913069940163673)
            ·
              refine ⟨547866057684802455122755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730488076913069940163673 547866057684802455122755)
              ·
                refine ⟨821799086527203682684133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547866057684802455122755 821799086527203682684133)
                ·
                  refine ⟨154087328723850690503275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821799086527203682684133 154087328723850690503275)
                  ·
                    rfl

theorem cell21_675189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_675189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675189 prefixEnd_675189 := by exact prefixLift 675189
  have htrace : WordTrace (prefixWord ++ tailWord_675189) baseStart_675189 baseEnd_675189 := by
    simpa [prefixWord, tailWord_675189, baseEnd_675189] using wordTrace_append hprefix tailTrace_675189
  have hstable : (prefixWord ++ tailWord_675189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675189).length < 2 ^ (prefixWord ++ tailWord_675189).sum := by decide
  have hdescent : baseEnd_675189 < baseStart_675189 := by decide
  rcases family_descends (prefixWord ++ tailWord_675189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675211 : List Nat := [1, 1, 1, 1, 4, 3, 1, 9]
def baseStart_675211 : Nat := 118140960795 + 675211 * 2 ^ 59
def prefixEnd_675211 : Nat := 4983230072969 + 3 ^ 40 * 675211 * 2
def baseEnd_675211 : Nat := 51364116474527847045521

theorem tailTrace_675211 : CollatzResearch.WordTrace tailWord_675211 prefixEnd_675211 51364116474527847045521 := by
  unfold tailWord_675211
  simp only [CollatzResearch.WordTrace]
  refine ⟨24626968356833338703065487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16417978904555559135376991 24626968356833338703065487)
  ·
    refine ⟨36940452535250008054598231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24626968356833338703065487 36940452535250008054598231)
    ·
      refine ⟨55410678802875012081897347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36940452535250008054598231 55410678802875012081897347)
      ·
        refine ⟨83116018204312518122846021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55410678802875012081897347 83116018204312518122846021)
        ·
          refine ⟨15584253413308597148033629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83116018204312518122846021 15584253413308597148033629)
          ·
            refine ⟨5844095029990723930512611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15584253413308597148033629 5844095029990723930512611)
            ·
              refine ⟨8766142544986085895768917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844095029990723930512611 8766142544986085895768917)
              ·
                refine ⟨51364116474527847045521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8766142544986085895768917 51364116474527847045521)
                ·
                  rfl

theorem cell21_675211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_675211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675211 prefixEnd_675211 := by exact prefixLift 675211
  have htrace : WordTrace (prefixWord ++ tailWord_675211) baseStart_675211 baseEnd_675211 := by
    simpa [prefixWord, tailWord_675211, baseEnd_675211] using wordTrace_append hprefix tailTrace_675211
  have hstable : (prefixWord ++ tailWord_675211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675211).length < 2 ^ (prefixWord ++ tailWord_675211).sum := by decide
  have hdescent : baseEnd_675211 < baseStart_675211 := by decide
  rcases family_descends (prefixWord ++ tailWord_675211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675228 : List Nat := [2, 2, 3, 4, 10]
def baseStart_675228 : Nat := 118140960795 + 675228 * 2 ^ 59
def prefixEnd_675228 : Nat := 4983230072969 + 3 ^ 40 * 675228 * 2
def baseEnd_675228 : Nat := 1902422580928336905595

theorem tailTrace_675228 : CollatzResearch.WordTrace tailWord_675228 prefixEnd_675228 1902422580928336905595 := by
  unfold tailWord_675228
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313794198885875303217169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16418392265181167070956225 12313794198885875303217169)
  ·
    refine ⟨9235345649164406477412877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12313794198885875303217169 9235345649164406477412877)
    ·
      refine ⟨3463254618436652429029829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9235345649164406477412877 3463254618436652429029829)
      ·
        refine ⟨649360240956872330443093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3463254618436652429029829 649360240956872330443093)
        ·
          refine ⟨1902422580928336905595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 649360240956872330443093 1902422580928336905595)
          ·
            rfl

theorem cell21_675228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 10].length) (baseStart_675228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675228 prefixEnd_675228 := by exact prefixLift 675228
  have htrace : WordTrace (prefixWord ++ tailWord_675228) baseStart_675228 baseEnd_675228 := by
    simpa [prefixWord, tailWord_675228, baseEnd_675228] using wordTrace_append hprefix tailTrace_675228
  have hstable : (prefixWord ++ tailWord_675228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675228).length < 2 ^ (prefixWord ++ tailWord_675228).sum := by decide
  have hdescent : baseEnd_675228 < baseStart_675228 := by decide
  rcases family_descends (prefixWord ++ tailWord_675228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675234 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_675234 : Nat := 118140960795 + 675234 * 2 ^ 59
def prefixEnd_675234 : Nat := 4983230072969 + 3 ^ 40 * 675234 * 2
def baseEnd_675234 : Nat := 154097598336940612253183

theorem tailTrace_675234 : CollatzResearch.WordTrace tailWord_675234 prefixEnd_675234 154097598336940612253183 := by
  unfold tailWord_675234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156951808937503407788189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16418538157166675754101837 6156951808937503407788189)
  ·
    refine ⟨2308856928351563777920571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6156951808937503407788189 2308856928351563777920571)
    ·
      refine ⟨3463285392527345666880857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308856928351563777920571 3463285392527345666880857)
      ·
        refine ⟨2597464044395509250160643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3463285392527345666880857 2597464044395509250160643)
        ·
          refine ⟨3896196066593263875240965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597464044395509250160643 3896196066593263875240965)
          ·
            refine ⟨730536762486236976607681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3896196066593263875240965 730536762486236976607681)
            ·
              refine ⟨547902571864677732455761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730536762486236976607681 547902571864677732455761)
              ·
                refine ⟨410926928898508299341821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547902571864677732455761 410926928898508299341821)
                ·
                  refine ⟨154097598336940612253183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410926928898508299341821 154097598336940612253183)
                  ·
                    rfl

theorem cell21_675234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_675234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675234 prefixEnd_675234 := by exact prefixLift 675234
  have htrace : WordTrace (prefixWord ++ tailWord_675234) baseStart_675234 baseEnd_675234 := by
    simpa [prefixWord, tailWord_675234, baseEnd_675234] using wordTrace_append hprefix tailTrace_675234
  have hstable : (prefixWord ++ tailWord_675234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675234).length < 2 ^ (prefixWord ++ tailWord_675234).sum := by decide
  have hdescent : baseEnd_675234 < baseStart_675234 := by decide
  rcases family_descends (prefixWord ++ tailWord_675234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675245 : List Nat := [1, 5, 2, 2, 1, 1, 3, 6]
def baseStart_675245 : Nat := 118140960795 + 675245 * 2 ^ 59
def prefixEnd_675245 : Nat := 4983230072969 + 3 ^ 40 * 675245 * 2
def baseEnd_675245 : Nat := 51366702895602345856609

theorem tailTrace_675245 : CollatzResearch.WordTrace tailWord_675245 prefixEnd_675245 51366702895602345856609 := by
  unfold tailWord_675245
  simp only [CollatzResearch.WordTrace]
  refine ⟨24628208438710162509803189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16418805625806775006535459 24628208438710162509803189)
  ·
    refine ⟨2308894541129077735294049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24628208438710162509803189 2308894541129077735294049)
    ·
      refine ⟨1731670905846808301470537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2308894541129077735294049 1731670905846808301470537)
      ·
        refine ⟨1298753179385106226102903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731670905846808301470537 1298753179385106226102903)
        ·
          refine ⟨1948129769077659339154355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298753179385106226102903 1948129769077659339154355)
          ·
            refine ⟨2922194653616489008731533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948129769077659339154355 2922194653616489008731533)
            ·
              refine ⟨1095822995106183378274325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2922194653616489008731533 1095822995106183378274325)
              ·
                refine ⟨51366702895602345856609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1095822995106183378274325 51366702895602345856609)
                ·
                  rfl

theorem cell21_675245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 6].length) (baseStart_675245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675245 prefixEnd_675245 := by exact prefixLift 675245
  have htrace : WordTrace (prefixWord ++ tailWord_675245) baseStart_675245 baseEnd_675245 := by
    simpa [prefixWord, tailWord_675245, baseEnd_675245] using wordTrace_append hprefix tailTrace_675245
  have hstable : (prefixWord ++ tailWord_675245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675245).length < 2 ^ (prefixWord ++ tailWord_675245).sum := by decide
  have hdescent : baseEnd_675245 < baseStart_675245 := by decide
  rcases family_descends (prefixWord ++ tailWord_675245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675276 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_675276 : Nat := 118140960795 + 675276 * 2 ^ 59
def prefixEnd_675276 : Nat := 4983230072969 + 3 ^ 40 * 675276 * 2
def baseEnd_675276 : Nat := 154107183309157872553097

theorem tailTrace_675276 : CollatzResearch.WordTrace tailWord_675276 prefixEnd_675276 154107183309157872553097 := by
  unfold tailWord_675276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314669550798927402090841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16419559401065236536121121 12314669550798927402090841)
  ·
    refine ⟨9236002163099195551568131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12314669550798927402090841 9236002163099195551568131)
    ·
      refine ⟨13854003244648793327352197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9236002163099195551568131 13854003244648793327352197)
      ·
        refine ⟨2597625608371648748878537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13854003244648793327352197 2597625608371648748878537)
        ·
          refine ⟨1948219206278736561658903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2597625608371648748878537 1948219206278736561658903)
          ·
            refine ⟨2922328809418104842488355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948219206278736561658903 2922328809418104842488355)
            ·
              refine ⟨4383493214127157263732533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2922328809418104842488355 4383493214127157263732533)
              ·
                refine ⟨410952488824420993474925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4383493214127157263732533 410952488824420993474925)
                ·
                  refine ⟨154107183309157872553097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410952488824420993474925 154107183309157872553097)
                  ·
                    rfl

theorem cell21_675276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_675276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675276 prefixEnd_675276 := by exact prefixLift 675276
  have htrace : WordTrace (prefixWord ++ tailWord_675276) baseStart_675276 baseEnd_675276 := by
    simpa [prefixWord, tailWord_675276, baseEnd_675276] using wordTrace_append hprefix tailTrace_675276
  have hstable : (prefixWord ++ tailWord_675276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675276).length < 2 ^ (prefixWord ++ tailWord_675276).sum := by decide
  have hdescent : baseEnd_675276 < baseStart_675276 := by decide
  rcases family_descends (prefixWord ++ tailWord_675276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675290 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_675290 : Nat := 118140960795 + 675290 * 2 ^ 59
def prefixEnd_675290 : Nat := 4983230072969 + 3 ^ 40 * 675290 * 2
def baseEnd_675290 : Nat := 154110378299896959319735

theorem tailTrace_675290 : CollatzResearch.WordTrace tailWord_675290 prefixEnd_675290 154110378299896959319735 := by
  unfold tailWord_675290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6157462430886783798797831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16419899815698090130127549 6157462430886783798797831)
  ·
    refine ⟨9236193646330175698196747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6157462430886783798797831 9236193646330175698196747)
    ·
      refine ⟨13854290469495263547295121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9236193646330175698196747 13854290469495263547295121)
      ·
        refine ⟨10390717852121447660471341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13854290469495263547295121 10390717852121447660471341)
        ·
          refine ⟨3896519194545542872676753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10390717852121447660471341 3896519194545542872676753)
          ·
            refine ⟨2922389395909157154507565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3896519194545542872676753 2922389395909157154507565)
            ·
              refine ⟨1095896023465933932940337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2922389395909157154507565 1095896023465933932940337)
              ·
                refine ⟨821922017599450449705253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095896023465933932940337 821922017599450449705253)
                ·
                  refine ⟨154110378299896959319735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821922017599450449705253 154110378299896959319735)
                  ·
                    rfl

theorem cell21_675290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_675290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675290 prefixEnd_675290 := by exact prefixLift 675290
  have htrace : WordTrace (prefixWord ++ tailWord_675290) baseStart_675290 baseEnd_675290 := by
    simpa [prefixWord, tailWord_675290, baseEnd_675290] using wordTrace_append hprefix tailTrace_675290
  have hstable : (prefixWord ++ tailWord_675290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675290).length < 2 ^ (prefixWord ++ tailWord_675290).sum := by decide
  have hdescent : baseEnd_675290 < baseStart_675290 := by decide
  rcases family_descends (prefixWord ++ tailWord_675290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675349 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_675349 : Nat := 118140960795 + 675349 * 2 ^ 59
def prefixEnd_675349 : Nat := 4983230072969 + 3 ^ 40 * 675349 * 2
def baseEnd_675349 : Nat := 154123842903725967836281

theorem tailTrace_675349 : CollatzResearch.WordTrace tailWord_675349 prefixEnd_675349 154123842903725967836281 := by
  unfold tailWord_675349
  simp only [CollatzResearch.WordTrace]
  refine ⟨24632001630333388271589101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16421334420222258847726067 24632001630333388271589101)
  ·
    refine ⟨9237000611375020601845913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24632001630333388271589101 9237000611375020601845913)
    ·
      refine ⟨6927750458531265451384435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9237000611375020601845913 6927750458531265451384435)
      ·
        refine ⟨10391625687796898177076653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927750458531265451384435 10391625687796898177076653)
        ·
          refine ⟨3896859632923836816403745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10391625687796898177076653 3896859632923836816403745)
          ·
            refine ⟨2922644724692877612302809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3896859632923836816403745 2922644724692877612302809)
            ·
              refine ⟨2191983543519658209227107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922644724692877612302809 2191983543519658209227107)
              ·
                refine ⟨3287975315279487313840661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191983543519658209227107 3287975315279487313840661)
                ·
                  refine ⟨154123842903725967836281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3287975315279487313840661 154123842903725967836281)
                  ·
                    rfl

theorem cell21_675349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_675349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675349 prefixEnd_675349 := by exact prefixLift 675349
  have htrace : WordTrace (prefixWord ++ tailWord_675349) baseStart_675349 baseEnd_675349 := by
    simpa [prefixWord, tailWord_675349, baseEnd_675349] using wordTrace_append hprefix tailTrace_675349
  have hstable : (prefixWord ++ tailWord_675349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675349).length < 2 ^ (prefixWord ++ tailWord_675349).sum := by decide
  have hdescent : baseEnd_675349 < baseStart_675349 := by decide
  rcases family_descends (prefixWord ++ tailWord_675349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675352 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_675352 : Nat := 118140960795 + 675352 * 2 ^ 59
def prefixEnd_675352 : Nat := 4983230072969 + 3 ^ 40 * 675352 * 2
def baseEnd_675352 : Nat := 154124527544598629286275

theorem tailTrace_675352 : CollatzResearch.WordTrace tailWord_675352 prefixEnd_675352 154124527544598629286275 := by
  unfold tailWord_675352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316055524661259891974155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16421407366215013189298873 12316055524661259891974155)
  ·
    refine ⟨18474083286991889837961233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316055524661259891974155 18474083286991889837961233)
    ·
      refine ⟨13855562465243917378470925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18474083286991889837961233 13855562465243917378470925)
      ·
        refine ⟨5195835924466469016926597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13855562465243917378470925 5195835924466469016926597)
        ·
          refine ⟨974219235837462940673737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5195835924466469016926597 974219235837462940673737)
          ·
            refine ⟨730664426878097205505303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974219235837462940673737 730664426878097205505303)
            ·
              refine ⟨1095996640317145808257955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730664426878097205505303 1095996640317145808257955)
              ·
                refine ⟨1643994960475718712386933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095996640317145808257955 1643994960475718712386933)
                ·
                  refine ⟨154124527544598629286275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643994960475718712386933 154124527544598629286275)
                  ·
                    rfl

theorem cell21_675352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_675352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675352 prefixEnd_675352 := by exact prefixLift 675352
  have htrace : WordTrace (prefixWord ++ tailWord_675352) baseStart_675352 baseEnd_675352 := by
    simpa [prefixWord, tailWord_675352, baseEnd_675352] using wordTrace_append hprefix tailTrace_675352
  have hstable : (prefixWord ++ tailWord_675352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675352).length < 2 ^ (prefixWord ++ tailWord_675352).sum := by decide
  have hdescent : baseEnd_675352 < baseStart_675352 := by decide
  rcases family_descends (prefixWord ++ tailWord_675352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675425 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 4]
def baseStart_675425 : Nat := 118140960795 + 675425 * 2 ^ 59
def prefixEnd_675425 : Nat := 4983230072969 + 3 ^ 40 * 675425 * 2
def baseEnd_675425 : Nat := 154141187139166724569459

theorem tailTrace_675425 : CollatzResearch.WordTrace tailWord_675425 prefixEnd_675425 154141187139166724569459 := by
  unfold tailWord_675425
  simp only [CollatzResearch.WordTrace]
  refine ⟨24634773578058053251355729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16423182385372035500903819 24634773578058053251355729)
  ·
    refine ⟨18476080183543539938516797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24634773578058053251355729 18476080183543539938516797)
    ·
      refine ⟨6928530068828827476943799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18476080183543539938516797 6928530068828827476943799)
      ·
        refine ⟨10392795103243241215415699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928530068828827476943799 10392795103243241215415699)
        ·
          refine ⟨15589192654864861823123549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10392795103243241215415699 15589192654864861823123549)
          ·
            refine ⟨5845947245574323183671331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15589192654864861823123549 5845947245574323183671331)
            ·
              refine ⟨8768920868361484775506997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845947245574323183671331 8768920868361484775506997)
              ·
                refine ⟨822086331408889197703781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8768920868361484775506997 822086331408889197703781)
                ·
                  refine ⟨154141187139166724569459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822086331408889197703781 154141187139166724569459)
                  ·
                    rfl

theorem cell21_675425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_675425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675425 prefixEnd_675425 := by exact prefixLift 675425
  have htrace : WordTrace (prefixWord ++ tailWord_675425) baseStart_675425 baseEnd_675425 := by
    simpa [prefixWord, tailWord_675425, baseEnd_675425] using wordTrace_append hprefix tailTrace_675425
  have hstable : (prefixWord ++ tailWord_675425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675425).length < 2 ^ (prefixWord ++ tailWord_675425).sum := by decide
  have hdescent : baseEnd_675425 < baseStart_675425 := by decide
  rcases family_descends (prefixWord ++ tailWord_675425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675445 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 3]
def baseStart_675445 : Nat := 118140960795 + 675445 * 2 ^ 59
def prefixEnd_675445 : Nat := 4983230072969 + 3 ^ 40 * 675445 * 2
def baseEnd_675445 : Nat := 154145751411651134236085

theorem tailTrace_675445 : CollatzResearch.WordTrace tailWord_675445 prefixEnd_675445 154145751411651134236085 := by
  unfold tailWord_675445
  simp only [CollatzResearch.WordTrace]
  refine ⟨24635503037985596667083789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16423668691990397778055859 24635503037985596667083789)
  ·
    refine ⟨9238313639244598750156421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24635503037985596667083789 9238313639244598750156421)
    ·
      refine ⟨1732183807358362265654329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9238313639244598750156421 1732183807358362265654329)
      ·
        refine ⟨1299137855518771699240747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1732183807358362265654329 1299137855518771699240747)
        ·
          refine ⟨1948706783278157548861121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299137855518771699240747 1948706783278157548861121)
          ·
            refine ⟨1461530087458618161645841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948706783278157548861121 1461530087458618161645841)
            ·
              refine ⟨1096147565593963621234381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461530087458618161645841 1096147565593963621234381)
              ·
                refine ⟨411055337097736357962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096147565593963621234381 411055337097736357962893)
                ·
                  refine ⟨154145751411651134236085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411055337097736357962893 154145751411651134236085)
                  ·
                    rfl

theorem cell21_675445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_675445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675445 prefixEnd_675445 := by exact prefixLift 675445
  have htrace : WordTrace (prefixWord ++ tailWord_675445) baseStart_675445 baseEnd_675445 := by
    simpa [prefixWord, tailWord_675445, baseEnd_675445] using wordTrace_append hprefix tailTrace_675445
  have hstable : (prefixWord ++ tailWord_675445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675445).length < 2 ^ (prefixWord ++ tailWord_675445).sum := by decide
  have hdescent : baseEnd_675445 < baseStart_675445 := by decide
  rcases family_descends (prefixWord ++ tailWord_675445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675476 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_675476 : Nat := 118140960795 + 675476 * 2 ^ 59
def prefixEnd_675476 : Nat := 4983230072969 + 3 ^ 40 * 675476 * 2
def baseEnd_675476 : Nat := 154152826034001969219355

theorem tailTrace_675476 : CollatzResearch.WordTrace tailWord_675476 prefixEnd_675476 154152826034001969219355 := by
  unfold tailWord_675476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318316850436644480731141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16424422467248859307641521 12318316850436644480731141)
  ·
    refine ⟨2309684409456870840137089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12318316850436644480731141 2309684409456870840137089)
    ·
      refine ⟨1732263307092653130102817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2309684409456870840137089 1732263307092653130102817)
      ·
        refine ⟨1299197480319489847577113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1732263307092653130102817 1299197480319489847577113)
        ·
          refine ⟨974398110239617385682835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1299197480319489847577113 974398110239617385682835)
          ·
            refine ⟨1461597165359426078524253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974398110239617385682835 1461597165359426078524253)
            ·
              refine ⟨548098937009784779446595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1461597165359426078524253 548098937009784779446595)
              ·
                refine ⟨822148405514677169169893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548098937009784779446595 822148405514677169169893)
                ·
                  refine ⟨154152826034001969219355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822148405514677169169893 154152826034001969219355)
                  ·
                    rfl

theorem cell21_675476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_675476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675476 prefixEnd_675476 := by exact prefixLift 675476
  have htrace : WordTrace (prefixWord ++ tailWord_675476) baseStart_675476 baseEnd_675476 := by
    simpa [prefixWord, tailWord_675476, baseEnd_675476] using wordTrace_append hprefix tailTrace_675476
  have hstable : (prefixWord ++ tailWord_675476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675476).length < 2 ^ (prefixWord ++ tailWord_675476).sum := by decide
  have hdescent : baseEnd_675476 < baseStart_675476 := by decide
  rcases family_descends (prefixWord ++ tailWord_675476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675496 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_675496 : Nat := 118140960795 + 675496 * 2 ^ 59
def prefixEnd_675496 : Nat := 4983230072969 + 3 ^ 40 * 675496 * 2
def baseEnd_675496 : Nat := 154157390306486378885981

theorem tailTrace_675496 : CollatzResearch.WordTrace tailWord_675496 prefixEnd_675496 154157390306486378885981 := by
  unfold tailWord_675496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318681580400416188595171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16424908773867221584793561 12318681580400416188595171)
  ·
    refine ⟨18478022370600624282892757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12318681580400416188595171 18478022370600624282892757)
    ·
      refine ⟨433078649310952131630299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18478022370600624282892757 433078649310952131630299)
      ·
        refine ⟨649617973966428197445449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433078649310952131630299 649617973966428197445449)
        ·
          refine ⟨487213480474821148084087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649617973966428197445449 487213480474821148084087)
          ·
            refine ⟨730820220712231722126131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487213480474821148084087 730820220712231722126131)
            ·
              refine ⟨1096230331068347583189197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730820220712231722126131 1096230331068347583189197)
              ·
                refine ⟨411086374150630343695949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096230331068347583189197 411086374150630343695949)
                ·
                  refine ⟨154157390306486378885981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411086374150630343695949 154157390306486378885981)
                  ·
                    rfl

theorem cell21_675496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_675496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675496 prefixEnd_675496 := by exact prefixLift 675496
  have htrace : WordTrace (prefixWord ++ tailWord_675496) baseStart_675496 baseEnd_675496 := by
    simpa [prefixWord, tailWord_675496, baseEnd_675496] using wordTrace_append hprefix tailTrace_675496
  have hstable : (prefixWord ++ tailWord_675496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675496).length < 2 ^ (prefixWord ++ tailWord_675496).sum := by decide
  have hdescent : baseEnd_675496 < baseStart_675496 := by decide
  rcases family_descends (prefixWord ++ tailWord_675496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675501 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_675501 : Nat := 118140960795 + 675501 * 2 ^ 59
def prefixEnd_675501 : Nat := 4983230072969 + 3 ^ 40 * 675501 * 2
def baseEnd_675501 : Nat := 154158531374607481302637

theorem tailTrace_675501 : CollatzResearch.WordTrace tailWord_675501 prefixEnd_675501 154158531374607481302637 := by
  unfold tailWord_675501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24637545525782718231122357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16425030350521812154081571 24637545525782718231122357)
  ·
    refine ⟨2309769893042129834167721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24637545525782718231122357 2309769893042129834167721)
    ·
      refine ⟨1732327419781597375625791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2309769893042129834167721 1732327419781597375625791)
      ·
        refine ⟨2598491129672396063438687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732327419781597375625791 2598491129672396063438687)
        ·
          refine ⟨3897736694508594095158031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598491129672396063438687 3897736694508594095158031)
          ·
            refine ⟨5846605041762891142737047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897736694508594095158031 5846605041762891142737047)
            ·
              refine ⟨8769907562644336714105571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846605041762891142737047 8769907562644336714105571)
              ·
                refine ⟨13154861343966505071158357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8769907562644336714105571 13154861343966505071158357)
                ·
                  refine ⟨154158531374607481302637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13154861343966505071158357 154158531374607481302637)
                  ·
                    rfl

theorem cell21_675501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_675501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675501 prefixEnd_675501 := by exact prefixLift 675501
  have htrace : WordTrace (prefixWord ++ tailWord_675501) baseStart_675501 baseEnd_675501 := by
    simpa [prefixWord, tailWord_675501, baseEnd_675501] using wordTrace_append hprefix tailTrace_675501
  have hstable : (prefixWord ++ tailWord_675501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675501).length < 2 ^ (prefixWord ++ tailWord_675501).sum := by decide
  have hdescent : baseEnd_675501 < baseStart_675501 := by decide
  rcases family_descends (prefixWord ++ tailWord_675501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675684 : List Nat := [2, 3, 1, 1, 5, 2, 7]
def baseStart_675684 : Nat := 118140960795 + 675684 * 2 ^ 59
def prefixEnd_675684 : Nat := 4983230072969 + 3 ^ 40 * 675684 * 2
def baseEnd_675684 : Nat := 17133366051982203305807

theorem tailTrace_675684 : CollatzResearch.WordTrace tailWord_675684 prefixEnd_675684 17133366051982203305807 := by
  unfold tailWord_675684
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322110042059870242517053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16429480056079826990022737 12322110042059870242517053)
  ·
    refine ⟨4620791265772451340943895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12322110042059870242517053 4620791265772451340943895)
    ·
      refine ⟨6931186898658677011415843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620791265772451340943895 6931186898658677011415843)
      ·
        refine ⟨10396780347988015517123765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6931186898658677011415843 10396780347988015517123765)
        ·
          refine ⟨974698157623876454730353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10396780347988015517123765 974698157623876454730353)
          ·
            refine ⟨731023618217907341047765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974698157623876454730353 731023618217907341047765)
            ·
              refine ⟨17133366051982203305807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 731023618217907341047765 17133366051982203305807)
              ·
                rfl

theorem cell21_675684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 7].length) (baseStart_675684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675684 prefixEnd_675684 := by exact prefixLift 675684
  have htrace : WordTrace (prefixWord ++ tailWord_675684) baseStart_675684 baseEnd_675684 := by
    simpa [prefixWord, tailWord_675684, baseEnd_675684] using wordTrace_append hprefix tailTrace_675684
  have hstable : (prefixWord ++ tailWord_675684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675684).length < 2 ^ (prefixWord ++ tailWord_675684).sum := by decide
  have hdescent : baseEnd_675684 < baseStart_675684 := by decide
  rcases family_descends (prefixWord ++ tailWord_675684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675690 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_675690 : Nat := 118140960795 + 675690 * 2 ^ 59
def prefixEnd_675690 : Nat := 4983230072969 + 3 ^ 40 * 675690 * 2
def baseEnd_675690 : Nat := 154201663749585152652251

theorem tailTrace_675690 : CollatzResearch.WordTrace tailWord_675690 prefixEnd_675690 154201663749585152652251 := by
  unfold tailWord_675690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161109730524500877438131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16429625948065335673168349 6161109730524500877438131)
  ·
    refine ⟨9241664595786751316157197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6161109730524500877438131 9241664595786751316157197)
    ·
      refine ⟨3465624223420031743558949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9241664595786751316157197 3465624223420031743558949)
      ·
        refine ⟨649804541891255951917303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3465624223420031743558949 649804541891255951917303)
        ·
          refine ⟨974706812836883927875955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649804541891255951917303 974706812836883927875955)
          ·
            refine ⟨1462060219255325891813933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974706812836883927875955 1462060219255325891813933)
            ·
              refine ⟨548272582220747209430225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1462060219255325891813933 548272582220747209430225)
              ·
                refine ⟨411204436665560407072669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548272582220747209430225 411204436665560407072669)
                ·
                  refine ⟨154201663749585152652251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411204436665560407072669 154201663749585152652251)
                  ·
                    rfl

theorem cell21_675690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_675690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675690 prefixEnd_675690 := by exact prefixLift 675690
  have htrace : WordTrace (prefixWord ++ tailWord_675690) baseStart_675690 baseEnd_675690 := by
    simpa [prefixWord, tailWord_675690, baseEnd_675690] using wordTrace_append hprefix tailTrace_675690
  have hstable : (prefixWord ++ tailWord_675690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675690).length < 2 ^ (prefixWord ++ tailWord_675690).sum := by decide
  have hdescent : baseEnd_675690 < baseStart_675690 := by decide
  rcases family_descends (prefixWord ++ tailWord_675690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675743 : List Nat := [1, 1, 2, 5, 3, 9]
def baseStart_675743 : Nat := 118140960795 + 675743 * 2 ^ 59
def prefixEnd_675743 : Nat := 4983230072969 + 3 ^ 40 * 675743 * 2
def baseEnd_675743 : Nat := 5711620706358105121067

theorem tailTrace_675743 : CollatzResearch.WordTrace tailWord_675743 prefixEnd_675743 5711620706358105121067 := by
  unfold tailWord_675743
  simp only [CollatzResearch.WordTrace]
  refine ⟨24646371990905993561431883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16430914660603995707621255 24646371990905993561431883)
  ·
    refine ⟨36969557986358990342147825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24646371990905993561431883 36969557986358990342147825)
    ·
      refine ⟨27727168489769242756610869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36969557986358990342147825 27727168489769242756610869)
      ·
        refine ⟨2599422045915866508432269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27727168489769242756610869 2599422045915866508432269)
        ·
          refine ⟨974783267218449940662101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2599422045915866508432269 974783267218449940662101)
          ·
            refine ⟨5711620706358105121067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 974783267218449940662101 5711620706358105121067)
            ·
              rfl

theorem cell21_675743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 9].length) (baseStart_675743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675743 prefixEnd_675743 := by exact prefixLift 675743
  have htrace : WordTrace (prefixWord ++ tailWord_675743) baseStart_675743 baseEnd_675743 := by
    simpa [prefixWord, tailWord_675743, baseEnd_675743] using wordTrace_append hprefix tailTrace_675743
  have hstable : (prefixWord ++ tailWord_675743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675743).length < 2 ^ (prefixWord ++ tailWord_675743).sum := by decide
  have hdescent : baseEnd_675743 < baseStart_675743 := by decide
  rcases family_descends (prefixWord ++ tailWord_675743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675774 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_675774 : Nat := 118140960795 + 675774 * 2 ^ 59
def prefixEnd_675774 : Nat := 4983230072969 + 3 ^ 40 * 675774 * 2
def baseEnd_675774 : Nat := 154220833694019673252079

theorem tailTrace_675774 : CollatzResearch.WordTrace tailWord_675774 prefixEnd_675774 154220833694019673252079 := by
  unfold tailWord_675774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080937831724210731976297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16431668435862457237206917 3080937831724210731976297)
  ·
    refine ⟨2310703373793158048982223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3080937831724210731976297 2310703373793158048982223)
    ·
      refine ⟨3466055060689737073473335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310703373793158048982223 3466055060689737073473335)
      ·
        refine ⟨5199082591034605610210003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466055060689737073473335 5199082591034605610210003)
        ·
          refine ⟨7798623886551908415315005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199082591034605610210003 7798623886551908415315005)
          ·
            refine ⟨2924483957456965655743127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7798623886551908415315005 2924483957456965655743127)
            ·
              refine ⟨4386725936185448483614691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924483957456965655743127 4386725936185448483614691)
              ·
                refine ⟨6580088904278172725422037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386725936185448483614691 6580088904278172725422037)
                ·
                  refine ⟨154220833694019673252079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6580088904278172725422037 154220833694019673252079)
                  ·
                    rfl

theorem cell21_675774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_675774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675774 prefixEnd_675774 := by exact prefixLift 675774
  have htrace : WordTrace (prefixWord ++ tailWord_675774) baseStart_675774 baseEnd_675774 := by
    simpa [prefixWord, tailWord_675774, baseEnd_675774] using wordTrace_append hprefix tailTrace_675774
  have hstable : (prefixWord ++ tailWord_675774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675774).length < 2 ^ (prefixWord ++ tailWord_675774).sum := by decide
  have hdescent : baseEnd_675774 < baseStart_675774 := by decide
  rcases family_descends (prefixWord ++ tailWord_675774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675791 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 3]
def baseStart_675791 : Nat := 118140960795 + 675791 * 2 ^ 59
def prefixEnd_675791 : Nat := 4983230072969 + 3 ^ 40 * 675791 * 2
def baseEnd_675791 : Nat := 154224713325631421468711

theorem tailTrace_675791 : CollatzResearch.WordTrace tailWord_675791 prefixEnd_675791 154224713325631421468711 := by
  unfold tailWord_675791
  simp only [CollatzResearch.WordTrace]
  refine ⟨24648122694732097759179227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16432081796488065172786151 24648122694732097759179227)
  ·
    refine ⟨36972184042098146638768841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24648122694732097759179227 36972184042098146638768841)
    ·
      refine ⟨27729138031573609979076631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36972184042098146638768841 27729138031573609979076631)
      ·
        refine ⟨41593707047360414968614947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27729138031573609979076631 41593707047360414968614947)
        ·
          refine ⟨62390560571040622452922421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41593707047360414968614947 62390560571040622452922421)
          ·
            refine ⟨5849115053535058354961477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62390560571040622452922421 5849115053535058354961477)
            ·
              refine ⟨1096709072537823441555277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5849115053535058354961477 1096709072537823441555277)
              ·
                refine ⟨411265902201683790583229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096709072537823441555277 411265902201683790583229)
                ·
                  refine ⟨154224713325631421468711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411265902201683790583229 154224713325631421468711)
                  ·
                    rfl

theorem cell21_675791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 3].length) (baseStart_675791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675791 prefixEnd_675791 := by exact prefixLift 675791
  have htrace : WordTrace (prefixWord ++ tailWord_675791) baseStart_675791 baseEnd_675791 := by
    simpa [prefixWord, tailWord_675791, baseEnd_675791] using wordTrace_append hprefix tailTrace_675791
  have hstable : (prefixWord ++ tailWord_675791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675791).length < 2 ^ (prefixWord ++ tailWord_675791).sum := by decide
  have hdescent : baseEnd_675791 < baseStart_675791 := by decide
  rcases family_descends (prefixWord ++ tailWord_675791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675864 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_675864 : Nat := 118140960795 + 675864 * 2 ^ 59
def prefixEnd_675864 : Nat := 4983230072969 + 3 ^ 40 * 675864 * 2
def baseEnd_675864 : Nat := 154241372920199516751895

theorem tailTrace_675864 : CollatzResearch.WordTrace tailWord_675864 prefixEnd_675864 154241372920199516751895 := by
  unfold tailWord_675864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325392611733815613293323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16433856815645087484391097 12325392611733815613293323)
  ·
    refine ⟨18488088917600723419939985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12325392611733815613293323 18488088917600723419939985)
    ·
      refine ⟨13866066688200542564954989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18488088917600723419939985 13866066688200542564954989)
      ·
        refine ⟨5199775008075203461858121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13866066688200542564954989 5199775008075203461858121)
        ·
          refine ⟨3899831256056402596393591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5199775008075203461858121 3899831256056402596393591)
          ·
            refine ⟨5849746884084603894590387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899831256056402596393591 5849746884084603894590387)
            ·
              refine ⟨8774620326126905841885581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849746884084603894590387 8774620326126905841885581)
              ·
                refine ⟨3290482622297589690707093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8774620326126905841885581 3290482622297589690707093)
                ·
                  refine ⟨154241372920199516751895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3290482622297589690707093 154241372920199516751895)
                  ·
                    rfl

theorem cell21_675864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_675864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_675864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_675864 prefixEnd_675864 := by exact prefixLift 675864
  have htrace : WordTrace (prefixWord ++ tailWord_675864) baseStart_675864 baseEnd_675864 := by
    simpa [prefixWord, tailWord_675864, baseEnd_675864] using wordTrace_append hprefix tailTrace_675864
  have hstable : (prefixWord ++ tailWord_675864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675864).length < 2 ^ (prefixWord ++ tailWord_675864).sum := by decide
  have hdescent : baseEnd_675864 < baseStart_675864 := by decide
  rcases family_descends (prefixWord ++ tailWord_675864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676050 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_676050 : Nat := 118140960795 + 676050 * 2 ^ 59
def prefixEnd_676050 : Nat := 4983230072969 + 3 ^ 40 * 676050 * 2
def baseEnd_676050 : Nat := 154283820654304526651515

theorem tailTrace_676050 : CollatzResearch.WordTrace tailWord_676050 prefixEnd_676050 154283820654304526651515 := by
  unfold tailWord_676050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164392300198446248214401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16438379467195856661905069 6164392300198446248214401)
  ·
    refine ⟨4623294225148834686160801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6164392300198446248214401 4623294225148834686160801)
    ·
      refine ⟨3467470668861626014620601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4623294225148834686160801 3467470668861626014620601)
      ·
        refine ⟨2600603001646219510965451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3467470668861626014620601 2600603001646219510965451)
        ·
          refine ⟨3900904502469329266448177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600603001646219510965451 3900904502469329266448177)
          ·
            refine ⟨2925678376851996949836133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3900904502469329266448177 2925678376851996949836133)
            ·
              refine ⟨548564695659749428094275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2925678376851996949836133 548564695659749428094275)
              ·
                refine ⟨822847043489624142141413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548564695659749428094275 822847043489624142141413)
                ·
                  refine ⟨154283820654304526651515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822847043489624142141413 154283820654304526651515)
                  ·
                    rfl

theorem cell21_676050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_676050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676050 prefixEnd_676050 := by exact prefixLift 676050
  have htrace : WordTrace (prefixWord ++ tailWord_676050) baseStart_676050 baseEnd_676050 := by
    simpa [prefixWord, tailWord_676050, baseEnd_676050] using wordTrace_append hprefix tailTrace_676050
  have hstable : (prefixWord ++ tailWord_676050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676050).length < 2 ^ (prefixWord ++ tailWord_676050).sum := by decide
  have hdescent : baseEnd_676050 < baseStart_676050 := by decide
  rcases family_descends (prefixWord ++ tailWord_676050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676154 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_676154 : Nat := 118140960795 + 676154 * 2 ^ 59
def prefixEnd_676154 : Nat := 4983230072969 + 3 ^ 40 * 676154 * 2
def baseEnd_676154 : Nat := 154307554871223456917969

theorem tailTrace_676154 : CollatzResearch.WordTrace tailWord_676154 prefixEnd_676154 154307554871223456917969 := by
  unfold tailWord_676154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165340598104252688660879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16440908261611340503095677 6165340598104252688660879)
  ·
    refine ⟨9248010897156379032991319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6165340598104252688660879 9248010897156379032991319)
    ·
      refine ⟨13872016345734568549486979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9248010897156379032991319 13872016345734568549486979)
      ·
        refine ⟨20808024518601852824230469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13872016345734568549486979 20808024518601852824230469)
        ·
          refine ⟨3901504597237847404543213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20808024518601852824230469 3901504597237847404543213)
          ·
            refine ⟨1463064223964192776703705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3901504597237847404543213 1463064223964192776703705)
            ·
              refine ⟨1097298167973144582527779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463064223964192776703705 1097298167973144582527779)
              ·
                refine ⟨1645947251959716873791669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097298167973144582527779 1645947251959716873791669)
                ·
                  refine ⟨154307554871223456917969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645947251959716873791669 154307554871223456917969)
                  ·
                    rfl

theorem cell21_676154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_676154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676154 prefixEnd_676154 := by exact prefixLift 676154
  have htrace : WordTrace (prefixWord ++ tailWord_676154) baseStart_676154 baseEnd_676154 := by
    simpa [prefixWord, tailWord_676154, baseEnd_676154] using wordTrace_append hprefix tailTrace_676154
  have hstable : (prefixWord ++ tailWord_676154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676154).length < 2 ^ (prefixWord ++ tailWord_676154).sum := by decide
  have hdescent : baseEnd_676154 < baseStart_676154 := by decide
  rcases family_descends (prefixWord ++ tailWord_676154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676168 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_676168 : Nat := 118140960795 + 676168 * 2 ^ 59
def prefixEnd_676168 : Nat := 4983230072969 + 3 ^ 40 * 676168 * 2
def baseEnd_676168 : Nat := 154310749861962543684607

theorem tailTrace_676168 : CollatzResearch.WordTrace tailWord_676168 prefixEnd_676168 154310749861962543684607 := by
  unfold tailWord_676168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330936507183145572826579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16441248676244194097102105 12330936507183145572826579)
  ·
    refine ⟨18496404760774718359239869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12330936507183145572826579 18496404760774718359239869)
    ·
      refine ⟨6936151785290519384714951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18496404760774718359239869 6936151785290519384714951)
      ·
        refine ⟨10404227677935779077072427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936151785290519384714951 10404227677935779077072427)
        ·
          refine ⟨15606341516903668615608641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10404227677935779077072427 15606341516903668615608641)
          ·
            refine ⟨11704756137677751461706481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15606341516903668615608641 11704756137677751461706481)
            ·
              refine ⟨8778567103258313596279861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11704756137677751461706481 8778567103258313596279861)
              ·
                refine ⟨822990665930466899651237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8778567103258313596279861 822990665930466899651237)
                ·
                  refine ⟨154310749861962543684607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822990665930466899651237 154310749861962543684607)
                  ·
                    rfl

theorem cell21_676168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_676168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676168 prefixEnd_676168 := by exact prefixLift 676168
  have htrace : WordTrace (prefixWord ++ tailWord_676168) baseStart_676168 baseEnd_676168 := by
    simpa [prefixWord, tailWord_676168, baseEnd_676168] using wordTrace_append hprefix tailTrace_676168
  have hstable : (prefixWord ++ tailWord_676168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676168).length < 2 ^ (prefixWord ++ tailWord_676168).sum := by decide
  have hdescent : baseEnd_676168 < baseStart_676168 := by decide
  rcases family_descends (prefixWord ++ tailWord_676168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676199 : List Nat := [1, 1, 5, 1, 3, 3, 7]
def baseStart_676199 : Nat := 118140960795 + 676199 * 2 ^ 59
def prefixEnd_676199 : Nat := 4983230072969 + 3 ^ 40 * 676199 * 2
def baseEnd_676199 : Nat := 17146424942701486518653

theorem tailTrace_676199 : CollatzResearch.WordTrace tailWord_676199 prefixEnd_676199 17146424942701486518653 := by
  unfold tailWord_676199
  simp only [CollatzResearch.WordTrace]
  refine ⟨24663003677253983440031651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16442002451502655626687767 24663003677253983440031651)
  ·
    refine ⟨36994505515880975160047477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24663003677253983440031651 36994505515880975160047477)
    ·
      refine ⟨3468234892113841421254451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36994505515880975160047477 3468234892113841421254451)
      ·
        refine ⟨5202352338170762131881677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468234892113841421254451 5202352338170762131881677)
        ·
          refine ⟨1950882126814035799455629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5202352338170762131881677 1950882126814035799455629)
          ·
            refine ⟨731580797555263424795861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1950882126814035799455629 731580797555263424795861)
            ·
              refine ⟨17146424942701486518653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 731580797555263424795861 17146424942701486518653)
              ·
                rfl

theorem cell21_676199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 7].length) (baseStart_676199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676199 prefixEnd_676199 := by exact prefixLift 676199
  have htrace : WordTrace (prefixWord ++ tailWord_676199) baseStart_676199 baseEnd_676199 := by
    simpa [prefixWord, tailWord_676199, baseEnd_676199] using wordTrace_append hprefix tailTrace_676199
  have hstable : (prefixWord ++ tailWord_676199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676199).length < 2 ^ (prefixWord ++ tailWord_676199).sum := by decide
  have hdescent : baseEnd_676199 < baseStart_676199 := by decide
  rcases family_descends (prefixWord ++ tailWord_676199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676264 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_676264 : Nat := 118140960795 + 676264 * 2 ^ 59
def prefixEnd_676264 : Nat := 4983230072969 + 3 ^ 40 * 676264 * 2
def baseEnd_676264 : Nat := 154332658369887710084411

theorem tailTrace_676264 : CollatzResearch.WordTrace tailWord_676264 prefixEnd_676264 154332658369887710084411 := by
  unfold tailWord_676264
  simp only [CollatzResearch.WordTrace]
  refine ⟨12332687211009249770573923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16443582948012333027431897 12332687211009249770573923)
  ·
    refine ⟨18499030816513874655860885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12332687211009249770573923 18499030816513874655860885)
    ·
      refine ⟨867142069524087874493479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18499030816513874655860885 867142069524087874493479)
      ·
        refine ⟨1300713104286131811740219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867142069524087874493479 1300713104286131811740219)
        ·
          refine ⟨1951069656429197717610329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300713104286131811740219 1951069656429197717610329)
          ·
            refine ⟨1463302242321898288207747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951069656429197717610329 1463302242321898288207747)
            ·
              refine ⟨2194953363482847432311621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463302242321898288207747 2194953363482847432311621)
              ·
                refine ⟨411553755653033893558429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2194953363482847432311621 411553755653033893558429)
                ·
                  refine ⟨154332658369887710084411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411553755653033893558429 154332658369887710084411)
                  ·
                    rfl

theorem cell21_676264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_676264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676264 prefixEnd_676264 := by exact prefixLift 676264
  have htrace : WordTrace (prefixWord ++ tailWord_676264) baseStart_676264 baseEnd_676264 := by
    simpa [prefixWord, tailWord_676264, baseEnd_676264] using wordTrace_append hprefix tailTrace_676264
  have hstable : (prefixWord ++ tailWord_676264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676264).length < 2 ^ (prefixWord ++ tailWord_676264).sum := by decide
  have hdescent : baseEnd_676264 < baseStart_676264 := by decide
  rcases family_descends (prefixWord ++ tailWord_676264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676303 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_676303 : Nat := 118140960795 + 676303 * 2 ^ 59
def prefixEnd_676303 : Nat := 4983230072969 + 3 ^ 40 * 676303 * 2
def baseEnd_676303 : Nat := 154341558701232308934331

theorem tailTrace_676303 : CollatzResearch.WordTrace tailWord_676303 prefixEnd_676303 154341558701232308934331 := by
  unfold tailWord_676303
  simp only [CollatzResearch.WordTrace]
  refine ⟨24666796868877209201817563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16444531245918139467878375 24666796868877209201817563)
  ·
    refine ⟨37000195303315813802726345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24666796868877209201817563 37000195303315813802726345)
    ·
      refine ⟨27750146477486860352044759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37000195303315813802726345 27750146477486860352044759)
      ·
        refine ⟨41625219716230290528067139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27750146477486860352044759 41625219716230290528067139)
        ·
          refine ⟨62437829574345435792100709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41625219716230290528067139 62437829574345435792100709)
          ·
            refine ⟨11707093045189769211018883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62437829574345435792100709 11707093045189769211018883)
            ·
              refine ⟨17560639567784653816528325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11707093045189769211018883 17560639567784653816528325)
              ·
                refine ⟨3292619918959622590599061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17560639567784653816528325 3292619918959622590599061)
                ·
                  refine ⟨154341558701232308934331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3292619918959622590599061 154341558701232308934331)
                  ·
                    rfl

theorem cell21_676303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_676303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676303 prefixEnd_676303 := by exact prefixLift 676303
  have htrace : WordTrace (prefixWord ++ tailWord_676303) baseStart_676303 baseEnd_676303 := by
    simpa [prefixWord, tailWord_676303, baseEnd_676303] using wordTrace_append hprefix tailTrace_676303
  have hstable : (prefixWord ++ tailWord_676303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676303).length < 2 ^ (prefixWord ++ tailWord_676303).sum := by decide
  have hdescent : baseEnd_676303 < baseStart_676303 := by decide
  rcases family_descends (prefixWord ++ tailWord_676303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676337 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 4]
def baseStart_676337 : Nat := 118140960795 + 676337 * 2 ^ 59
def prefixEnd_676337 : Nat := 4983230072969 + 3 ^ 40 * 676337 * 2
def baseEnd_676337 : Nat := 154349317964455805367595

theorem tailTrace_676337 : CollatzResearch.WordTrace tailWord_676337 prefixEnd_676337 154349317964455805367595 := by
  unfold tailWord_676337
  simp only [CollatzResearch.WordTrace]
  refine ⟨24668036950754033008555265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16445357967169355339036843 24668036950754033008555265)
  ·
    refine ⟨18501027713065524756416449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24668036950754033008555265 18501027713065524756416449)
    ·
      refine ⟨13875770784799143567312337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18501027713065524756416449 13875770784799143567312337)
      ·
        refine ⟨10406828088599357675484253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13875770784799143567312337 10406828088599357675484253)
        ·
          refine ⟨3902560533224759128306595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10406828088599357675484253 3902560533224759128306595)
          ·
            refine ⟨5853840799837138692459893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902560533224759128306595 5853840799837138692459893)
            ·
              refine ⟨548797574984731752418115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5853840799837138692459893 548797574984731752418115)
              ·
                refine ⟨823196362477097628627173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548797574984731752418115 823196362477097628627173)
                ·
                  refine ⟨154349317964455805367595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823196362477097628627173 154349317964455805367595)
                  ·
                    rfl

theorem cell21_676337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_676337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676337 prefixEnd_676337 := by exact prefixLift 676337
  have htrace : WordTrace (prefixWord ++ tailWord_676337) baseStart_676337 baseEnd_676337 := by
    simpa [prefixWord, tailWord_676337, baseEnd_676337] using wordTrace_append hprefix tailTrace_676337
  have hstable : (prefixWord ++ tailWord_676337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676337).length < 2 ^ (prefixWord ++ tailWord_676337).sum := by decide
  have hdescent : baseEnd_676337 < baseStart_676337 := by decide
  rcases family_descends (prefixWord ++ tailWord_676337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676388 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_676388 : Nat := 118140960795 + 676388 * 2 ^ 59
def prefixEnd_676388 : Nat := 4983230072969 + 3 ^ 40 * 676388 * 2
def baseEnd_676388 : Nat := 154360956859291050017491

theorem tailTrace_676388 : CollatzResearch.WordTrace tailWord_676388 prefixEnd_676388 154360956859291050017491 := by
  unfold tailWord_676388
  simp only [CollatzResearch.WordTrace]
  refine ⟨12334948536784634359330909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16446598049046179145774545 12334948536784634359330909)
  ·
    refine ⟨4625605701294237884749091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12334948536784634359330909 4625605701294237884749091)
    ·
      refine ⟨6938408551941356827123637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625605701294237884749091 6938408551941356827123637)
      ·
        refine ⟨650475801744502202542841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6938408551941356827123637 650475801744502202542841)
        ·
          refine ⟨487856851308376651907131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650475801744502202542841 487856851308376651907131)
          ·
            refine ⟨731785276962564977860697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487856851308376651907131 731785276962564977860697)
            ·
              refine ⟨548838957721923733395523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731785276962564977860697 548838957721923733395523)
              ·
                refine ⟨823258436582885600093285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548838957721923733395523 823258436582885600093285)
                ·
                  refine ⟨154360956859291050017491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823258436582885600093285 154360956859291050017491)
                  ·
                    rfl

theorem cell21_676388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_676388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676388 prefixEnd_676388 := by exact prefixLift 676388
  have htrace : WordTrace (prefixWord ++ tailWord_676388) baseStart_676388 baseEnd_676388 := by
    simpa [prefixWord, tailWord_676388, baseEnd_676388] using wordTrace_append hprefix tailTrace_676388
  have hstable : (prefixWord ++ tailWord_676388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676388).length < 2 ^ (prefixWord ++ tailWord_676388).sum := by decide
  have hdescent : baseEnd_676388 < baseStart_676388 := by decide
  rcases family_descends (prefixWord ++ tailWord_676388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676410 : List Nat := [3, 1, 1, 1, 3, 3, 2, 7]
def baseStart_676410 : Nat := 118140960795 + 676410 * 2 ^ 59
def prefixEnd_676410 : Nat := 4983230072969 + 3 ^ 40 * 676410 * 2
def baseEnd_676410 : Nat := 51455325853007966883593

theorem tailTrace_676410 : CollatzResearch.WordTrace tailWord_676410 prefixEnd_676410 51455325853007966883593 := by
  unfold tailWord_676410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167674869872391618990671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16447132986326377650641789 6167674869872391618990671)
  ·
    refine ⟨9251512304808587428486007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6167674869872391618990671 9251512304808587428486007)
    ·
      refine ⟨13877268457212881142729011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9251512304808587428486007 13877268457212881142729011)
      ·
        refine ⟨20815902685819321714093517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13877268457212881142729011 20815902685819321714093517)
        ·
          refine ⟨7805963507182245642785069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20815902685819321714093517 7805963507182245642785069)
          ·
            refine ⟨2927236315193342116044401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7805963507182245642785069 2927236315193342116044401)
            ·
              refine ⟨2195427236395006587033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927236315193342116044401 2195427236395006587033301)
              ·
                refine ⟨51455325853007966883593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2195427236395006587033301 51455325853007966883593)
                ·
                  rfl

theorem cell21_676410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_676410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676410 prefixEnd_676410 := by exact prefixLift 676410
  have htrace : WordTrace (prefixWord ++ tailWord_676410) baseStart_676410 baseEnd_676410 := by
    simpa [prefixWord, tailWord_676410, baseEnd_676410] using wordTrace_append hprefix tailTrace_676410
  have hstable : (prefixWord ++ tailWord_676410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676410).length < 2 ^ (prefixWord ++ tailWord_676410).sum := by decide
  have hdescent : baseEnd_676410 < baseStart_676410 := by decide
  rcases family_descends (prefixWord ++ tailWord_676410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676444 : List Nat := [2, 2, 4, 1, 3, 2, 1, 6]
def baseStart_676444 : Nat := 118140960795 + 676444 * 2 ^ 59
def prefixEnd_676444 : Nat := 4983230072969 + 3 ^ 40 * 676444 * 2
def baseEnd_676444 : Nat := 51457912274082465694681

theorem tailTrace_676444 : CollatzResearch.WordTrace tailWord_676444 prefixEnd_676444 51457912274082465694681 := by
  unfold tailWord_676444
  simp only [CollatzResearch.WordTrace]
  refine ⟨12335969780683195141350193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16447959707577593521800257 12335969780683195141350193)
  ·
    refine ⟨9251977335512396356012645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12335969780683195141350193 9251977335512396356012645)
    ·
      refine ⟨1734745750408574316752371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9251977335512396356012645 1734745750408574316752371)
      ·
        refine ⟨2602118625612861475128557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734745750408574316752371 2602118625612861475128557)
        ·
          refine ⟨975794484604823053173209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2602118625612861475128557 975794484604823053173209)
          ·
            refine ⟨731845863453617289879907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975794484604823053173209 731845863453617289879907)
            ·
              refine ⟨1097768795180425934819861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731845863453617289879907 1097768795180425934819861)
              ·
                refine ⟨51457912274082465694681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1097768795180425934819861 51457912274082465694681)
                ·
                  rfl

theorem cell21_676444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_676444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676444 prefixEnd_676444 := by exact prefixLift 676444
  have htrace : WordTrace (prefixWord ++ tailWord_676444) baseStart_676444 baseEnd_676444 := by
    simpa [prefixWord, tailWord_676444, baseEnd_676444] using wordTrace_append hprefix tailTrace_676444
  have hstable : (prefixWord ++ tailWord_676444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676444).length < 2 ^ (prefixWord ++ tailWord_676444).sum := by decide
  have hdescent : baseEnd_676444 < baseStart_676444 := by decide
  rcases family_descends (prefixWord ++ tailWord_676444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676455 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_676455 : Nat := 118140960795 + 676455 * 2 ^ 59
def prefixEnd_676455 : Nat := 4983230072969 + 3 ^ 40 * 676455 * 2
def baseEnd_676455 : Nat := 154376247172113822400687

theorem tailTrace_676455 : CollatzResearch.WordTrace tailWord_676455 prefixEnd_676455 154376247172113822400687 := by
  unfold tailWord_676455
  simp only [CollatzResearch.WordTrace]
  refine ⟨24672340764326539161350819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16448227176217692774233879 24672340764326539161350819)
  ·
    refine ⟨37008511146489808742026229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24672340764326539161350819 37008511146489808742026229)
    ·
      refine ⟨3469547919983419569564959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37008511146489808742026229 3469547919983419569564959)
      ·
        refine ⟨5204321879975129354347439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3469547919983419569564959 5204321879975129354347439)
        ·
          refine ⟨7806482819962694031521159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204321879975129354347439 7806482819962694031521159)
          ·
            refine ⟨11709724229944041047281739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806482819962694031521159 11709724229944041047281739)
            ·
              refine ⟨17564586344916061570922609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11709724229944041047281739 17564586344916061570922609)
              ·
                refine ⟨13173439758687046178191957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17564586344916061570922609 13173439758687046178191957)
                ·
                  refine ⟨154376247172113822400687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13173439758687046178191957 154376247172113822400687)
                  ·
                    rfl

theorem cell21_676455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_676455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676455 prefixEnd_676455 := by exact prefixLift 676455
  have htrace : WordTrace (prefixWord ++ tailWord_676455) baseStart_676455 baseEnd_676455 := by
    simpa [prefixWord, tailWord_676455, baseEnd_676455] using wordTrace_append hprefix tailTrace_676455
  have hstable : (prefixWord ++ tailWord_676455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676455).length < 2 ^ (prefixWord ++ tailWord_676455).sum := by decide
  have hdescent : baseEnd_676455 < baseStart_676455 := by decide
  rcases family_descends (prefixWord ++ tailWord_676455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676531 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_676531 : Nat := 118140960795 + 676531 * 2 ^ 59
def prefixEnd_676531 : Nat := 4983230072969 + 3 ^ 40 * 676531 * 2
def baseEnd_676531 : Nat := 154393591407554579133865

theorem tailTrace_676531 : CollatzResearch.WordTrace tailWord_676531 prefixEnd_676531 154393591407554579133865 := by
  unfold tailWord_676531
  simp only [CollatzResearch.WordTrace]
  refine ⟨24675112712051204141117447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16450075141367469427411631 24675112712051204141117447)
  ·
    refine ⟨37012669068076806211676171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24675112712051204141117447 37012669068076806211676171)
    ·
      refine ⟨55519003602115209317514257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37012669068076806211676171 55519003602115209317514257)
      ·
        refine ⟨41639252701586406988135693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55519003602115209317514257 41639252701586406988135693)
        ·
          refine ⟨15614719763094902620550885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41639252701586406988135693 15614719763094902620550885)
          ·
            refine ⟨2927759955580294241353291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15614719763094902620550885 2927759955580294241353291)
            ·
              refine ⟨4391639933370441362029937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927759955580294241353291 4391639933370441362029937)
              ·
                refine ⟨3293729950027831021522453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391639933370441362029937 3293729950027831021522453)
                ·
                  refine ⟨154393591407554579133865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3293729950027831021522453 154393591407554579133865)
                  ·
                    rfl

theorem cell21_676531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_676531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676531 prefixEnd_676531 := by exact prefixLift 676531
  have htrace : WordTrace (prefixWord ++ tailWord_676531) baseStart_676531 baseEnd_676531 := by
    simpa [prefixWord, tailWord_676531, baseEnd_676531] using wordTrace_append hprefix tailTrace_676531
  have hstable : (prefixWord ++ tailWord_676531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676531).length < 2 ^ (prefixWord ++ tailWord_676531).sum := by decide
  have hdescent : baseEnd_676531 < baseStart_676531 := by decide
  rcases family_descends (prefixWord ++ tailWord_676531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676548 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_676548 : Nat := 118140960795 + 676548 * 2 ^ 59
def prefixEnd_676548 : Nat := 4983230072969 + 3 ^ 40 * 676548 * 2
def baseEnd_676548 : Nat := 154397471039166327350497

theorem tailTrace_676548 : CollatzResearch.WordTrace tailWord_676548 prefixEnd_676548 154397471039166327350497 := by
  unfold tailWord_676548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12337866376494808022243149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16450488501993077362990865 12337866376494808022243149)
  ·
    refine ⟨4626699891185553008341181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12337866376494808022243149 4626699891185553008341181)
    ·
      refine ⟨1735012459194582378127943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4626699891185553008341181 1735012459194582378127943)
      ·
        refine ⟨2602518688791873567191915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735012459194582378127943 2602518688791873567191915)
        ·
          refine ⟨3903778033187810350787873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602518688791873567191915 3903778033187810350787873)
          ·
            refine ⟨2927833524890857763090905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3903778033187810350787873 2927833524890857763090905)
            ·
              refine ⟨2195875143668143322318179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927833524890857763090905 2195875143668143322318179)
              ·
                refine ⟨3293812715502214983477269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195875143668143322318179 3293812715502214983477269)
                ·
                  refine ⟨154397471039166327350497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3293812715502214983477269 154397471039166327350497)
                  ·
                    rfl

theorem cell21_676548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_676548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676548 prefixEnd_676548 := by exact prefixLift 676548
  have htrace : WordTrace (prefixWord ++ tailWord_676548) baseStart_676548 baseEnd_676548 := by
    simpa [prefixWord, tailWord_676548, baseEnd_676548] using wordTrace_append hprefix tailTrace_676548
  have hstable : (prefixWord ++ tailWord_676548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676548).length < 2 ^ (prefixWord ++ tailWord_676548).sum := by decide
  have hdescent : baseEnd_676548 < baseStart_676548 := by decide
  rcases family_descends (prefixWord ++ tailWord_676548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676576 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_676576 : Nat := 118140960795 + 676576 * 2 ^ 59
def prefixEnd_676576 : Nat := 4983230072969 + 3 ^ 40 * 676576 * 2
def baseEnd_676576 : Nat := 154403861020644500883773

theorem tailTrace_676576 : CollatzResearch.WordTrace tailWord_676576 prefixEnd_676576 154403861020644500883773 := by
  unfold tailWord_676576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338376998444088413252791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16451169331258784551003721 12338376998444088413252791)
  ·
    refine ⟨18507565497666132619879187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12338376998444088413252791 18507565497666132619879187)
    ·
      refine ⟨27761348246499198929818781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18507565497666132619879187 27761348246499198929818781)
      ·
        refine ⟨10410505592437199598682043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27761348246499198929818781 10410505592437199598682043)
        ·
          refine ⟨15615758388655799398023065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10410505592437199598682043 15615758388655799398023065)
          ·
            refine ⟨11711818791491849548517299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15615758388655799398023065 11711818791491849548517299)
            ·
              refine ⟨17567728187237774322775949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711818791491849548517299 17567728187237774322775949)
              ·
                refine ⟨6587898070214165371040981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17567728187237774322775949 6587898070214165371040981)
                ·
                  refine ⟨154403861020644500883773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6587898070214165371040981 154403861020644500883773)
                  ·
                    rfl

theorem cell21_676576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_676576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676576 prefixEnd_676576 := by exact prefixLift 676576
  have htrace : WordTrace (prefixWord ++ tailWord_676576) baseStart_676576 baseEnd_676576 := by
    simpa [prefixWord, tailWord_676576, baseEnd_676576] using wordTrace_append hprefix tailTrace_676576
  have hstable : (prefixWord ++ tailWord_676576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676576).length < 2 ^ (prefixWord ++ tailWord_676576).sum := by decide
  have hdescent : baseEnd_676576 < baseStart_676576 := by decide
  rcases family_descends (prefixWord ++ tailWord_676576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676596 : List Nat := [2, 6, 1, 1, 2, 9]
def baseStart_676596 : Nat := 118140960795 + 676596 * 2 ^ 59
def prefixEnd_676596 : Nat := 4983230072969 + 3 ^ 40 * 676596 * 2
def baseEnd_676596 : Nat := 5718830566412181872237

theorem tailTrace_676596 : CollatzResearch.WordTrace tailWord_676596 prefixEnd_676596 5718830566412181872237 := by
  unfold tailWord_676596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338741728407860121116821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16451655637877146828155761 12338741728407860121116821)
  ·
    refine ⟨578378518519118443177351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12338741728407860121116821 578378518519118443177351)
    ·
      refine ⟨867567777778677664766027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578378518519118443177351 867567777778677664766027)
      ·
        refine ⟨1301351666668016497149041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867567777778677664766027 1301351666668016497149041)
        ·
          refine ⟨976013750001012372861781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301351666668016497149041 976013750001012372861781)
          ·
            refine ⟨5718830566412181872237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 976013750001012372861781 5718830566412181872237)
            ·
              rfl

theorem cell21_676596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 9].length) (baseStart_676596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676596 prefixEnd_676596 := by exact prefixLift 676596
  have htrace : WordTrace (prefixWord ++ tailWord_676596) baseStart_676596 baseEnd_676596 := by
    simpa [prefixWord, tailWord_676596, baseEnd_676596] using wordTrace_append hprefix tailTrace_676596
  have hstable : (prefixWord ++ tailWord_676596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676596).length < 2 ^ (prefixWord ++ tailWord_676596).sum := by decide
  have hdescent : baseEnd_676596 < baseStart_676596 := by decide
  rcases family_descends (prefixWord ++ tailWord_676596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676652 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_676652 : Nat := 118140960795 + 676652 * 2 ^ 59
def prefixEnd_676652 : Nat := 4983230072969 + 3 ^ 40 * 676652 * 2
def baseEnd_676652 : Nat := 154421205256085257616951

theorem tailTrace_676652 : CollatzResearch.WordTrace tailWord_676652 prefixEnd_676652 154421205256085257616951 := by
  unfold tailWord_676652
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339762972306420903136105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16453017296408561204181473 12339762972306420903136105)
  ·
    refine ⟨9254822229229815677352079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12339762972306420903136105 9254822229229815677352079)
    ·
      refine ⟨13882233343844723516028119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254822229229815677352079 13882233343844723516028119)
      ·
        refine ⟨20823350015767085274042179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13882233343844723516028119 20823350015767085274042179)
        ·
          refine ⟨31235025023650627911063269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20823350015767085274042179 31235025023650627911063269)
          ·
            refine ⟨5856567191934492733324363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31235025023650627911063269 5856567191934492733324363)
            ·
              refine ⟨8784850787901739099986545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856567191934492733324363 8784850787901739099986545)
              ·
                refine ⟨6588638090926304324989909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8784850787901739099986545 6588638090926304324989909)
                ·
                  refine ⟨154421205256085257616951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6588638090926304324989909 154421205256085257616951)
                  ·
                    rfl

theorem cell21_676652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_676652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676652 prefixEnd_676652 := by exact prefixLift 676652
  have htrace : WordTrace (prefixWord ++ tailWord_676652) baseStart_676652 baseEnd_676652 := by
    simpa [prefixWord, tailWord_676652, baseEnd_676652] using wordTrace_append hprefix tailTrace_676652
  have hstable : (prefixWord ++ tailWord_676652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676652).length < 2 ^ (prefixWord ++ tailWord_676652).sum := by decide
  have hdescent : baseEnd_676652 < baseStart_676652 := by decide
  rcases family_descends (prefixWord ++ tailWord_676652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676700 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_676700 : Nat := 118140960795 + 676700 * 2 ^ 59
def prefixEnd_676700 : Nat := 4983230072969 + 3 ^ 40 * 676700 * 2
def baseEnd_676700 : Nat := 154432159510047840816853

theorem tailTrace_676700 : CollatzResearch.WordTrace tailWord_676700 prefixEnd_676700 154432159510047840816853 := by
  unfold tailWord_676700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12340638324219473002009777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16454184432292630669346369 12340638324219473002009777)
  ·
    refine ⟨9255478743164604751507333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12340638324219473002009777 9255478743164604751507333)
    ·
      refine ⟨1735402264343363390907625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9255478743164604751507333 1735402264343363390907625)
      ·
        refine ⟨1301551698257522543180719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1735402264343363390907625 1301551698257522543180719)
        ·
          refine ⟨1952327547386283814771079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301551698257522543180719 1952327547386283814771079)
          ·
            refine ⟨2928491321079425722156619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952327547386283814771079 2928491321079425722156619)
            ·
              refine ⟨4392736981619138583234929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928491321079425722156619 4392736981619138583234929)
              ·
                refine ⟨3294552736214353937426197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392736981619138583234929 3294552736214353937426197)
                ·
                  refine ⟨154432159510047840816853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3294552736214353937426197 154432159510047840816853)
                  ·
                    rfl

theorem cell21_676700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_676700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676700 prefixEnd_676700 := by exact prefixLift 676700
  have htrace : WordTrace (prefixWord ++ tailWord_676700) baseStart_676700 baseEnd_676700 := by
    simpa [prefixWord, tailWord_676700, baseEnd_676700] using wordTrace_append hprefix tailTrace_676700
  have hstable : (prefixWord ++ tailWord_676700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676700).length < 2 ^ (prefixWord ++ tailWord_676700).sum := by decide
  have hdescent : baseEnd_676700 < baseStart_676700 := by decide
  rcases family_descends (prefixWord ++ tailWord_676700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676728 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_676728 : Nat := 118140960795 + 676728 * 2 ^ 59
def prefixEnd_676728 : Nat := 4983230072969 + 3 ^ 40 * 676728 * 2
def baseEnd_676728 : Nat := 154438549491526014350129

theorem tailTrace_676728 : CollatzResearch.WordTrace tailWord_676728 prefixEnd_676728 154438549491526014350129 := by
  unfold tailWord_676728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12341148946168753393019419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16454865261558337857359225 12341148946168753393019419)
  ·
    refine ⟨18511723419253130089529129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12341148946168753393019419 18511723419253130089529129)
    ·
      refine ⟨13883792564439847567146847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18511723419253130089529129 13883792564439847567146847)
      ·
        refine ⟨20825688846659771350720271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13883792564439847567146847 20825688846659771350720271)
        ·
          refine ⟨31238533269989657026080407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20825688846659771350720271 31238533269989657026080407)
          ·
            refine ⟨46857799904984485539120611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31238533269989657026080407 46857799904984485539120611)
            ·
              refine ⟨70286699857476728308680917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46857799904984485539120611 70286699857476728308680917)
              ·
                refine ⟨1647344527909610819734709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70286699857476728308680917 1647344527909610819734709)
                ·
                  refine ⟨154438549491526014350129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647344527909610819734709 154438549491526014350129)
                  ·
                    rfl

theorem cell21_676728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_676728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676728 prefixEnd_676728 := by exact prefixLift 676728
  have htrace : WordTrace (prefixWord ++ tailWord_676728) baseStart_676728 baseEnd_676728 := by
    simpa [prefixWord, tailWord_676728, baseEnd_676728] using wordTrace_append hprefix tailTrace_676728
  have hstable : (prefixWord ++ tailWord_676728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676728).length < 2 ^ (prefixWord ++ tailWord_676728).sum := by decide
  have hdescent : baseEnd_676728 < baseStart_676728 := by decide
  rcases family_descends (prefixWord ++ tailWord_676728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676734 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_676734 : Nat := 118140960795 + 676734 * 2 ^ 59
def prefixEnd_676734 : Nat := 4983230072969 + 3 ^ 40 * 676734 * 2
def baseEnd_676734 : Nat := 154439918773271337250117

theorem tailTrace_676734 : CollatzResearch.WordTrace tailWord_676734 prefixEnd_676734 154439918773271337250117 := by
  unfold tailWord_676734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085314591289471226344657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16455011153543846540504837 3085314591289471226344657)
  ·
    refine ⟨2313985943467103419758493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3085314591289471226344657 2313985943467103419758493)
    ·
      refine ⟨867744728800163782409435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2313985943467103419758493 867744728800163782409435)
      ·
        refine ⟨1301617093200245673614153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867744728800163782409435 1301617093200245673614153)
        ·
          refine ⟨976212819900184255210615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301617093200245673614153 976212819900184255210615)
          ·
            refine ⟨1464319229850276382815923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976212819900184255210615 1464319229850276382815923)
            ·
              refine ⟨2196478844775414574223885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464319229850276382815923 2196478844775414574223885)
              ·
                refine ⟨823679566790780465333957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2196478844775414574223885 823679566790780465333957)
                ·
                  refine ⟨154439918773271337250117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823679566790780465333957 154439918773271337250117)
                  ·
                    rfl

theorem cell21_676734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_676734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676734 prefixEnd_676734 := by exact prefixLift 676734
  have htrace : WordTrace (prefixWord ++ tailWord_676734) baseStart_676734 baseEnd_676734 := by
    simpa [prefixWord, tailWord_676734, baseEnd_676734] using wordTrace_append hprefix tailTrace_676734
  have hstable : (prefixWord ++ tailWord_676734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676734).length < 2 ^ (prefixWord ++ tailWord_676734).sum := by decide
  have hdescent : baseEnd_676734 < baseStart_676734 := by decide
  rcases family_descends (prefixWord ++ tailWord_676734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676835 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_676835 : Nat := 118140960795 + 676835 * 2 ^ 59
def prefixEnd_676835 : Nat := 4983230072969 + 3 ^ 40 * 676835 * 2
def baseEnd_676835 : Nat := 154462968349317606066577

theorem tailTrace_676835 : CollatzResearch.WordTrace tailWord_676835 prefixEnd_676835 154462968349317606066577 := by
  unfold tailWord_676835
  simp only [CollatzResearch.WordTrace]
  refine ⟨24686200502949864060183959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16457467001966576040122639 24686200502949864060183959)
  ·
    refine ⟨37029300754424796090275939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24686200502949864060183959 37029300754424796090275939)
    ·
      refine ⟨55543951131637194135413909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37029300754424796090275939 55543951131637194135413909)
      ·
        refine ⟨2603622709295493475097527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55543951131637194135413909 2603622709295493475097527)
        ·
          refine ⟨3905434063943240212646291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603622709295493475097527 3905434063943240212646291)
          ·
            refine ⟨5858151095914860318969437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905434063943240212646291 5858151095914860318969437)
            ·
              refine ⟨2196806660968072619613539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5858151095914860318969437 2196806660968072619613539)
              ·
                refine ⟨3295209991452108929420309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196806660968072619613539 3295209991452108929420309)
                ·
                  refine ⟨154462968349317606066577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3295209991452108929420309 154462968349317606066577)
                  ·
                    rfl

theorem cell21_676835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_676835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676835 prefixEnd_676835 := by exact prefixLift 676835
  have htrace : WordTrace (prefixWord ++ tailWord_676835) baseStart_676835 baseEnd_676835 := by
    simpa [prefixWord, tailWord_676835, baseEnd_676835] using wordTrace_append hprefix tailTrace_676835
  have hstable : (prefixWord ++ tailWord_676835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676835).length < 2 ^ (prefixWord ++ tailWord_676835).sum := by decide
  have hdescent : baseEnd_676835 < baseStart_676835 := by decide
  rcases family_descends (prefixWord ++ tailWord_676835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676897 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 5]
def baseStart_676897 : Nat := 118140960795 + 676897 * 2 ^ 59
def prefixEnd_676897 : Nat := 4983230072969 + 3 ^ 40 * 676897 * 2
def baseEnd_676897 : Nat := 154477117594019276033117

theorem tailTrace_676897 : CollatzResearch.WordTrace tailWord_676897 prefixEnd_676897 154477117594019276033117 := by
  unfold tailWord_676897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24688461828725248648940945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16458974552483499099293963 24688461828725248648940945)
  ·
    refine ⟨18516346371543936486705709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24688461828725248648940945 18516346371543936486705709)
    ·
      refine ⟨6943629889328976182514641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18516346371543936486705709 6943629889328976182514641)
      ·
        refine ⟨5207722416996732136885981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6943629889328976182514641 5207722416996732136885981)
        ·
          refine ⟨1952895906373774551332243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5207722416996732136885981 1952895906373774551332243)
          ·
            refine ⟨2929343859560661826998365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952895906373774551332243 2929343859560661826998365)
            ·
              refine ⟨1098503947335248185124387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2929343859560661826998365 1098503947335248185124387)
              ·
                refine ⟨1647755921002872277686581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098503947335248185124387 1647755921002872277686581)
                ·
                  refine ⟨154477117594019276033117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647755921002872277686581 154477117594019276033117)
                  ·
                    rfl

theorem cell21_676897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_676897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676897 prefixEnd_676897 := by exact prefixLift 676897
  have htrace : WordTrace (prefixWord ++ tailWord_676897) baseStart_676897 baseEnd_676897 := by
    simpa [prefixWord, tailWord_676897, baseEnd_676897] using wordTrace_append hprefix tailTrace_676897
  have hstable : (prefixWord ++ tailWord_676897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676897).length < 2 ^ (prefixWord ++ tailWord_676897).sum := by decide
  have hdescent : baseEnd_676897 < baseStart_676897 := by decide
  rcases family_descends (prefixWord ++ tailWord_676897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676973 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 5]
def baseStart_676973 : Nat := 118140960795 + 676973 * 2 ^ 59
def prefixEnd_676973 : Nat := 4983230072969 + 3 ^ 40 * 676973 * 2
def baseEnd_676973 : Nat := 154494461829460032766295

theorem tailTrace_676973 : CollatzResearch.WordTrace tailWord_676973 prefixEnd_676973 154494461829460032766295 := by
  unfold tailWord_676973
  simp only [CollatzResearch.WordTrace]
  refine ⟨24691233776449913628707573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16460822517633275752471715 24691233776449913628707573)
  ·
    refine ⟨2314803166542179402691335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24691233776449913628707573 2314803166542179402691335)
    ·
      refine ⟨3472204749813269104037003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314803166542179402691335 3472204749813269104037003)
      ·
        refine ⟨5208307124719903656055505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472204749813269104037003 5208307124719903656055505)
        ·
          refine ⟨3906230343539927742041629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5208307124719903656055505 3906230343539927742041629)
          ·
            refine ⟨1464836378827472903265611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3906230343539927742041629 1464836378827472903265611)
            ·
              refine ⟨2197254568241209354898417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464836378827472903265611 2197254568241209354898417)
              ·
                refine ⟨1647940926180907016173813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197254568241209354898417 1647940926180907016173813)
                ·
                  refine ⟨154494461829460032766295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647940926180907016173813 154494461829460032766295)
                  ·
                    rfl

theorem cell21_676973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_676973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_676973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_676973 prefixEnd_676973 := by exact prefixLift 676973
  have htrace : WordTrace (prefixWord ++ tailWord_676973) baseStart_676973 baseEnd_676973 := by
    simpa [prefixWord, tailWord_676973, baseEnd_676973] using wordTrace_append hprefix tailTrace_676973
  have hstable : (prefixWord ++ tailWord_676973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676973).length < 2 ^ (prefixWord ++ tailWord_676973).sum := by decide
  have hdescent : baseEnd_676973 < baseStart_676973 := by decide
  rcases family_descends (prefixWord ++ tailWord_676973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677001 : List Nat := [1, 2, 1, 1, 4, 4, 8]
def baseStart_677001 : Nat := 118140960795 + 677001 * 2 ^ 59
def prefixEnd_677001 : Nat := 4983230072969 + 3 ^ 40 * 677001 * 2
def baseEnd_677001 : Nat := 17166761312326467366619

theorem tailTrace_677001 : CollatzResearch.WordTrace tailWord_677001 prefixEnd_677001 17166761312326467366619 := by
  unfold tailWord_677001
  simp only [CollatzResearch.WordTrace]
  refine ⟨24692255020348474410726857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16461503346898982940484571 24692255020348474410726857)
  ·
    refine ⟨18519191265261355808045143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24692255020348474410726857 18519191265261355808045143)
    ·
      refine ⟨27778786897892033712067715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18519191265261355808045143 27778786897892033712067715)
      ·
        refine ⟨41668180346838050568101573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27778786897892033712067715 41668180346838050568101573)
        ·
          refine ⟨7812783815032134481519045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41668180346838050568101573 7812783815032134481519045)
          ·
            refine ⟨1464896965318525215284821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7812783815032134481519045 1464896965318525215284821)
            ·
              refine ⟨17166761312326467366619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1464896965318525215284821 17166761312326467366619)
              ·
                rfl

theorem cell21_677001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 8].length) (baseStart_677001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677001 prefixEnd_677001 := by exact prefixLift 677001
  have htrace : WordTrace (prefixWord ++ tailWord_677001) baseStart_677001 baseEnd_677001 := by
    simpa [prefixWord, tailWord_677001, baseEnd_677001] using wordTrace_append hprefix tailTrace_677001
  have hstable : (prefixWord ++ tailWord_677001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677001).length < 2 ^ (prefixWord ++ tailWord_677001).sum := by decide
  have hdescent : baseEnd_677001 < baseStart_677001 := by decide
  rcases family_descends (prefixWord ++ tailWord_677001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677080 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_677080 : Nat := 118140960795 + 677080 * 2 ^ 59
def prefixEnd_677080 : Nat := 4983230072969 + 3 ^ 40 * 677080 * 2
def baseEnd_677080 : Nat := 154518880687251624482743

theorem tailTrace_677080 : CollatzResearch.WordTrace tailWord_677080 prefixEnd_677080 154518880687251624482743 := by
  unfold tailWord_677080
  simp only [CollatzResearch.WordTrace]
  refine ⟨12347568193531135451426347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16463424258041513935235129 12347568193531135451426347)
  ·
    refine ⟨18521352290296703177139521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12347568193531135451426347 18521352290296703177139521)
    ·
      refine ⟨13891014217722527382854641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18521352290296703177139521 13891014217722527382854641)
      ·
        refine ⟨10418260663291895537140981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13891014217722527382854641 10418260663291895537140981)
        ·
          refine ⟨976711937183615206606967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10418260663291895537140981 976711937183615206606967)
          ·
            refine ⟨1465067905775422809910451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976711937183615206606967 1465067905775422809910451)
            ·
              refine ⟨2197601858663134214865677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465067905775422809910451 2197601858663134214865677)
              ·
                refine ⟨824100696998675330574629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2197601858663134214865677 824100696998675330574629)
                ·
                  refine ⟨154518880687251624482743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824100696998675330574629 154518880687251624482743)
                  ·
                    rfl

theorem cell21_677080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_677080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677080 prefixEnd_677080 := by exact prefixLift 677080
  have htrace : WordTrace (prefixWord ++ tailWord_677080) baseStart_677080 baseEnd_677080 := by
    simpa [prefixWord, tailWord_677080, baseEnd_677080] using wordTrace_append hprefix tailTrace_677080
  have hstable : (prefixWord ++ tailWord_677080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677080).length < 2 ^ (prefixWord ++ tailWord_677080).sum := by decide
  have hdescent : baseEnd_677080 < baseStart_677080 := by decide
  rcases family_descends (prefixWord ++ tailWord_677080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677125 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 3]
def baseStart_677125 : Nat := 118140960795 + 677125 * 2 ^ 59
def prefixEnd_677125 : Nat := 4983230072969 + 3 ^ 40 * 677125 * 2
def baseEnd_677125 : Nat := 154529150300341546232651

theorem tailTrace_677125 : CollatzResearch.WordTrace tailWord_677125 prefixEnd_677125 154529150300341546232651 := by
  unfold tailWord_677125
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696777671899243588240829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16464518447932829058827219 24696777671899243588240829)
  ·
    refine ⟨9261291626962216345590311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24696777671899243588240829 9261291626962216345590311)
    ·
      refine ⟨13891937440443324518385467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9261291626962216345590311 13891937440443324518385467)
      ·
        refine ⟨20837906160664986777578201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13891937440443324518385467 20837906160664986777578201)
        ·
          refine ⟨15628429620498740083183651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20837906160664986777578201 15628429620498740083183651)
          ·
            refine ⟨23442644430748110124775477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15628429620498740083183651 23442644430748110124775477)
            ·
              refine ⟨2197747915382635324197701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23442644430748110124775477 2197747915382635324197701)
              ·
                refine ⟨412077734134244123287069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2197747915382635324197701 412077734134244123287069)
                ·
                  refine ⟨154529150300341546232651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412077734134244123287069 154529150300341546232651)
                  ·
                    rfl

theorem cell21_677125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_677125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677125 prefixEnd_677125 := by exact prefixLift 677125
  have htrace : WordTrace (prefixWord ++ tailWord_677125) baseStart_677125 baseEnd_677125 := by
    simpa [prefixWord, tailWord_677125, baseEnd_677125] using wordTrace_append hprefix tailTrace_677125
  have hstable : (prefixWord ++ tailWord_677125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677125).length < 2 ^ (prefixWord ++ tailWord_677125).sum := by decide
  have hdescent : baseEnd_677125 < baseStart_677125 := by decide
  rcases family_descends (prefixWord ++ tailWord_677125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677167 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_677167 : Nat := 118140960795 + 677167 * 2 ^ 59
def prefixEnd_677167 : Nat := 4983230072969 + 3 ^ 40 * 677167 * 2
def baseEnd_677167 : Nat := 154538735272558806532565

theorem tailTrace_677167 : CollatzResearch.WordTrace tailWord_677167 prefixEnd_677167 154538735272558806532565 := by
  unfold tailWord_677167
  simp only [CollatzResearch.WordTrace]
  refine ⟨24698309537747084761269755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16465539691831389840846503 24698309537747084761269755)
  ·
    refine ⟨37047464306620627141904633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24698309537747084761269755 37047464306620627141904633)
    ·
      refine ⟨27785598229965470356428475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37047464306620627141904633 27785598229965470356428475)
      ·
        refine ⟨41678397344948205534642713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27785598229965470356428475 41678397344948205534642713)
        ·
          refine ⟨31258798008711154150982035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41678397344948205534642713 31258798008711154150982035)
          ·
            refine ⟨46888197013066731226473053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31258798008711154150982035 46888197013066731226473053)
            ·
              refine ⟨17583073879900024209927395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46888197013066731226473053 17583073879900024209927395)
              ·
                refine ⟨26374610819850036314891093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17583073879900024209927395 26374610819850036314891093)
                ·
                  refine ⟨154538735272558806532565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26374610819850036314891093 154538735272558806532565)
                  ·
                    rfl

theorem cell21_677167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_677167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677167 prefixEnd_677167 := by exact prefixLift 677167
  have htrace : WordTrace (prefixWord ++ tailWord_677167) baseStart_677167 baseEnd_677167 := by
    simpa [prefixWord, tailWord_677167, baseEnd_677167] using wordTrace_append hprefix tailTrace_677167
  have hstable : (prefixWord ++ tailWord_677167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677167).length < 2 ^ (prefixWord ++ tailWord_677167).sum := by decide
  have hdescent : baseEnd_677167 < baseStart_677167 := by decide
  rcases family_descends (prefixWord ++ tailWord_677167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677184 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_677184 : Nat := 118140960795 + 677184 * 2 ^ 59
def prefixEnd_677184 : Nat := 4983230072969 + 3 ^ 40 * 677184 * 2
def baseEnd_677184 : Nat := 154542614904170554749197

theorem tailTrace_677184 : CollatzResearch.WordTrace tailWord_677184 prefixEnd_677184 154542614904170554749197 := by
  unfold tailWord_677184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349464789342748332319303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16465953052456997776425737 12349464789342748332319303)
  ·
    refine ⟨18524197184014122498478955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12349464789342748332319303 18524197184014122498478955)
    ·
      refine ⟨27786295776021183747718433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18524197184014122498478955 27786295776021183747718433)
      ·
        refine ⟨20839721832015887810788825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27786295776021183747718433 20839721832015887810788825)
        ·
          refine ⟨15629791374011915858091619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20839721832015887810788825 15629791374011915858091619)
          ·
            refine ⟨23444687061017873787137429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15629791374011915858091619 23444687061017873787137429)
            ·
              refine ⟨1098969705985212833772067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23444687061017873787137429 1098969705985212833772067)
              ·
                refine ⟨1648454558977819250658101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098969705985212833772067 1648454558977819250658101)
                ·
                  refine ⟨154542614904170554749197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1648454558977819250658101 154542614904170554749197)
                  ·
                    rfl

theorem cell21_677184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_677184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677184 prefixEnd_677184 := by exact prefixLift 677184
  have htrace : WordTrace (prefixWord ++ tailWord_677184) baseStart_677184 baseEnd_677184 := by
    simpa [prefixWord, tailWord_677184, baseEnd_677184] using wordTrace_append hprefix tailTrace_677184
  have hstable : (prefixWord ++ tailWord_677184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677184).length < 2 ^ (prefixWord ++ tailWord_677184).sum := by decide
  have hdescent : baseEnd_677184 < baseStart_677184 := by decide
  rcases family_descends (prefixWord ++ tailWord_677184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677229 : List Nat := [1, 5, 1, 1, 1, 3, 9]
def baseStart_677229 : Nat := 118140960795 + 677229 * 2 ^ 59
def prefixEnd_677229 : Nat := 4983230072969 + 3 ^ 40 * 677229 * 2
def baseEnd_677229 : Nat := 17172542724140052944345

theorem tailTrace_677229 : CollatzResearch.WordTrace tailWord_677229 prefixEnd_677229 17172542724140052944345 := by
  unfold tailWord_677229
  simp only [CollatzResearch.WordTrace]
  refine ⟨24700570863522469350026741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16467047242348312900017827 24700570863522469350026741)
  ·
    refine ⟨2315678518455231501565007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24700570863522469350026741 2315678518455231501565007)
    ·
      refine ⟨3473517777682847252347511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2315678518455231501565007 3473517777682847252347511)
      ·
        refine ⟨5210276666524270878521267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473517777682847252347511 5210276666524270878521267)
        ·
          refine ⟨7815414999786406317781901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210276666524270878521267 7815414999786406317781901)
          ·
            refine ⟨2930780624919902369168213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7815414999786406317781901 2930780624919902369168213)
            ·
              refine ⟨17172542724140052944345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2930780624919902369168213 17172542724140052944345)
              ·
                rfl

theorem cell21_677229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 9].length) (baseStart_677229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677229 prefixEnd_677229 := by exact prefixLift 677229
  have htrace : WordTrace (prefixWord ++ tailWord_677229) baseStart_677229 baseEnd_677229 := by
    simpa [prefixWord, tailWord_677229, baseEnd_677229] using wordTrace_append hprefix tailTrace_677229
  have hstable : (prefixWord ++ tailWord_677229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677229).length < 2 ^ (prefixWord ++ tailWord_677229).sum := by decide
  have hdescent : baseEnd_677229 < baseStart_677229 := by decide
  rcases family_descends (prefixWord ++ tailWord_677229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677314 : List Nat := [3, 5, 2, 1, 1, 1, 3, 5]
def baseStart_677314 : Nat := 118140960795 + 677314 * 2 ^ 59
def prefixEnd_677314 : Nat := 4983230072969 + 3 ^ 40 * 677314 * 2
def baseEnd_677314 : Nat := 51524094225106405860755

theorem tailTrace_677314 : CollatzResearch.WordTrace tailWord_677314 prefixEnd_677314 51524094225106405860755 := by
  unfold tailWord_677314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175917767053632216717749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16469114045476352577913997 6175917767053632216717749)
  ·
    refine ⟨578992290661278020317289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6175917767053632216717749 578992290661278020317289)
    ·
      refine ⟨434244217995958515237967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 578992290661278020317289 434244217995958515237967)
      ·
        refine ⟨651366326993937772856951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434244217995958515237967 651366326993937772856951)
        ·
          refine ⟨977049490490906659285427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651366326993937772856951 977049490490906659285427)
          ·
            refine ⟨1465574235736359988928141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977049490490906659285427 1465574235736359988928141)
            ·
              refine ⟨549590338401134995848053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1465574235736359988928141 549590338401134995848053)
              ·
                refine ⟨51524094225106405860755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549590338401134995848053 51524094225106405860755)
                ·
                  rfl

theorem cell21_677314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_677314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677314 prefixEnd_677314 := by exact prefixLift 677314
  have htrace : WordTrace (prefixWord ++ tailWord_677314) baseStart_677314 baseEnd_677314 := by
    simpa [prefixWord, tailWord_677314, baseEnd_677314] using wordTrace_append hprefix tailTrace_677314
  have hstable : (prefixWord ++ tailWord_677314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677314).length < 2 ^ (prefixWord ++ tailWord_677314).sum := by decide
  have hdescent : baseEnd_677314 < baseStart_677314 := by decide
  rcases family_descends (prefixWord ++ tailWord_677314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677322 : List Nat := [3, 1, 2, 1, 2, 4, 3, 5]
def baseStart_677322 : Nat := 118140960795 + 677322 * 2 ^ 59
def prefixEnd_677322 : Nat := 4983230072969 + 3 ^ 40 * 677322 * 2
def baseEnd_677322 : Nat := 51524702794770993816305

theorem tailTrace_677322 : CollatzResearch.WordTrace tailWord_677322 prefixEnd_677322 51524702794770993816305 := by
  unfold tailWord_677322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175990713046386558290555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16469308568123697488774813 6175990713046386558290555)
  ·
    refine ⟨9263986069569579837435833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6175990713046386558290555 9263986069569579837435833)
    ·
      refine ⟨6947989552177184878076875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9263986069569579837435833 6947989552177184878076875)
      ·
        refine ⟨10421984328265777317115313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947989552177184878076875 10421984328265777317115313)
        ·
          refine ⟨7816488246199332987836485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10421984328265777317115313 7816488246199332987836485)
          ·
            refine ⟨1465591546162374935219341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7816488246199332987836485 1465591546162374935219341)
            ·
              refine ⟨549596829810890600707253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1465591546162374935219341 549596829810890600707253)
              ·
                refine ⟨51524702794770993816305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549596829810890600707253 51524702794770993816305)
                ·
                  rfl

theorem cell21_677322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_677322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677322 prefixEnd_677322 := by exact prefixLift 677322
  have htrace : WordTrace (prefixWord ++ tailWord_677322) baseStart_677322 baseEnd_677322 := by
    simpa [prefixWord, tailWord_677322, baseEnd_677322] using wordTrace_append hprefix tailTrace_677322
  have hstable : (prefixWord ++ tailWord_677322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677322).length < 2 ^ (prefixWord ++ tailWord_677322).sum := by decide
  have hdescent : baseEnd_677322 < baseStart_677322 := by decide
  rcases family_descends (prefixWord ++ tailWord_677322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677387 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 3]
def baseStart_677387 : Nat := 118140960795 + 677387 * 2 ^ 59
def prefixEnd_677387 : Nat := 4983230072969 + 3 ^ 40 * 677387 * 2
def baseEnd_677387 : Nat := 154588942269887312865449

theorem tailTrace_677387 : CollatzResearch.WordTrace tailWord_677387 prefixEnd_677387 154588942269887312865449 := by
  unfold tailWord_677387
  simp only [CollatzResearch.WordTrace]
  refine ⟨24706333596950062334278415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16470889064633374889518943 24706333596950062334278415)
  ·
    refine ⟨37059500395425093501417623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24706333596950062334278415 37059500395425093501417623)
    ·
      refine ⟨55589250593137640252126435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37059500395425093501417623 55589250593137640252126435)
      ·
        refine ⟨83383875889706460378189653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55589250593137640252126435 83383875889706460378189653)
        ·
          refine ⟨488577397791248791278455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 83383875889706460378189653 488577397791248791278455)
          ·
            refine ⟨732866096686873186917683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488577397791248791278455 732866096686873186917683)
            ·
              refine ⟨1099299145030309780376525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732866096686873186917683 1099299145030309780376525)
              ·
                refine ⟨412237179386366167641197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099299145030309780376525 412237179386366167641197)
                ·
                  refine ⟨154588942269887312865449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412237179386366167641197 154588942269887312865449)
                  ·
                    rfl

theorem cell21_677387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 3].length) (baseStart_677387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677387 prefixEnd_677387 := by exact prefixLift 677387
  have htrace : WordTrace (prefixWord ++ tailWord_677387) baseStart_677387 baseEnd_677387 := by
    simpa [prefixWord, tailWord_677387, baseEnd_677387] using wordTrace_append hprefix tailTrace_677387
  have hstable : (prefixWord ++ tailWord_677387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677387).length < 2 ^ (prefixWord ++ tailWord_677387).sum := by decide
  have hdescent : baseEnd_677387 < baseStart_677387 := by decide
  rcases family_descends (prefixWord ++ tailWord_677387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677488 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_677488 : Nat := 118140960795 + 677488 * 2 ^ 59
def prefixEnd_677488 : Nat := 4983230072969 + 3 ^ 40 * 677488 * 2
def baseEnd_677488 : Nat := 154611991845933581681909

theorem tailTrace_677488 : CollatzResearch.WordTrace tailWord_677488 prefixEnd_677488 154611991845933581681909 := by
  unfold tailWord_677488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355008684792078291852559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16473344913056104389136745 12355008684792078291852559)
  ·
    refine ⟨18532513027188117437778839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12355008684792078291852559 18532513027188117437778839)
    ·
      refine ⟨27798769540782176156668259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18532513027188117437778839 27798769540782176156668259)
      ·
        refine ⟨41698154311173264235002389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27798769540782176156668259 41698154311173264235002389)
        ·
          refine ⟨1954600983336246761015737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41698154311173264235002389 1954600983336246761015737)
          ·
            refine ⟨1465950737502185070761803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954600983336246761015737 1465950737502185070761803)
            ·
              refine ⟨2198926106253277606142705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465950737502185070761803 2198926106253277606142705)
              ·
                refine ⟨1649194579689958204607029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198926106253277606142705 1649194579689958204607029)
                ·
                  refine ⟨154611991845933581681909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649194579689958204607029 154611991845933581681909)
                  ·
                    rfl

theorem cell21_677488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_677488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677488 prefixEnd_677488 := by exact prefixLift 677488
  have htrace : WordTrace (prefixWord ++ tailWord_677488) baseStart_677488 baseEnd_677488 := by
    simpa [prefixWord, tailWord_677488, baseEnd_677488] using wordTrace_append hprefix tailTrace_677488
  have hstable : (prefixWord ++ tailWord_677488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677488).length < 2 ^ (prefixWord ++ tailWord_677488).sum := by decide
  have hdescent : baseEnd_677488 < baseStart_677488 := by decide
  rcases family_descends (prefixWord ++ tailWord_677488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677505 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 3]
def baseStart_677505 : Nat := 118140960795 + 677505 * 2 ^ 59
def prefixEnd_677505 : Nat := 4983230072969 + 3 ^ 40 * 677505 * 2
def baseEnd_677505 : Nat := 154615871477545329898541

theorem tailTrace_677505 : CollatzResearch.WordTrace tailWord_677505 prefixEnd_677505 154615871477545329898541 := by
  unfold tailWord_677505
  simp only [CollatzResearch.WordTrace]
  refine ⟨24710637410522568487073969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16473758273681712324715979 24710637410522568487073969)
  ·
    refine ⟨18532978057891926365305477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24710637410522568487073969 18532978057891926365305477)
    ·
      refine ⟨3474933385854736193494777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18532978057891926365305477 3474933385854736193494777)
      ·
        refine ⟨2606200039391052145121083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3474933385854736193494777 2606200039391052145121083)
        ·
          refine ⟨3909300059086578217681625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606200039391052145121083 3909300059086578217681625)
          ·
            refine ⟨2931975044314933663261219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909300059086578217681625 2931975044314933663261219)
            ·
              refine ⟨4397962566472400494891829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931975044314933663261219 4397962566472400494891829)
              ·
                refine ⟨412308990606787546396109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4397962566472400494891829 412308990606787546396109)
                ·
                  refine ⟨154615871477545329898541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412308990606787546396109 154615871477545329898541)
                  ·
                    rfl

theorem cell21_677505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_677505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677505 prefixEnd_677505 := by exact prefixLift 677505
  have htrace : WordTrace (prefixWord ++ tailWord_677505) baseStart_677505 baseEnd_677505 := by
    simpa [prefixWord, tailWord_677505, baseEnd_677505] using wordTrace_append hprefix tailTrace_677505
  have hstable : (prefixWord ++ tailWord_677505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677505).length < 2 ^ (prefixWord ++ tailWord_677505).sum := by decide
  have hdescent : baseEnd_677505 < baseStart_677505 := by decide
  rcases family_descends (prefixWord ++ tailWord_677505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677516 : List Nat := [2, 2, 1, 2, 1, 1, 12]
def baseStart_677516 : Nat := 118140960795 + 677516 * 2 ^ 59
def prefixEnd_677516 : Nat := 4983230072969 + 3 ^ 40 * 677516 * 2
def baseEnd_677516 : Nat := 17179820203045750579465

theorem tailTrace_677516 : CollatzResearch.WordTrace tailWord_677516 prefixEnd_677516 17179820203045750579465 := by
  unfold tailWord_677516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355519306741358682862201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16474025742321811577149601 12355519306741358682862201)
  ·
    refine ⟨9266639480056019012146651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12355519306741358682862201 9266639480056019012146651)
    ·
      refine ⟨13899959220084028518219977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9266639480056019012146651 13899959220084028518219977)
      ·
        refine ⟨10424969415063021388664983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13899959220084028518219977 10424969415063021388664983)
        ·
          refine ⟨15637454122594532082997475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424969415063021388664983 15637454122594532082997475)
          ·
            refine ⟨23456181183891798124496213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15637454122594532082997475 23456181183891798124496213)
            ·
              refine ⟨17179820203045750579465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 23456181183891798124496213 17179820203045750579465)
              ·
                rfl

theorem cell21_677516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 12].length) (baseStart_677516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677516 prefixEnd_677516 := by exact prefixLift 677516
  have htrace : WordTrace (prefixWord ++ tailWord_677516) baseStart_677516 baseEnd_677516 := by
    simpa [prefixWord, tailWord_677516, baseEnd_677516] using wordTrace_append hprefix tailTrace_677516
  have hstable : (prefixWord ++ tailWord_677516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677516).length < 2 ^ (prefixWord ++ tailWord_677516).sum := by decide
  have hdescent : baseEnd_677516 < baseStart_677516 := by decide
  rcases family_descends (prefixWord ++ tailWord_677516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677536 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_677536 : Nat := 118140960795 + 677536 * 2 ^ 59
def prefixEnd_677536 : Nat := 4983230072969 + 3 ^ 40 * 677536 * 2
def baseEnd_677536 : Nat := 154622946099896164881811

theorem tailTrace_677536 : CollatzResearch.WordTrace tailWord_677536 prefixEnd_677536 154622946099896164881811 := by
  unfold tailWord_677536
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355884036705130390726231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16474512048940173854301641 12355884036705130390726231)
  ·
    refine ⟨18533826055057695586089347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12355884036705130390726231 18533826055057695586089347)
    ·
      refine ⟨27800739082586543379134021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18533826055057695586089347 27800739082586543379134021)
      ·
        refine ⟨5212638577984976883587629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27800739082586543379134021 5212638577984976883587629)
        ·
          refine ⟨1954739466744366331345361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5212638577984976883587629 1954739466744366331345361)
          ·
            refine ⟨1466054600058274748509021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954739466744366331345361 1466054600058274748509021)
            ·
              refine ⟨549770475021853030690883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1466054600058274748509021 549770475021853030690883)
              ·
                refine ⟨824655712532779546036325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549770475021853030690883 824655712532779546036325)
                ·
                  refine ⟨154622946099896164881811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824655712532779546036325 154622946099896164881811)
                  ·
                    rfl

theorem cell21_677536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_677536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677536 prefixEnd_677536 := by exact prefixLift 677536
  have htrace : WordTrace (prefixWord ++ tailWord_677536) baseStart_677536 baseEnd_677536 := by
    simpa [prefixWord, tailWord_677536, baseEnd_677536] using wordTrace_append hprefix tailTrace_677536
  have hstable : (prefixWord ++ tailWord_677536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677536).length < 2 ^ (prefixWord ++ tailWord_677536).sum := by decide
  have hdescent : baseEnd_677536 < baseStart_677536 := by decide
  rcases family_descends (prefixWord ++ tailWord_677536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677685 : List Nat := [1, 3, 3, 1, 4, 1, 8]
def baseStart_677685 : Nat := 118140960795 + 677685 * 2 ^ 59
def prefixEnd_677685 : Nat := 4983230072969 + 3 ^ 40 * 677685 * 2
def baseEnd_677685 : Nat := 17184105547767224099797

theorem tailTrace_677685 : CollatzResearch.WordTrace tailWord_677685 prefixEnd_677685 17184105547767224099797 := by
  unfold tailWord_677685
  simp only [CollatzResearch.WordTrace]
  refine ⟨24717202549870459228626509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16478135033246972819084339 24717202549870459228626509)
  ·
    refine ⟨9268950956201422210734941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24717202549870459228626509 9268950956201422210734941)
    ·
      refine ⟨3475856608575533329025603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9268950956201422210734941 3475856608575533329025603)
      ·
        refine ⟨5213784912863299993538405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475856608575533329025603 5213784912863299993538405)
        ·
          refine ⟨977584671161868748788451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5213784912863299993538405 977584671161868748788451)
          ·
            refine ⟨1466377006742803123182677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977584671161868748788451 1466377006742803123182677)
            ·
              refine ⟨17184105547767224099797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1466377006742803123182677 17184105547767224099797)
              ·
                rfl

theorem cell21_677685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 8].length) (baseStart_677685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677685 prefixEnd_677685 := by exact prefixLift 677685
  have htrace : WordTrace (prefixWord ++ tailWord_677685) baseStart_677685 baseEnd_677685 := by
    simpa [prefixWord, tailWord_677685, baseEnd_677685] using wordTrace_append hprefix tailTrace_677685
  have hstable : (prefixWord ++ tailWord_677685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677685).length < 2 ^ (prefixWord ++ tailWord_677685).sum := by decide
  have hdescent : baseEnd_677685 < baseStart_677685 := by decide
  rcases family_descends (prefixWord ++ tailWord_677685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677699 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_677699 : Nat := 118140960795 + 677699 * 2 ^ 59
def prefixEnd_677699 : Nat := 4983230072969 + 3 ^ 40 * 677699 * 2
def baseEnd_677699 : Nat := 154660144920644103664811

theorem tailTrace_677699 : CollatzResearch.WordTrace tailWord_677699 prefixEnd_677699 154660144920644103664811 := by
  unfold tailWord_677699
  simp only [CollatzResearch.WordTrace]
  refine ⟨24717713171819739619636151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16478475447879826413090767 24717713171819739619636151)
  ·
    refine ⟨37076569757729609429454227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24717713171819739619636151 37076569757729609429454227)
    ·
      refine ⟨55614854636594414144181341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37076569757729609429454227 55614854636594414144181341)
      ·
        refine ⟨20855570488722905304068003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55614854636594414144181341 20855570488722905304068003)
        ·
          refine ⟨31283355733084357956102005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20855570488722905304068003 31283355733084357956102005)
          ·
            refine ⟨2932814599976658558384563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31283355733084357956102005 2932814599976658558384563)
            ·
              refine ⟨4399221899964987837576845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932814599976658558384563 4399221899964987837576845)
              ·
                refine ⟨1649708212486870439091317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4399221899964987837576845 1649708212486870439091317)
                ·
                  refine ⟨154660144920644103664811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649708212486870439091317 154660144920644103664811)
                  ·
                    rfl

theorem cell21_677699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_677699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677699 prefixEnd_677699 := by exact prefixLift 677699
  have htrace : WordTrace (prefixWord ++ tailWord_677699) baseStart_677699 baseEnd_677699 := by
    simpa [prefixWord, tailWord_677699, baseEnd_677699] using wordTrace_append hprefix tailTrace_677699
  have hstable : (prefixWord ++ tailWord_677699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677699).length < 2 ^ (prefixWord ++ tailWord_677699).sum := by decide
  have hdescent : baseEnd_677699 < baseStart_677699 := by decide
  rcases family_descends (prefixWord ++ tailWord_677699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677716 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_677716 : Nat := 118140960795 + 677716 * 2 ^ 59
def prefixEnd_677716 : Nat := 4983230072969 + 3 ^ 40 * 677716 * 2
def baseEnd_677716 : Nat := 154664024552255851881443

theorem tailTrace_677716 : CollatzResearch.WordTrace tailWord_677716 prefixEnd_677716 154664024552255851881443 := by
  unfold tailWord_677716
  simp only [CollatzResearch.WordTrace]
  refine ⟨12359166606379075761502501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16478888808505434348670001 12359166606379075761502501)
  ·
    refine ⟨2317343738696076705281719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12359166606379075761502501 2317343738696076705281719)
    ·
      refine ⟨3476015608044115057922579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317343738696076705281719 3476015608044115057922579)
      ·
        refine ⟨5214023412066172586883869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476015608044115057922579 5214023412066172586883869)
        ·
          refine ⟨1955258779524814720081451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5214023412066172586883869 1955258779524814720081451)
          ·
            refine ⟨2932888169287222080122177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955258779524814720081451 2932888169287222080122177)
            ·
              refine ⟨2199666126965416560091633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932888169287222080122177 2199666126965416560091633)
              ·
                refine ⟨1649749595224062420068725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2199666126965416560091633 1649749595224062420068725)
                ·
                  refine ⟨154664024552255851881443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649749595224062420068725 154664024552255851881443)
                  ·
                    rfl

theorem cell21_677716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_677716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677716 prefixEnd_677716 := by exact prefixLift 677716
  have htrace : WordTrace (prefixWord ++ tailWord_677716) baseStart_677716 baseEnd_677716 := by
    simpa [prefixWord, tailWord_677716, baseEnd_677716] using wordTrace_append hprefix tailTrace_677716
  have hstable : (prefixWord ++ tailWord_677716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677716).length < 2 ^ (prefixWord ++ tailWord_677716).sum := by decide
  have hdescent : baseEnd_677716 < baseStart_677716 := by decide
  rcases family_descends (prefixWord ++ tailWord_677716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677719 : List Nat := [1, 1, 3, 2, 6, 1, 2, 5]
def baseStart_677719 : Nat := 118140960795 + 677719 * 2 ^ 59
def prefixEnd_677719 : Nat := 4983230072969 + 3 ^ 40 * 677719 * 2
def baseEnd_677719 : Nat := 51554903064376171110479

theorem tailTrace_677719 : CollatzResearch.WordTrace tailWord_677719 prefixEnd_677719 51554903064376171110479 := by
  unfold tailWord_677719
  simp only [CollatzResearch.WordTrace]
  refine ⟨24718442631747283035364211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16478961754498188690242807 24718442631747283035364211)
  ·
    refine ⟨37077663947620924553046317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24718442631747283035364211 37077663947620924553046317)
    ·
      refine ⟨13904123980357846707392369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37077663947620924553046317 13904123980357846707392369)
      ·
        refine ⟨10428092985268385030544277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13904123980357846707392369 10428092985268385030544277)
        ·
          refine ⟨488816858684455548306763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10428092985268385030544277 488816858684455548306763)
          ·
            refine ⟨733225288026683322460145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488816858684455548306763 733225288026683322460145)
            ·
              refine ⟨549918966020012491845109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733225288026683322460145 549918966020012491845109)
              ·
                refine ⟨51554903064376171110479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549918966020012491845109 51554903064376171110479)
                ·
                  rfl

theorem cell21_677719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 5].length) (baseStart_677719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677719 prefixEnd_677719 := by exact prefixLift 677719
  have htrace : WordTrace (prefixWord ++ tailWord_677719) baseStart_677719 baseEnd_677719 := by
    simpa [prefixWord, tailWord_677719, baseEnd_677719] using wordTrace_append hprefix tailTrace_677719
  have hstable : (prefixWord ++ tailWord_677719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677719).length < 2 ^ (prefixWord ++ tailWord_677719).sum := by decide
  have hdescent : baseEnd_677719 < baseStart_677719 := by decide
  rcases family_descends (prefixWord ++ tailWord_677719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677750 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_677750 : Nat := 118140960795 + 677750 * 2 ^ 59
def prefixEnd_677750 : Nat := 4983230072969 + 3 ^ 40 * 677750 * 2
def baseEnd_677750 : Nat := 154671783815479348314707

theorem tailTrace_677750 : CollatzResearch.WordTrace tailWord_677750 prefixEnd_677750 154671783815479348314707 := by
  unfold tailWord_677750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544973330914685958108919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16479715529756650219828469 1544973330914685958108919)
  ·
    refine ⟨2317459996372028937163379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544973330914685958108919 2317459996372028937163379)
    ·
      refine ⟨3476189994558043405745069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317459996372028937163379 3476189994558043405745069)
      ·
        refine ⟨1303571247959266277154401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3476189994558043405745069 1303571247959266277154401)
        ·
          refine ⟨977678435969449707865801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1303571247959266277154401 977678435969449707865801)
          ·
            refine ⟨733258826977087280899351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977678435969449707865801 733258826977087280899351)
            ·
              refine ⟨1099888240465630921349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733258826977087280899351 1099888240465630921349027)
              ·
                refine ⟨1649832360698446382023541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099888240465630921349027 1649832360698446382023541)
                ·
                  refine ⟨154671783815479348314707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649832360698446382023541 154671783815479348314707)
                  ·
                    rfl

theorem cell21_677750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_677750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677750 prefixEnd_677750 := by exact prefixLift 677750
  have htrace : WordTrace (prefixWord ++ tailWord_677750) baseStart_677750 baseEnd_677750 := by
    simpa [prefixWord, tailWord_677750, baseEnd_677750] using wordTrace_append hprefix tailTrace_677750
  have hstable : (prefixWord ++ tailWord_677750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677750).length < 2 ^ (prefixWord ++ tailWord_677750).sum := by decide
  have hdescent : baseEnd_677750 < baseStart_677750 := by decide
  rcases family_descends (prefixWord ++ tailWord_677750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677792 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_677792 : Nat := 118140960795 + 677792 * 2 ^ 59
def prefixEnd_677792 : Nat := 4983230072969 + 3 ^ 40 * 677792 * 2
def baseEnd_677792 : Nat := 154681368787696608614621

theorem tailTrace_677792 : CollatzResearch.WordTrace tailWord_677792 prefixEnd_677792 154681368787696608614621 := by
  unfold tailWord_677792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360552580241408251385815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16480736773655211001847753 12360552580241408251385815)
  ·
    refine ⟨18540828870362112377078723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12360552580241408251385815 18540828870362112377078723)
    ·
      refine ⟨27811243305543168565618085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18540828870362112377078723 27811243305543168565618085)
      ·
        refine ⟨5214608119789344106053391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27811243305543168565618085 5214608119789344106053391)
        ·
          refine ⟨7821912179684016159080087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214608119789344106053391 7821912179684016159080087)
          ·
            refine ⟨11732868269526024238620131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821912179684016159080087 11732868269526024238620131)
            ·
              refine ⟨17599302404289036357930197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11732868269526024238620131 17599302404289036357930197)
              ·
                refine ⟨412483650100524289638989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17599302404289036357930197 412483650100524289638989)
                ·
                  refine ⟨154681368787696608614621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412483650100524289638989 154681368787696608614621)
                  ·
                    rfl

theorem cell21_677792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_677792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677792 prefixEnd_677792 := by exact prefixLift 677792
  have htrace : WordTrace (prefixWord ++ tailWord_677792) baseStart_677792 baseEnd_677792 := by
    simpa [prefixWord, tailWord_677792, baseEnd_677792] using wordTrace_append hprefix tailTrace_677792
  have hstable : (prefixWord ++ tailWord_677792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677792).length < 2 ^ (prefixWord ++ tailWord_677792).sum := by decide
  have hdescent : baseEnd_677792 < baseStart_677792 := by decide
  rcases family_descends (prefixWord ++ tailWord_677792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677809 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 3]
def baseStart_677809 : Nat := 118140960795 + 677809 * 2 ^ 59
def prefixEnd_677809 : Nat := 4983230072969 + 3 ^ 40 * 677809 * 2
def baseEnd_677809 : Nat := 154685248419308356831253

theorem tailTrace_677809 : CollatzResearch.WordTrace tailWord_677809 prefixEnd_677809 154685248419308356831253 := by
  unfold tailWord_677809
  simp only [CollatzResearch.WordTrace]
  refine ⟨24721725201421228406140481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16481150134280818937426987 24721725201421228406140481)
  ·
    refine ⟨18541293901065921304605361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24721725201421228406140481 18541293901065921304605361)
    ·
      refine ⟨13905970425799440978454021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18541293901065921304605361 13905970425799440978454021)
      ·
        refine ⟨2607369454837395183460129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13905970425799440978454021 2607369454837395183460129)
        ·
          refine ⟨1955527091128046387595097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607369454837395183460129 1955527091128046387595097)
          ·
            refine ⟨1466645318346034790696323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1955527091128046387595097 1466645318346034790696323)
            ·
              refine ⟨2199967977519052186044485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466645318346034790696323 2199967977519052186044485)
              ·
                refine ⟨412493995784822284883341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2199967977519052186044485 412493995784822284883341)
                ·
                  refine ⟨154685248419308356831253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412493995784822284883341 154685248419308356831253)
                  ·
                    rfl

theorem cell21_677809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_677809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677809 prefixEnd_677809 := by exact prefixLift 677809
  have htrace : WordTrace (prefixWord ++ tailWord_677809) baseStart_677809 baseEnd_677809 := by
    simpa [prefixWord, tailWord_677809, baseEnd_677809] using wordTrace_append hprefix tailTrace_677809
  have hstable : (prefixWord ++ tailWord_677809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677809).length < 2 ^ (prefixWord ++ tailWord_677809).sum := by decide
  have hdescent : baseEnd_677809 < baseStart_677809 := by decide
  rcases family_descends (prefixWord ++ tailWord_677809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677812 : List Nat := [2, 5, 2, 1, 3, 1, 1, 6]
def baseStart_677812 : Nat := 118140960795 + 677812 * 2 ^ 59
def prefixEnd_677812 : Nat := 4983230072969 + 3 ^ 40 * 677812 * 2
def baseEnd_677812 : Nat := 51561977686727006093749

theorem tailTrace_677812 : CollatzResearch.WordTrace tailWord_677812 prefixEnd_677812 51561977686727006093749 := by
  unfold tailWord_677812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360917310205179959249845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16481223080273573278999793 12360917310205179959249845)
  ·
    refine ⟨1158835997831735621179673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12360917310205179959249845 1158835997831735621179673)
    ·
      refine ⟨869126998373801715884755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158835997831735621179673 869126998373801715884755)
      ·
        refine ⟨1303690497560702573827133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869126998373801715884755 1303690497560702573827133)
        ·
          refine ⟨488883936585263465185175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1303690497560702573827133 488883936585263465185175)
          ·
            refine ⟨733325904877895197777763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488883936585263465185175 733325904877895197777763)
            ·
              refine ⟨1099988857316842796666645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733325904877895197777763 1099988857316842796666645)
              ·
                refine ⟨51561977686727006093749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1099988857316842796666645 51561977686727006093749)
                ·
                  rfl

theorem cell21_677812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_677812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677812 prefixEnd_677812 := by exact prefixLift 677812
  have htrace : WordTrace (prefixWord ++ tailWord_677812) baseStart_677812 baseEnd_677812 := by
    simpa [prefixWord, tailWord_677812, baseEnd_677812] using wordTrace_append hprefix tailTrace_677812
  have hstable : (prefixWord ++ tailWord_677812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677812).length < 2 ^ (prefixWord ++ tailWord_677812).sum := by decide
  have hdescent : baseEnd_677812 < baseStart_677812 := by decide
  rcases family_descends (prefixWord ++ tailWord_677812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677894 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_677894 : Nat := 118140960795 + 677894 * 2 ^ 59
def prefixEnd_677894 : Nat := 4983230072969 + 3 ^ 40 * 677894 * 2
def baseEnd_677894 : Nat := 154704646577367097914413

theorem tailTrace_677894 : CollatzResearch.WordTrace tailWord_677894 prefixEnd_677894 154704646577367097914413 := by
  unfold tailWord_677894
  simp only [CollatzResearch.WordTrace]
  refine ⟨772650793941040247593273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16483216937408858615323157 772650793941040247593273)
  ·
    refine ⟨579488095455780185694955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772650793941040247593273 579488095455780185694955)
    ·
      refine ⟨869232143183670278542433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579488095455780185694955 869232143183670278542433)
      ·
        refine ⟨651924107387752708906825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 869232143183670278542433 651924107387752708906825)
        ·
          refine ⟨488943080540814531680119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651924107387752708906825 488943080540814531680119)
          ·
            refine ⟨733414620811221797520179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488943080540814531680119 733414620811221797520179)
            ·
              refine ⟨1100121931216832696280269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733414620811221797520179 1100121931216832696280269)
              ·
                refine ⟨412545724206312261105101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1100121931216832696280269 412545724206312261105101)
                ·
                  refine ⟨154704646577367097914413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412545724206312261105101 154704646577367097914413)
                  ·
                    rfl

theorem cell21_677894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_677894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677894 prefixEnd_677894 := by exact prefixLift 677894
  have htrace : WordTrace (prefixWord ++ tailWord_677894) baseStart_677894 baseEnd_677894 := by
    simpa [prefixWord, tailWord_677894, baseEnd_677894] using wordTrace_append hprefix tailTrace_677894
  have hstable : (prefixWord ++ tailWord_677894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677894).length < 2 ^ (prefixWord ++ tailWord_677894).sum := by decide
  have hdescent : baseEnd_677894 < baseStart_677894 := by decide
  rcases family_descends (prefixWord ++ tailWord_677894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677896 : List Nat := [2, 1, 3, 2, 1, 2, 3, 7]
def baseStart_677896 : Nat := 118140960795 + 677896 * 2 ^ 59
def prefixEnd_677896 : Nat := 4983230072969 + 3 ^ 40 * 677896 * 2
def baseEnd_677896 : Nat := 51568367668205179627025

theorem tailTrace_677896 : CollatzResearch.WordTrace tailWord_677896 prefixEnd_677896 51568367668205179627025 := by
  unfold tailWord_677896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12362449176053021132278771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16483265568070694843038361 12362449176053021132278771)
  ·
    refine ⟨18543673764079531698418157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12362449176053021132278771 18543673764079531698418157)
    ·
      refine ⟨6953877661529824386906809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18543673764079531698418157 6953877661529824386906809)
      ·
        refine ⟨5215408246147368290180107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6953877661529824386906809 5215408246147368290180107)
        ·
          refine ⟨7823112369221052435270161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215408246147368290180107 7823112369221052435270161)
          ·
            refine ⟨5867334276915789326452621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7823112369221052435270161 5867334276915789326452621)
            ·
              refine ⟨2200250353843420997419733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5867334276915789326452621 2200250353843420997419733)
              ·
                refine ⟨51568367668205179627025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2200250353843420997419733 51568367668205179627025)
                ·
                  rfl

theorem cell21_677896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_677896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677896 prefixEnd_677896 := by exact prefixLift 677896
  have htrace : WordTrace (prefixWord ++ tailWord_677896) baseStart_677896 baseEnd_677896 := by
    simpa [prefixWord, tailWord_677896, baseEnd_677896] using wordTrace_append hprefix tailTrace_677896
  have hstable : (prefixWord ++ tailWord_677896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677896).length < 2 ^ (prefixWord ++ tailWord_677896).sum := by decide
  have hdescent : baseEnd_677896 < baseStart_677896 := by decide
  rcases family_descends (prefixWord ++ tailWord_677896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677989 : List Nat := [1, 3, 1, 3, 2, 4, 1, 6]
def baseStart_677989 : Nat := 118140960795 + 677989 * 2 ^ 59
def prefixEnd_677989 : Nat := 4983230072969 + 3 ^ 40 * 677989 * 2
def baseEnd_677989 : Nat := 51575442290556014610295

theorem tailTrace_677989 : CollatzResearch.WordTrace tailWord_677989 prefixEnd_677989 51575442290556014610295 := by
  unfold tailWord_677989
  simp only [CollatzResearch.WordTrace]
  refine ⟨24728290340769119147693021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16485526893846079431795347 24728290340769119147693021)
  ·
    refine ⟨9273108877788419680384883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24728290340769119147693021 9273108877788419680384883)
    ·
      refine ⟨13909663316682629520577325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9273108877788419680384883 13909663316682629520577325)
      ·
        refine ⟨5216123743755986070216497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13909663316682629520577325 5216123743755986070216497)
        ·
          refine ⟨3912092807816989552662373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5216123743755986070216497 3912092807816989552662373)
          ·
            refine ⟨733517401465685541124195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3912092807816989552662373 733517401465685541124195)
            ·
              refine ⟨1100276102198528311686293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733517401465685541124195 1100276102198528311686293)
              ·
                refine ⟨51575442290556014610295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1100276102198528311686293 51575442290556014610295)
                ·
                  rfl

theorem cell21_677989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 6].length) (baseStart_677989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_677989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_677989 prefixEnd_677989 := by exact prefixLift 677989
  have htrace : WordTrace (prefixWord ++ tailWord_677989) baseStart_677989 baseEnd_677989 := by
    simpa [prefixWord, tailWord_677989, baseEnd_677989] using wordTrace_append hprefix tailTrace_677989
  have hstable : (prefixWord ++ tailWord_677989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677989).length < 2 ^ (prefixWord ++ tailWord_677989).sum := by decide
  have hdescent : baseEnd_677989 < baseStart_677989 := by decide
  rcases family_descends (prefixWord ++ tailWord_677989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678006 : List Nat := [5, 1, 1, 2, 1, 3, 3, 5]
def baseStart_678006 : Nat := 118140960795 + 678006 * 2 ^ 59
def prefixEnd_678006 : Nat := 4983230072969 + 3 ^ 40 * 678006 * 2
def baseEnd_678006 : Nat := 51576735501093264015839

theorem tailTrace_678006 : CollatzResearch.WordTrace tailWord_678006 prefixEnd_678006 51576735501093264015839 := by
  unfold tailWord_678006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545556898856720690691367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16485940254471687367374581 1545556898856720690691367)
  ·
    refine ⟨2318335348285081036037051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545556898856720690691367 2318335348285081036037051)
    ·
      refine ⟨3477503022427621554055577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318335348285081036037051 3477503022427621554055577)
      ·
        refine ⟨2608127266820716165541683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3477503022427621554055577 2608127266820716165541683)
        ·
          refine ⟨3912190900231074248312525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608127266820716165541683 3912190900231074248312525)
          ·
            refine ⟨1467071587586652843117197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3912190900231074248312525 1467071587586652843117197)
            ·
              refine ⟨550151845344994816168949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1467071587586652843117197 550151845344994816168949)
              ·
                refine ⟨51576735501093264015839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 550151845344994816168949 51576735501093264015839)
                ·
                  rfl

theorem cell21_678006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_678006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678006 prefixEnd_678006 := by exact prefixLift 678006
  have htrace : WordTrace (prefixWord ++ tailWord_678006) baseStart_678006 baseEnd_678006 := by
    simpa [prefixWord, tailWord_678006, baseEnd_678006] using wordTrace_append hprefix tailTrace_678006
  have hstable : (prefixWord ++ tailWord_678006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678006).length < 2 ^ (prefixWord ++ tailWord_678006).sum := by decide
  have hdescent : baseEnd_678006 < baseStart_678006 := by decide
  rcases family_descends (prefixWord ++ tailWord_678006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678034 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_678034 : Nat := 118140960795 + 678034 * 2 ^ 59
def prefixEnd_678034 : Nat := 4983230072969 + 3 ^ 40 * 678034 * 2
def baseEnd_678034 : Nat := 154736596484757965580793

theorem tailTrace_678034 : CollatzResearch.WordTrace tailWord_678034 prefixEnd_678034 154736596484757965580793 := by
  unfold tailWord_678034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182482906401522958270289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16486621083737394555387437 6182482906401522958270289)
  ·
    refine ⟨4636862179801142218702717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6182482906401522958270289 4636862179801142218702717)
    ·
      refine ⟨1738823317425428332013519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4636862179801142218702717 1738823317425428332013519)
      ·
        refine ⟨2608234976138142498020279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738823317425428332013519 2608234976138142498020279)
        ·
          refine ⟨3912352464207213747030419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608234976138142498020279 3912352464207213747030419)
          ·
            refine ⟨5868528696310820620545629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912352464207213747030419 5868528696310820620545629)
            ·
              refine ⟨2200698261116557732704611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5868528696310820620545629 2200698261116557732704611)
              ·
                refine ⟨3301047391674836599056917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200698261116557732704611 3301047391674836599056917)
                ·
                  refine ⟨154736596484757965580793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3301047391674836599056917 154736596484757965580793)
                  ·
                    rfl

theorem cell21_678034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_678034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678034 prefixEnd_678034 := by exact prefixLift 678034
  have htrace : WordTrace (prefixWord ++ tailWord_678034) baseStart_678034 baseEnd_678034 := by
    simpa [prefixWord, tailWord_678034, baseEnd_678034] using wordTrace_append hprefix tailTrace_678034
  have hstable : (prefixWord ++ tailWord_678034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678034).length < 2 ^ (prefixWord ++ tailWord_678034).sum := by decide
  have hdescent : baseEnd_678034 < baseStart_678034 := by decide
  rcases family_descends (prefixWord ++ tailWord_678034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678065 : List Nat := [1, 2, 2, 5, 2, 1, 1, 7]
def baseStart_678065 : Nat := 118140960795 + 678065 * 2 ^ 59
def prefixEnd_678065 : Nat := 4983230072969 + 3 ^ 40 * 678065 * 2
def baseEnd_678065 : Nat := 51581223702369600188021

theorem tailTrace_678065 : CollatzResearch.WordTrace tailWord_678065 prefixEnd_678065 51581223702369600188021 := by
  unfold tailWord_678065
  simp only [CollatzResearch.WordTrace]
  refine ⟨24731062288493784127459649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16487374858995856084973099 24731062288493784127459649)
  ·
    refine ⟨18548296716370338095594737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24731062288493784127459649 18548296716370338095594737)
    ·
      refine ⟨13911222537277753571696053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18548296716370338095594737 13911222537277753571696053)
      ·
        refine ⟨1304177112869789397346505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13911222537277753571696053 1304177112869789397346505)
        ·
          refine ⟨978132834652342048009879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304177112869789397346505 978132834652342048009879)
          ·
            refine ⟨1467199251978513072014819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978132834652342048009879 1467199251978513072014819)
            ·
              refine ⟨2200798877967769608022229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467199251978513072014819 2200798877967769608022229)
              ·
                refine ⟨51581223702369600188021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2200798877967769608022229 51581223702369600188021)
                ·
                  rfl

theorem cell21_678065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 7].length) (baseStart_678065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678065 prefixEnd_678065 := by exact prefixLift 678065
  have htrace : WordTrace (prefixWord ++ tailWord_678065) baseStart_678065 baseEnd_678065 := by
    simpa [prefixWord, tailWord_678065, baseEnd_678065] using wordTrace_append hprefix tailTrace_678065
  have hstable : (prefixWord ++ tailWord_678065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678065).length < 2 ^ (prefixWord ++ tailWord_678065).sum := by decide
  have hdescent : baseEnd_678065 < baseStart_678065 := by decide
  rcases family_descends (prefixWord ++ tailWord_678065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678082 : List Nat := [3, 5, 1, 1, 1, 1, 9]
def baseStart_678082 : Nat := 118140960795 + 678082 * 2 ^ 59
def prefixEnd_678082 : Nat := 4983230072969 + 3 ^ 40 * 678082 * 2
def baseEnd_678082 : Nat := 17194172304302283197855

theorem tailTrace_678082 : CollatzResearch.WordTrace tailWord_678082 prefixEnd_678082 17194172304302283197855 := by
  unfold tailWord_678082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182920582358049007707125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16487788219621464020552333 6182920582358049007707125)
  ·
    refine ⟨579648804596067094472543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6182920582358049007707125 579648804596067094472543)
    ·
      refine ⟨869473206894100641708815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579648804596067094472543 869473206894100641708815)
      ·
        refine ⟨1304209810341150962563223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869473206894100641708815 1304209810341150962563223)
        ·
          refine ⟨1956314715511726443844835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304209810341150962563223 1956314715511726443844835)
          ·
            refine ⟨2934472073267589665767253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956314715511726443844835 2934472073267589665767253)
            ·
              refine ⟨17194172304302283197855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2934472073267589665767253 17194172304302283197855)
              ·
                rfl

theorem cell21_678082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 9].length) (baseStart_678082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678082 prefixEnd_678082 := by exact prefixLift 678082
  have htrace : WordTrace (prefixWord ++ tailWord_678082) baseStart_678082 baseEnd_678082 := by
    simpa [prefixWord, tailWord_678082, baseEnd_678082] using wordTrace_append hprefix tailTrace_678082
  have hstable : (prefixWord ++ tailWord_678082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678082).length < 2 ^ (prefixWord ++ tailWord_678082).sum := by decide
  have hdescent : baseEnd_678082 < baseStart_678082 := by decide
  rcases family_descends (prefixWord ++ tailWord_678082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678107 : List Nat := [1, 1, 1, 1, 1, 1, 1, 14]
def baseStart_678107 : Nat := 118140960795 + 678107 * 2 ^ 59
def prefixEnd_678107 : Nat := 4983230072969 + 3 ^ 40 * 678107 * 2
def baseEnd_678107 : Nat := 51584418693108686954659

theorem tailTrace_678107 : CollatzResearch.WordTrace tailWord_678107 prefixEnd_678107 51584418693108686954659 := by
  unfold tailWord_678107
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732594154341625300488575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16488396102894416866992383 24732594154341625300488575)
  ·
    refine ⟨37098891231512437950732863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24732594154341625300488575 37098891231512437950732863)
    ·
      refine ⟨55648336847268656926099295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37098891231512437950732863 55648336847268656926099295)
      ·
        refine ⟨83472505270902985389148943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55648336847268656926099295 83472505270902985389148943)
        ·
          refine ⟨125208757906354478083723415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83472505270902985389148943 125208757906354478083723415)
          ·
            refine ⟨187813136859531717125585123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125208757906354478083723415 187813136859531717125585123)
            ·
              refine ⟨281719705289297575688377685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187813136859531717125585123 281719705289297575688377685)
              ·
                refine ⟨51584418693108686954659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 281719705289297575688377685 51584418693108686954659)
                ·
                  rfl

theorem cell21_678107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_678107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678107 prefixEnd_678107 := by exact prefixLift 678107
  have htrace : WordTrace (prefixWord ++ tailWord_678107) baseStart_678107 baseEnd_678107 := by
    simpa [prefixWord, tailWord_678107, baseEnd_678107] using wordTrace_append hprefix tailTrace_678107
  have hstable : (prefixWord ++ tailWord_678107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678107).length < 2 ^ (prefixWord ++ tailWord_678107).sum := by decide
  have hdescent : baseEnd_678107 < baseStart_678107 := by decide
  rcases family_descends (prefixWord ++ tailWord_678107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678245 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_678245 : Nat := 118140960795 + 678245 * 2 ^ 59
def prefixEnd_678245 : Nat := 4983230072969 + 3 ^ 40 * 678245 * 2
def baseEnd_678245 : Nat := 154784749559468487563695

theorem tailTrace_678245 : CollatzResearch.WordTrace tailWord_678245 prefixEnd_678245 154784749559468487563695 := by
  unfold tailWord_678245
  simp only [CollatzResearch.WordTrace]
  refine ⟨24737627427841674869012189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16491751618561116579341459 24737627427841674869012189)
  ·
    refine ⟨9276610285440628075879571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24737627427841674869012189 9276610285440628075879571)
    ·
      refine ⟨13914915428160942113819357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9276610285440628075879571 13914915428160942113819357)
      ·
        refine ⟨5218093285560353292682259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13914915428160942113819357 5218093285560353292682259)
        ·
          refine ⟨7827139928340529939023389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218093285560353292682259 7827139928340529939023389)
          ·
            refine ⟨2935177473127698727133771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7827139928340529939023389 2935177473127698727133771)
            ·
              refine ⟨4402766209691548090700657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935177473127698727133771 4402766209691548090700657)
              ·
                refine ⟨3302074657268661068025493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4402766209691548090700657 3302074657268661068025493)
                ·
                  refine ⟨154784749559468487563695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3302074657268661068025493 154784749559468487563695)
                  ·
                    rfl

theorem cell21_678245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_678245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678245 prefixEnd_678245 := by exact prefixLift 678245
  have htrace : WordTrace (prefixWord ++ tailWord_678245) baseStart_678245 baseEnd_678245 := by
    simpa [prefixWord, tailWord_678245, baseEnd_678245] using wordTrace_append hprefix tailTrace_678245
  have hstable : (prefixWord ++ tailWord_678245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678245).length < 2 ^ (prefixWord ++ tailWord_678245).sum := by decide
  have hdescent : baseEnd_678245 < baseStart_678245 := by decide
  rcases family_descends (prefixWord ++ tailWord_678245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678276 : List Nat := [2, 3, 2, 1, 1, 2, 4, 6]
def baseStart_678276 : Nat := 118140960795 + 678276 * 2 ^ 59
def prefixEnd_678276 : Nat := 4983230072969 + 3 ^ 40 * 678276 * 2
def baseEnd_678276 : Nat := 51597274727273107515655

theorem tailTrace_678276 : CollatzResearch.WordTrace tailWord_678276 prefixEnd_678276 51597274727273107515655 := by
  unfold tailWord_678276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369379045364683581695341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16492505393819578108927121 12369379045364683581695341)
  ·
    refine ⟨4638517142011756343135753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12369379045364683581695341 4638517142011756343135753)
    ·
      refine ⟨3478887856508817257351815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638517142011756343135753 3478887856508817257351815)
      ·
        refine ⟨5218331784763225886027723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3478887856508817257351815 5218331784763225886027723)
        ·
          refine ⟨7827497677144838829041585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218331784763225886027723 7827497677144838829041585)
          ·
            refine ⟨5870623257858629121781189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7827497677144838829041585 5870623257858629121781189)
            ·
              refine ⟨1100741860848492960333973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5870623257858629121781189 1100741860848492960333973)
              ·
                refine ⟨51597274727273107515655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1100741860848492960333973 51597274727273107515655)
                ·
                  rfl

theorem cell21_678276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_678276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678276 prefixEnd_678276 := by exact prefixLift 678276
  have htrace : WordTrace (prefixWord ++ tailWord_678276) baseStart_678276 baseEnd_678276 := by
    simpa [prefixWord, tailWord_678276, baseEnd_678276] using wordTrace_append hprefix tailTrace_678276
  have hstable : (prefixWord ++ tailWord_678276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678276).length < 2 ^ (prefixWord ++ tailWord_678276).sum := by decide
  have hdescent : baseEnd_678276 < baseStart_678276 := by decide
  rcases family_descends (prefixWord ++ tailWord_678276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678428 : List Nat := [2, 2, 3, 1, 2, 4, 7]
def baseStart_678428 : Nat := 118140960795 + 678428 * 2 ^ 59
def prefixEnd_678428 : Nat := 4983230072969 + 3 ^ 40 * 678428 * 2
def baseEnd_678428 : Nat := 17202945850300092890369

theorem tailTrace_678428 : CollatzResearch.WordTrace tailWord_678428 prefixEnd_678428 17202945850300092890369 := by
  unfold tailWord_678428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12372150993089348561461969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16496201324119131415282625 12372150993089348561461969)
  ·
    refine ⟨9279113244817011421096477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12372150993089348561461969 9279113244817011421096477)
    ·
      refine ⟨3479667466806379282911179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9279113244817011421096477 3479667466806379282911179)
      ·
        refine ⟨5219501200209568924366769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479667466806379282911179 5219501200209568924366769)
        ·
          refine ⟨3914625900157176693275077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219501200209568924366769 3914625900157176693275077)
          ·
            refine ⟨733992356279470629989077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3914625900157176693275077 733992356279470629989077)
            ·
              refine ⟨17202945850300092890369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 733992356279470629989077 17202945850300092890369)
              ·
                rfl

theorem cell21_678428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 7].length) (baseStart_678428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678428 prefixEnd_678428 := by exact prefixLift 678428
  have htrace : WordTrace (prefixWord ++ tailWord_678428) baseStart_678428 baseEnd_678428 := by
    simpa [prefixWord, tailWord_678428, baseEnd_678428] using wordTrace_append hprefix tailTrace_678428
  have hstable : (prefixWord ++ tailWord_678428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678428).length < 2 ^ (prefixWord ++ tailWord_678428).sum := by decide
  have hdescent : baseEnd_678428 < baseStart_678428 := by decide
  rcases family_descends (prefixWord ++ tailWord_678428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678639 : List Nat := [1, 1, 2, 1, 5, 2, 2, 7]
def baseStart_678639 : Nat := 118140960795 + 678639 * 2 ^ 59
def prefixEnd_678639 : Nat := 4983230072969 + 3 ^ 40 * 678639 * 2
def baseEnd_678639 : Nat := 51624888575803785998741

theorem tailTrace_678639 : CollatzResearch.WordTrace tailWord_678639 prefixEnd_678639 51624888575803785998741 := by
  unfold tailWord_678639
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751997788414280158854971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16501331858942853439236647 24751997788414280158854971)
  ·
    refine ⟨37127996682621420238282457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24751997788414280158854971 37127996682621420238282457)
    ·
      refine ⟨27845997511966065178711843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37127996682621420238282457 27845997511966065178711843)
      ·
        refine ⟨41768996267949097768067765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27845997511966065178711843 41768996267949097768067765)
        ·
          refine ⟨3915843400120227915756353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41768996267949097768067765 3915843400120227915756353)
          ·
            refine ⟨2936882550090170936817265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915843400120227915756353 2936882550090170936817265)
            ·
              refine ⟨2202661912567628202612949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936882550090170936817265 2202661912567628202612949)
              ·
                refine ⟨51624888575803785998741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2202661912567628202612949 51624888575803785998741)
                ·
                  rfl

theorem cell21_678639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_678639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678639 prefixEnd_678639 := by exact prefixLift 678639
  have htrace : WordTrace (prefixWord ++ tailWord_678639) baseStart_678639 baseEnd_678639 := by
    simpa [prefixWord, tailWord_678639, baseEnd_678639] using wordTrace_append hprefix tailTrace_678639
  have hstable : (prefixWord ++ tailWord_678639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678639).length < 2 ^ (prefixWord ++ tailWord_678639).sum := by decide
  have hdescent : baseEnd_678639 < baseStart_678639 := by decide
  rcases family_descends (prefixWord ++ tailWord_678639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678670 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_678670 : Nat := 118140960795 + 678670 * 2 ^ 59
def prefixEnd_678670 : Nat := 4983230072969 + 3 ^ 40 * 678670 * 2
def baseEnd_678670 : Nat := 154881740349762192979493

theorem tailTrace_678670 : CollatzResearch.WordTrace tailWord_678670 prefixEnd_678670 154881740349762192979493 := by
  unfold tailWord_678670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094141056412746556654183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16502085634201314968822309 3094141056412746556654183)
  ·
    refine ⟨4641211584619119834981275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3094141056412746556654183 4641211584619119834981275)
    ·
      refine ⟨6961817376928679752471913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641211584619119834981275 6961817376928679752471913)
      ·
        refine ⟨5221363032696509814353935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6961817376928679752471913 5221363032696509814353935)
        ·
          refine ⟨7832044549044764721530903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221363032696509814353935 7832044549044764721530903)
          ·
            refine ⟨11748066823567147082296355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832044549044764721530903 11748066823567147082296355)
            ·
              refine ⟨17622100235350720623444533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11748066823567147082296355 17622100235350720623444533)
              ·
                refine ⟨1652071897064130058447925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17622100235350720623444533 1652071897064130058447925)
                ·
                  refine ⟨154881740349762192979493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652071897064130058447925 154881740349762192979493)
                  ·
                    rfl

theorem cell21_678670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_678670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678670 prefixEnd_678670 := by exact prefixLift 678670
  have htrace : WordTrace (prefixWord ++ tailWord_678670) baseStart_678670 baseEnd_678670 := by
    simpa [prefixWord, tailWord_678670, baseEnd_678670] using wordTrace_append hprefix tailTrace_678670
  have hstable : (prefixWord ++ tailWord_678670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678670).length < 2 ^ (prefixWord ++ tailWord_678670).sum := by decide
  have hdescent : baseEnd_678670 < baseStart_678670 := by decide
  rcases family_descends (prefixWord ++ tailWord_678670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678718 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_678718 : Nat := 118140960795 + 678718 * 2 ^ 59
def prefixEnd_678718 : Nat := 4983230072969 + 3 ^ 40 * 678718 * 2
def baseEnd_678718 : Nat := 154892694603724776179395

theorem tailTrace_678718 : CollatzResearch.WordTrace tailWord_678718 prefixEnd_678718 154892694603724776179395 := by
  unfold tailWord_678718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094359894391009581372601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16503252770085384433987205 3094359894391009581372601)
  ·
    refine ⟨2320769920793257186029451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3094359894391009581372601 2320769920793257186029451)
    ·
      refine ⟨3481154881189885779044177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320769920793257186029451 3481154881189885779044177)
      ·
        refine ⟨2610866160892414334283133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3481154881189885779044177 2610866160892414334283133)
        ·
          refine ⟨979074810334655375356175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2610866160892414334283133 979074810334655375356175)
          ·
            refine ⟨1468612215501983063034263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979074810334655375356175 1468612215501983063034263)
            ·
              refine ⟨2202918323252974594551395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468612215501983063034263 2202918323252974594551395)
              ·
                refine ⟨3304377484879461891827093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202918323252974594551395 3304377484879461891827093)
                ·
                  refine ⟨154892694603724776179395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3304377484879461891827093 154892694603724776179395)
                  ·
                    rfl

theorem cell21_678718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_678718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678718 prefixEnd_678718 := by exact prefixLift 678718
  have htrace : WordTrace (prefixWord ++ tailWord_678718) baseStart_678718 baseEnd_678718 := by
    simpa [prefixWord, tailWord_678718, baseEnd_678718] using wordTrace_append hprefix tailTrace_678718
  have hstable : (prefixWord ++ tailWord_678718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678718).length < 2 ^ (prefixWord ++ tailWord_678718).sum := by decide
  have hdescent : baseEnd_678718 < baseStart_678718 := by decide
  rcases family_descends (prefixWord ++ tailWord_678718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678746 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_678746 : Nat := 118140960795 + 678746 * 2 ^ 59
def prefixEnd_678746 : Nat := 4983230072969 + 3 ^ 40 * 678746 * 2
def baseEnd_678746 : Nat := 154899084585202949712671

theorem tailTrace_678746 : CollatzResearch.WordTrace tailWord_678746 prefixEnd_678746 154899084585202949712671 := by
  unfold tailWord_678746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188975099756659358250023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16503933599351091622000061 6188975099756659358250023)
  ·
    refine ⟨9283462649634989037375035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6188975099756659358250023 9283462649634989037375035)
    ·
      refine ⟨13925193974452483556062553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9283462649634989037375035 13925193974452483556062553)
      ·
        refine ⟨10443895480839362667046915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13925193974452483556062553 10443895480839362667046915)
        ·
          refine ⟨15665843221259044000570373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10443895480839362667046915 15665843221259044000570373)
          ·
            refine ⟨2937345603986070750106945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15665843221259044000570373 2937345603986070750106945)
            ·
              refine ⟨2203009202989553062580209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2937345603986070750106945 2203009202989553062580209)
              ·
                refine ⟨1652256902242164796935157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203009202989553062580209 1652256902242164796935157)
                ·
                  refine ⟨154899084585202949712671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652256902242164796935157 154899084585202949712671)
                  ·
                    rfl

theorem cell21_678746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_678746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678746 prefixEnd_678746 := by exact prefixLift 678746
  have htrace : WordTrace (prefixWord ++ tailWord_678746) baseStart_678746 baseEnd_678746 := by
    simpa [prefixWord, tailWord_678746, baseEnd_678746] using wordTrace_append hprefix tailTrace_678746
  have hstable : (prefixWord ++ tailWord_678746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678746).length < 2 ^ (prefixWord ++ tailWord_678746).sum := by decide
  have hdescent : baseEnd_678746 < baseStart_678746 := by decide
  rcases family_descends (prefixWord ++ tailWord_678746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678763 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 3]
def baseStart_678763 : Nat := 118140960795 + 678763 * 2 ^ 59
def prefixEnd_678763 : Nat := 4983230072969 + 3 ^ 40 * 678763 * 2
def baseEnd_678763 : Nat := 154902964216814697929303

theorem tailTrace_678763 : CollatzResearch.WordTrace tailWord_678763 prefixEnd_678763 154902964216814697929303 := by
  unfold tailWord_678763
  simp only [CollatzResearch.WordTrace]
  refine ⟨24756520439965049336368943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16504346959976699557579295 24756520439965049336368943)
  ·
    refine ⟨37134780659947574004553415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24756520439965049336368943 37134780659947574004553415)
    ·
      refine ⟨55702170989921361006830123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37134780659947574004553415 55702170989921361006830123)
      ·
        refine ⟨83553256484882041510245185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55702170989921361006830123 83553256484882041510245185)
        ·
          refine ⟨62664942363661531132683889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83553256484882041510245185 62664942363661531132683889)
          ·
            refine ⟨46998706772746148349512917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62664942363661531132683889 46998706772746148349512917)
            ·
              refine ⟨1101532189986237851941709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46998706772746148349512917 1101532189986237851941709)
              ·
                refine ⟨413074571244839194478141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1101532189986237851941709 413074571244839194478141)
                ·
                  refine ⟨154902964216814697929303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413074571244839194478141 154902964216814697929303)
                  ·
                    rfl

theorem cell21_678763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 3].length) (baseStart_678763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678763 prefixEnd_678763 := by exact prefixLift 678763
  have htrace : WordTrace (prefixWord ++ tailWord_678763) baseStart_678763 baseEnd_678763 := by
    simpa [prefixWord, tailWord_678763, baseEnd_678763] using wordTrace_append hprefix tailTrace_678763
  have hstable : (prefixWord ++ tailWord_678763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678763).length < 2 ^ (prefixWord ++ tailWord_678763).sum := by decide
  have hdescent : baseEnd_678763 < baseStart_678763 := by decide
  rcases family_descends (prefixWord ++ tailWord_678763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678786 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_678786 : Nat := 118140960795 + 678786 * 2 ^ 59
def prefixEnd_678786 : Nat := 4983230072969 + 3 ^ 40 * 678786 * 2
def baseEnd_678786 : Nat := 154908213130171769045923

theorem tailTrace_678786 : CollatzResearch.WordTrace tailWord_678786 prefixEnd_678786 154908213130171769045923 := by
  unfold tailWord_678786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189339829720431066114053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16504906212587816176304141 6189339829720431066114053)
  ·
    refine ⟨1160501218072580824896385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6189339829720431066114053 1160501218072580824896385)
    ·
      refine ⟨870375913554435618672289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1160501218072580824896385 870375913554435618672289)
      ·
        refine ⟨652781935165826714004217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870375913554435618672289 652781935165826714004217)
        ·
          refine ⟨489586451374370035503163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652781935165826714004217 489586451374370035503163)
          ·
            refine ⟨734379677061555053254745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489586451374370035503163 734379677061555053254745)
            ·
              refine ⟨550784757796166289941059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734379677061555053254745 550784757796166289941059)
              ·
                refine ⟨826177136694249434911589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550784757796166289941059 826177136694249434911589)
                ·
                  refine ⟨154908213130171769045923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826177136694249434911589 154908213130171769045923)
                  ·
                    rfl

theorem cell21_678786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_678786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678786 prefixEnd_678786 := by exact prefixLift 678786
  have htrace : WordTrace (prefixWord ++ tailWord_678786) baseStart_678786 baseEnd_678786 := by
    simpa [prefixWord, tailWord_678786, baseEnd_678786] using wordTrace_append hprefix tailTrace_678786
  have hstable : (prefixWord ++ tailWord_678786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678786).length < 2 ^ (prefixWord ++ tailWord_678786).sum := by decide
  have hdescent : baseEnd_678786 < baseStart_678786 := by decide
  rcases family_descends (prefixWord ++ tailWord_678786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678791 : List Nat := [1, 1, 4, 2, 3, 1, 1, 8]
def baseStart_678791 : Nat := 118140960795 + 678791 * 2 ^ 59
def prefixEnd_678791 : Nat := 4983230072969 + 3 ^ 40 * 678791 * 2
def baseEnd_678791 : Nat := 51636451399430957154193

theorem tailTrace_678791 : CollatzResearch.WordTrace tailWord_678791 prefixEnd_678791 51636451399430957154193 := by
  unfold tailWord_678791
  simp only [CollatzResearch.WordTrace]
  refine ⟨24757541683863610118388227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16505027789242406745592151 24757541683863610118388227)
  ·
    refine ⟨37136312525795415177582341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24757541683863610118388227 37136312525795415177582341)
    ·
      refine ⟨6963058598586640345796689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37136312525795415177582341 6963058598586640345796689)
      ·
        refine ⟨5222293948939980259347517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6963058598586640345796689 5222293948939980259347517)
        ·
          refine ⟨1958360230852492597255319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5222293948939980259347517 1958360230852492597255319)
          ·
            refine ⟨2937540346278738895882979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958360230852492597255319 2937540346278738895882979)
            ·
              refine ⟨4406310519418108343824469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937540346278738895882979 4406310519418108343824469)
              ·
                refine ⟨51636451399430957154193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4406310519418108343824469 51636451399430957154193)
                ·
                  rfl

theorem cell21_678791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_678791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_678791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_678791 prefixEnd_678791 := by exact prefixLift 678791
  have htrace : WordTrace (prefixWord ++ tailWord_678791) baseStart_678791 baseEnd_678791 := by
    simpa [prefixWord, tailWord_678791, baseEnd_678791] using wordTrace_append hprefix tailTrace_678791
  have hstable : (prefixWord ++ tailWord_678791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678791).length < 2 ^ (prefixWord ++ tailWord_678791).sum := by decide
  have hdescent : baseEnd_678791 < baseStart_678791 := by decide
  rcases family_descends (prefixWord ++ tailWord_678791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
