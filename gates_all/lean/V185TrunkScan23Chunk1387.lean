import V185TrunkScan23Chunk1386

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8215117 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 5]
def baseStart_8215117 : Nat := 118140960795 + 8215117 * 2 ^ 59
def prefixEnd_8215117 : Nat := 4983230072969 + 3 ^ 40 * 8215117 * 2
def baseEnd_8215117 : Nat := 468700405991337783406319

theorem tailTrace_8215117 : CollatzResearch.WordTrace tailWord_8215117 prefixEnd_8215117 468700405991337783406319 := by
  unfold tailWord_8215117
  simp only [CollatzResearch.WordTrace]
  refine ⟨299629932579041614127763605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199753288386027742751842403 299629932579041614127763605)
  ·
    refine ⟨14045153089642575662238919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 299629932579041614127763605 14045153089642575662238919)
    ·
      refine ⟨21067729634463863493358379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14045153089642575662238919 21067729634463863493358379)
      ·
        refine ⟨31601594451695795240037569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21067729634463863493358379 31601594451695795240037569)
        ·
          refine ⟨23701195838771846430028177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31601594451695795240037569 23701195838771846430028177)
          ·
            refine ⟨17775896879078884822521133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23701195838771846430028177 17775896879078884822521133)
            ·
              refine ⟨6665961329654581808445425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17775896879078884822521133 6665961329654581808445425)
              ·
                refine ⟨4999470997240936356334069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665961329654581808445425 4999470997240936356334069)
                ·
                  refine ⟨468700405991337783406319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4999470997240936356334069 468700405991337783406319)
                  ·
                    rfl

theorem cell23_8215117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_8215117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215117 prefixEnd_8215117 := by exact prefixLift 8215117
  have htrace : WordTrace (prefixWord ++ tailWord_8215117) baseStart_8215117 baseEnd_8215117 := by
    simpa [prefixWord, tailWord_8215117, baseEnd_8215117] using wordTrace_append hprefix tailTrace_8215117
  have hstable : (prefixWord ++ tailWord_8215117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215117).length < 2 ^ (prefixWord ++ tailWord_8215117).sum := by decide
  have hdescent : baseEnd_8215117 < baseStart_8215117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215136 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_8215136 : Nat := 118140960795 + 8215136 * 2 ^ 59
def prefixEnd_8215136 : Nat := 4983230072969 + 3 ^ 40 * 8215136 * 2
def baseEnd_8215136 : Nat := 4218313410054475476319283

theorem tailTrace_8215136 : CollatzResearch.WordTrace tailWord_8215136 prefixEnd_8215136 4218313410054475476319283 := by
  unfold tailWord_8215136
  simp only [CollatzResearch.WordTrace]
  refine ⟨149815312782986390186352631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199753750377315186915136841 149815312782986390186352631)
  ·
    refine ⟨224722969174479585279528947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149815312782986390186352631 224722969174479585279528947)
    ·
      refine ⟨337084453761719377919293421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224722969174479585279528947 337084453761719377919293421)
      ·
        refine ⟨126406670160644766719735033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337084453761719377919293421 126406670160644766719735033)
        ·
          refine ⟨94805002620483575039801275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126406670160644766719735033 94805002620483575039801275)
          ·
            refine ⟨142207503930725362559701913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94805002620483575039801275 142207503930725362559701913)
            ·
              refine ⟨106655627948044021919776435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142207503930725362559701913 106655627948044021919776435)
              ·
                refine ⟨159983441922066032879664653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106655627948044021919776435 159983441922066032879664653)
                ·
                  refine ⟨59993790720774762329874245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159983441922066032879664653 59993790720774762329874245)
                  ·
                    refine ⟨11248835760145267936851421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59993790720774762329874245 11248835760145267936851421)
                    ·
                      refine ⟨4218313410054475476319283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11248835760145267936851421 4218313410054475476319283)
                      ·
                        rfl

theorem cell23_8215136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_8215136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215136 prefixEnd_8215136 := by exact prefixLift 8215136
  have htrace : WordTrace (prefixWord ++ tailWord_8215136) baseStart_8215136 baseEnd_8215136 := by
    simpa [prefixWord, tailWord_8215136, baseEnd_8215136] using wordTrace_append hprefix tailTrace_8215136
  have hstable : (prefixWord ++ tailWord_8215136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215136).length < 2 ^ (prefixWord ++ tailWord_8215136).sum := by decide
  have hdescent : baseEnd_8215136 < baseStart_8215136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215150 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_8215150 : Nat := 118140960795 + 8215150 * 2 ^ 59
def prefixEnd_8215150 : Nat := 4983230072969 + 3 ^ 40 * 8215150 * 2
def baseEnd_8215150 : Nat := 4218320598783638421544219

theorem tailTrace_8215150 : CollatzResearch.WordTrace tailWord_8215150 prefixEnd_8215150 4218320598783638421544219 := by
  unfold tailWord_8215150
  simp only [CollatzResearch.WordTrace]
  refine ⟨37453892023490257595464363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199754090791948040509143269 37453892023490257595464363)
  ·
    refine ⟨56180838035235386393196545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37453892023490257595464363 56180838035235386393196545)
    ·
      refine ⟨42135628526426539794897409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56180838035235386393196545 42135628526426539794897409)
      ·
        refine ⟨31601721394819904846173057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42135628526426539794897409 31601721394819904846173057)
        ·
          refine ⟨23701291046114928634629793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31601721394819904846173057 23701291046114928634629793)
          ·
            refine ⟨17775968284586196475972345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23701291046114928634629793 17775968284586196475972345)
            ·
              refine ⟨13331976213439647356979259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17775968284586196475972345 13331976213439647356979259)
              ·
                refine ⟨19997964320159471035468889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13331976213439647356979259 19997964320159471035468889)
                ·
                  refine ⟨14998473240119603276601667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19997964320159471035468889 14998473240119603276601667)
                  ·
                    refine ⟨22497709860179404914902501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14998473240119603276601667 22497709860179404914902501)
                    ·
                      refine ⟨4218320598783638421544219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22497709860179404914902501 4218320598783638421544219)
                      ·
                        rfl

theorem cell23_8215150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_8215150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215150 prefixEnd_8215150 := by exact prefixLift 8215150
  have htrace : WordTrace (prefixWord ++ tailWord_8215150) baseStart_8215150 baseEnd_8215150 := by
    simpa [prefixWord, tailWord_8215150, baseEnd_8215150] using wordTrace_append hprefix tailTrace_8215150
  have hstable : (prefixWord ++ tailWord_8215150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215150).length < 2 ^ (prefixWord ++ tailWord_8215150).sum := by decide
  have hdescent : baseEnd_8215150 < baseStart_8215150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215173 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 6]
def baseStart_8215173 : Nat := 118140960795 + 8215173 * 2 ^ 59
def prefixEnd_8215173 : Nat := 4983230072969 + 3 ^ 40 * 8215173 * 2
def baseEnd_8215173 : Nat := 468703600982076870172957

theorem tailTrace_8215173 : CollatzResearch.WordTrace tailWord_8215173 prefixEnd_8215173 468703600982076870172957 := by
  unfold tailWord_8215173
  simp only [CollatzResearch.WordTrace]
  refine ⟨299631975066838735691802173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199754650044559157127868115 299631975066838735691802173)
  ·
    refine ⟨112361990650064525884425815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299631975066838735691802173 112361990650064525884425815)
    ·
      refine ⟨168542985975096788826638723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112361990650064525884425815 168542985975096788826638723)
      ·
        refine ⟨252814478962645183239958085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168542985975096788826638723 252814478962645183239958085)
        ·
          refine ⟨47402714805495971857492141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252814478962645183239958085 47402714805495971857492141)
          ·
            refine ⟨17776018052060989446559553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47402714805495971857492141 17776018052060989446559553)
            ·
              refine ⟨13332013539045742084919665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17776018052060989446559553 13332013539045742084919665)
              ·
                refine ⟨9999010154284306563689749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13332013539045742084919665 9999010154284306563689749)
                ·
                  refine ⟨468703600982076870172957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9999010154284306563689749 468703600982076870172957)
                  ·
                    rfl

theorem cell23_8215173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_8215173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215173 prefixEnd_8215173 := by exact prefixLift 8215173
  have htrace : WordTrace (prefixWord ++ tailWord_8215173) baseStart_8215173 baseEnd_8215173 := by
    simpa [prefixWord, tailWord_8215173, baseEnd_8215173] using wordTrace_append hprefix tailTrace_8215173
  have hstable : (prefixWord ++ tailWord_8215173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215173).length < 2 ^ (prefixWord ++ tailWord_8215173).sum := by decide
  have hdescent : baseEnd_8215173 < baseStart_8215173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215193 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 1, 5, 2]
def baseStart_8215193 : Nat := 118140960795 + 8215193 * 2 ^ 59
def prefixEnd_8215193 : Nat := 4983230072969 + 3 ^ 40 * 8215193 * 2
def baseEnd_8215193 : Nat := 4218342678451781753306521

theorem tailTrace_8215193 : CollatzResearch.WordTrace tailWord_8215193 prefixEnd_8215193 4218342678451781753306521 := by
  unfold tailWord_8215193
  simp only [CollatzResearch.WordTrace]
  refine ⟨299632704526766279107530233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199755136351177519405020155 299632704526766279107530233)
  ·
    refine ⟨224724528395074709330647675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299632704526766279107530233 224724528395074709330647675)
    ·
      refine ⟨337086792592612063995971513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224724528395074709330647675 337086792592612063995971513)
      ·
        refine ⟨252815094444459047996978635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337086792592612063995971513 252815094444459047996978635)
        ·
          refine ⟨379222641666688571995467953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252815094444459047996978635 379222641666688571995467953)
          ·
            refine ⟨284416981250016428996600965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379222641666688571995467953 284416981250016428996600965)
            ·
              refine ⟨53328183984378080436862681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284416981250016428996600965 53328183984378080436862681)
              ·
                refine ⟨39996137988283560327647011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53328183984378080436862681 39996137988283560327647011)
                ·
                  refine ⟨59994206982425340491470517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39996137988283560327647011 59994206982425340491470517)
                  ·
                    refine ⟨5624456904602375671075361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59994206982425340491470517 5624456904602375671075361)
                    ·
                      refine ⟨4218342678451781753306521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624456904602375671075361 4218342678451781753306521)
                      ·
                        rfl

theorem cell23_8215193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_8215193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215193 prefixEnd_8215193 := by exact prefixLift 8215193
  have htrace : WordTrace (prefixWord ++ tailWord_8215193) baseStart_8215193 baseEnd_8215193 := by
    simpa [prefixWord, tailWord_8215193, baseEnd_8215193] using wordTrace_append hprefix tailTrace_8215193
  have hstable : (prefixWord ++ tailWord_8215193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215193).length < 2 ^ (prefixWord ++ tailWord_8215193).sum := by decide
  have hdescent : baseEnd_8215193 < baseStart_8215193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215263 : List Nat := [1, 1, 2, 3, 2, 3, 4, 7]
def baseStart_8215263 : Nat := 118140960795 + 8215263 * 2 ^ 59
def prefixEnd_8215263 : Nat := 4983230072969 + 3 ^ 40 * 8215263 * 2
def baseEnd_8215263 : Nat := 156236245262873943682637

theorem tailTrace_8215263 : CollatzResearch.WordTrace tailWord_8215263 prefixEnd_8215263 156236245262873943682637 := by
  unfold tailWord_8215263
  simp only [CollatzResearch.WordTrace]
  refine ⟨299635257636512681062578443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199756838424341787375052295 299635257636512681062578443)
  ·
    refine ⟨449452886454769021593867665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299635257636512681062578443 449452886454769021593867665)
    ·
      refine ⟨337089664841076766195400749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449452886454769021593867665 337089664841076766195400749)
      ·
        refine ⟨126408624315403787323275281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337089664841076766195400749 126408624315403787323275281)
        ·
          refine ⟨94806468236552840492456461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126408624315403787323275281 94806468236552840492456461)
          ·
            refine ⟨35552425588707315184671173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94806468236552840492456461 35552425588707315184671173)
            ·
              refine ⟨6666079797882621597125845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35552425588707315184671173 6666079797882621597125845)
              ·
                refine ⟨156236245262873943682637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6666079797882621597125845 156236245262873943682637)
                ·
                  rfl

theorem cell23_8215263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 7].length) (baseStart_8215263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215263 prefixEnd_8215263 := by exact prefixLift 8215263
  have htrace : WordTrace (prefixWord ++ tailWord_8215263) baseStart_8215263 baseEnd_8215263 := by
    simpa [prefixWord, tailWord_8215263, baseEnd_8215263] using wordTrace_append hprefix tailTrace_8215263
  have hstable : (prefixWord ++ tailWord_8215263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215263).length < 2 ^ (prefixWord ++ tailWord_8215263).sum := by decide
  have hdescent : baseEnd_8215263 < baseStart_8215263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215273 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_8215273 : Nat := 118140960795 + 8215273 * 2 ^ 59
def prefixEnd_8215273 : Nat := 4983230072969 + 3 ^ 40 * 8215273 * 2
def baseEnd_8215273 : Nat := 4218383756904141440306153

theorem tailTrace_8215273 : CollatzResearch.WordTrace tailWord_8215273 prefixEnd_8215273 4218383756904141440306153 := by
  unfold tailWord_8215273
  simp only [CollatzResearch.WordTrace]
  refine ⟨299635622366476452770442473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199757081577650968513628315 299635622366476452770442473)
  ·
    refine ⟨224726716774857339577831855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299635622366476452770442473 224726716774857339577831855)
    ·
      refine ⟨337090075162286009366747783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224726716774857339577831855 337090075162286009366747783)
      ·
        refine ⟨505635112743429014050121675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337090075162286009366747783 505635112743429014050121675)
        ·
          refine ⟨758452669115143521075182513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505635112743429014050121675 758452669115143521075182513)
          ·
            refine ⟨568839501836357640806386885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758452669115143521075182513 568839501836357640806386885)
            ·
              refine ⟨106657406594317057651197541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568839501836357640806386885 106657406594317057651197541)
              ·
                refine ⟨19998263736434448309599539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106657406594317057651197541 19998263736434448309599539)
                ·
                  refine ⟨29997395604651672464399309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19998263736434448309599539 29997395604651672464399309)
                  ·
                    refine ⟨11249023351744377174149741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29997395604651672464399309 11249023351744377174149741)
                    ·
                      refine ⟨4218383756904141440306153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249023351744377174149741 4218383756904141440306153)
                      ·
                        rfl

theorem cell23_8215273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_8215273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215273 prefixEnd_8215273 := by exact prefixLift 8215273
  have htrace : WordTrace (prefixWord ++ tailWord_8215273) baseStart_8215273 baseEnd_8215273 := by
    simpa [prefixWord, tailWord_8215273, baseEnd_8215273] using wordTrace_append hprefix tailTrace_8215273
  have hstable : (prefixWord ++ tailWord_8215273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215273).length < 2 ^ (prefixWord ++ tailWord_8215273).sum := by decide
  have hdescent : baseEnd_8215273 < baseStart_8215273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215276 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_8215276 : Nat := 118140960795 + 8215276 * 2 ^ 59
def prefixEnd_8215276 : Nat := 4983230072969 + 3 ^ 40 * 8215276 * 2
def baseEnd_8215276 : Nat := 1406128432448701642856213

theorem tailTrace_8215276 : CollatzResearch.WordTrace tailWord_8215276 prefixEnd_8215276 1406128432448701642856213 := by
  unfold tailWord_8215276
  simp only [CollatzResearch.WordTrace]
  refine ⟨149817865892732792141400841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199757154523643722855201121 149817865892732792141400841)
  ·
    refine ⟨112363399419549594106050631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149817865892732792141400841 112363399419549594106050631)
    ·
      refine ⟨168545099129324391159075947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112363399419549594106050631 168545099129324391159075947)
      ·
        refine ⟨252817648693986586738613921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168545099129324391159075947 252817648693986586738613921)
        ·
          refine ⟨189613236520489940053960441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252817648693986586738613921 189613236520489940053960441)
          ·
            refine ⟨142209927390367455040470331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189613236520489940053960441 142209927390367455040470331)
            ·
              refine ⟨213314891085551182560705497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142209927390367455040470331 213314891085551182560705497)
              ·
                refine ⟨159986168314163386920529123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213314891085551182560705497 159986168314163386920529123)
                ·
                  refine ⟨239979252471245080380793685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159986168314163386920529123 239979252471245080380793685)
                  ·
                    refine ⟨1406128432448701642856213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 239979252471245080380793685 1406128432448701642856213)
                    ·
                      rfl

theorem cell23_8215276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_8215276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215276 prefixEnd_8215276 := by exact prefixLift 8215276
  have htrace : WordTrace (prefixWord ++ tailWord_8215276) baseStart_8215276 baseEnd_8215276 := by
    simpa [prefixWord, tailWord_8215276, baseEnd_8215276] using wordTrace_append hprefix tailTrace_8215276
  have hstable : (prefixWord ++ tailWord_8215276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215276).length < 2 ^ (prefixWord ++ tailWord_8215276).sum := by decide
  have hdescent : baseEnd_8215276 < baseStart_8215276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215285 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_8215285 : Nat := 118140960795 + 8215285 * 2 ^ 59
def prefixEnd_8215285 : Nat := 4983230072969 + 3 ^ 40 * 8215285 * 2
def baseEnd_8215285 : Nat := 4218389918671995393356099

theorem tailTrace_8215285 : CollatzResearch.WordTrace tailWord_8215285 prefixEnd_8215285 4218389918671995393356099 := by
  unfold tailWord_8215285
  simp only [CollatzResearch.WordTrace]
  refine ⟨299636060042432978819879309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199757373361621985879919539 299636060042432978819879309)
  ·
    refine ⟨112363522515912367057454741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299636060042432978819879309 112363522515912367057454741)
    ·
      refine ⟨5267040117933392205818191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112363522515912367057454741 5267040117933392205818191)
      ·
        refine ⟨7900560176900088308727287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267040117933392205818191 7900560176900088308727287)
        ·
          refine ⟨11850840265350132463090931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7900560176900088308727287 11850840265350132463090931)
          ·
            refine ⟨17776260398025198694636397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11850840265350132463090931 17776260398025198694636397)
            ·
              refine ⟨6666097649259449510488649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17776260398025198694636397 6666097649259449510488649)
              ·
                refine ⟨4999573236944587132866487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6666097649259449510488649 4999573236944587132866487)
                ·
                  refine ⟨7499359855416880699299731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999573236944587132866487 7499359855416880699299731)
                  ·
                    refine ⟨11249039783125321048949597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7499359855416880699299731 11249039783125321048949597)
                    ·
                      refine ⟨4218389918671995393356099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249039783125321048949597 4218389918671995393356099)
                      ·
                        rfl

theorem cell23_8215285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_8215285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215285 prefixEnd_8215285 := by exact prefixLift 8215285
  have htrace : WordTrace (prefixWord ++ tailWord_8215285) baseStart_8215285 baseEnd_8215285 := by
    simpa [prefixWord, tailWord_8215285, baseEnd_8215285] using wordTrace_append hprefix tailTrace_8215285
  have hstable : (prefixWord ++ tailWord_8215285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215285).length < 2 ^ (prefixWord ++ tailWord_8215285).sum := by decide
  have hdescent : baseEnd_8215285 < baseStart_8215285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215290 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_8215290 : Nat := 118140960795 + 8215290 * 2 ^ 59
def prefixEnd_8215290 : Nat := 4983230072969 + 3 ^ 40 * 8215290 * 2
def baseEnd_8215290 : Nat := 4218392486075267873793575

theorem tailTrace_8215290 : CollatzResearch.WordTrace tailWord_8215290 prefixEnd_8215290 4218392486075267873793575 := by
  unfold tailWord_8215290
  simp only [CollatzResearch.WordTrace]
  refine ⟨74909060601853716168452831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199757494938276576449207549 74909060601853716168452831)
  ·
    refine ⟨112363590902780574252679247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74909060601853716168452831 112363590902780574252679247)
    ·
      refine ⟨168545386354170861379018871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112363590902780574252679247 168545386354170861379018871)
      ·
        refine ⟨252818079531256292068528307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168545386354170861379018871 252818079531256292068528307)
        ·
          refine ⟨379227119296884438102792461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252818079531256292068528307 379227119296884438102792461)
          ·
            refine ⟨142210169736331664288547173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379227119296884438102792461 142210169736331664288547173)
            ·
              refine ⟨26664406825562187054102595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142210169736331664288547173 26664406825562187054102595)
              ·
                refine ⟨39996610238343280581153893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26664406825562187054102595 39996610238343280581153893)
                ·
                  refine ⟨7499364419689365108966355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39996610238343280581153893 7499364419689365108966355)
                  ·
                    refine ⟨11249046629534047663449533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7499364419689365108966355 11249046629534047663449533)
                    ·
                      refine ⟨4218392486075267873793575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249046629534047663449533 4218392486075267873793575)
                      ·
                        rfl

theorem cell23_8215290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_8215290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215290 prefixEnd_8215290 := by exact prefixLift 8215290
  have htrace : WordTrace (prefixWord ++ tailWord_8215290) baseStart_8215290 baseEnd_8215290 := by
    simpa [prefixWord, tailWord_8215290, baseEnd_8215290] using wordTrace_append hprefix tailTrace_8215290
  have hstable : (prefixWord ++ tailWord_8215290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215290).length < 2 ^ (prefixWord ++ tailWord_8215290).sum := by decide
  have hdescent : baseEnd_8215290 < baseStart_8215290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215333 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_8215333 : Nat := 118140960795 + 8215333 * 2 ^ 59
def prefixEnd_8215333 : Nat := 4983230072969 + 3 ^ 40 * 8215333 * 2
def baseEnd_8215333 : Nat := 4218414565743411205555877

theorem tailTrace_8215333 : CollatzResearch.WordTrace tailWord_8215333 prefixEnd_8215333 4218414565743411205555877 := by
  unfold tailWord_8215333
  simp only [CollatzResearch.WordTrace]
  refine ⟨299637810746259083017626653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199758540497506055345084435 299637810746259083017626653)
  ·
    refine ⟨112364179029847156131609995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299637810746259083017626653 112364179029847156131609995)
    ·
      refine ⟨168546268544770734197414993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112364179029847156131609995 168546268544770734197414993)
      ·
        refine ⟨126409701408578050648061245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168546268544770734197414993 126409701408578050648061245)
        ·
          refine ⟨47403638028216768993022967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126409701408578050648061245 47403638028216768993022967)
          ·
            refine ⟨71105457042325153489534451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47403638028216768993022967 71105457042325153489534451)
            ·
              refine ⟨106658185563487730234301677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71105457042325153489534451 106658185563487730234301677)
              ·
                refine ⟨39996819586307898837863129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106658185563487730234301677 39996819586307898837863129)
                ·
                  refine ⟨29997614689730924128397347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39996819586307898837863129 29997614689730924128397347)
                  ·
                    refine ⟨44996422034596386192596021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29997614689730924128397347 44996422034596386192596021)
                    ·
                      refine ⟨4218414565743411205555877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44996422034596386192596021 4218414565743411205555877)
                      ·
                        rfl

theorem cell23_8215333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_8215333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215333 prefixEnd_8215333 := by exact prefixLift 8215333
  have htrace : WordTrace (prefixWord ++ tailWord_8215333) baseStart_8215333 baseEnd_8215333 := by
    simpa [prefixWord, tailWord_8215333, baseEnd_8215333] using wordTrace_append hprefix tailTrace_8215333
  have hstable : (prefixWord ++ tailWord_8215333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215333).length < 2 ^ (prefixWord ++ tailWord_8215333).sum := by decide
  have hdescent : baseEnd_8215333 < baseStart_8215333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215393 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_8215393 : Nat := 118140960795 + 8215393 * 2 ^ 59
def prefixEnd_8215393 : Nat := 4983230072969 + 3 ^ 40 * 8215393 * 2
def baseEnd_8215393 : Nat := 4218445374582680970805601

theorem tailTrace_8215393 : CollatzResearch.WordTrace tailWord_8215393 prefixEnd_8215393 4218445374582680970805601 := by
  unfold tailWord_8215393
  simp only [CollatzResearch.WordTrace]
  refine ⟨299639999126041713264810833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199759999417361142176540555 299639999126041713264810833)
  ·
    refine ⟨224729999344531284948608125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299639999126041713264810833 224729999344531284948608125)
    ·
      refine ⟨84273749754199231855728047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224729999344531284948608125 84273749754199231855728047)
      ·
        refine ⟨126410624631298847783592071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84273749754199231855728047 126410624631298847783592071)
        ·
          refine ⟨189615936946948271675388107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126410624631298847783592071 189615936946948271675388107)
          ·
            refine ⟨284423905420422407513082161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189615936946948271675388107 284423905420422407513082161)
            ·
              refine ⟨213317929065316805634811621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284423905420422407513082161 213317929065316805634811621)
              ·
                refine ⟨39997111699746901056527179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213317929065316805634811621 39997111699746901056527179)
                ·
                  refine ⟨59995667549620351584790769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39997111699746901056527179 59995667549620351584790769)
                  ·
                    refine ⟨44996750662215263688593077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59995667549620351584790769 44996750662215263688593077)
                    ·
                      refine ⟨4218445374582680970805601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44996750662215263688593077 4218445374582680970805601)
                      ·
                        rfl

theorem cell23_8215393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_8215393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215393 prefixEnd_8215393 := by exact prefixLift 8215393
  have htrace : WordTrace (prefixWord ++ tailWord_8215393) baseStart_8215393 baseEnd_8215393 := by
    simpa [prefixWord, tailWord_8215393, baseEnd_8215393] using wordTrace_append hprefix tailTrace_8215393
  have hstable : (prefixWord ++ tailWord_8215393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215393).length < 2 ^ (prefixWord ++ tailWord_8215393).sum := by decide
  have hdescent : baseEnd_8215393 < baseStart_8215393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215457 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_8215457 : Nat := 118140960795 + 8215457 * 2 ^ 59
def prefixEnd_8215457 : Nat := 4983230072969 + 3 ^ 40 * 8215457 * 2
def baseEnd_8215457 : Nat := 4218478237344568720405307

theorem tailTrace_8215457 : CollatzResearch.WordTrace tailWord_8215457 prefixEnd_8215457 4218478237344568720405307 := by
  unfold tailWord_8215457
  simp only [CollatzResearch.WordTrace]
  refine ⟨299642333397809852195140625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199761555598539901463427083 299642333397809852195140625)
  ·
    refine ⟨224731750048357389146355469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299642333397809852195140625 224731750048357389146355469)
    ·
      refine ⟨84274406268134020929883301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224731750048357389146355469 84274406268134020929883301)
      ·
        refine ⟨15801451175275128924353119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84274406268134020929883301 15801451175275128924353119)
        ·
          refine ⟨23702176762912693386529679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801451175275128924353119 23702176762912693386529679)
          ·
            refine ⟨35553265144369040079794519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23702176762912693386529679 35553265144369040079794519)
            ·
              refine ⟨53329897716553560119691779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35553265144369040079794519 53329897716553560119691779)
              ·
                refine ⟨79994846574830340179537669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53329897716553560119691779 79994846574830340179537669)
                ·
                  refine ⟨14999033732780688783663313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79994846574830340179537669 14999033732780688783663313)
                  ·
                    refine ⟨11249275299585516587747485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14999033732780688783663313 11249275299585516587747485)
                    ·
                      refine ⟨4218478237344568720405307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249275299585516587747485 4218478237344568720405307)
                      ·
                        rfl

theorem cell23_8215457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_8215457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215457 prefixEnd_8215457 := by exact prefixLift 8215457
  have htrace : WordTrace (prefixWord ++ tailWord_8215457) baseStart_8215457 baseEnd_8215457 := by
    simpa [prefixWord, tailWord_8215457, baseEnd_8215457] using wordTrace_append hprefix tailTrace_8215457
  have hstable : (prefixWord ++ tailWord_8215457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215457).length < 2 ^ (prefixWord ++ tailWord_8215457).sum := by decide
  have hdescent : baseEnd_8215457 < baseStart_8215457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215460 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 6]
def baseStart_8215460 : Nat := 118140960795 + 8215460 * 2 ^ 59
def prefixEnd_8215460 : Nat := 4983230072969 + 3 ^ 40 * 8215460 * 2
def baseEnd_8215460 : Nat := 468719975309614689851977

theorem tailTrace_8215460 : CollatzResearch.WordTrace tailWord_8215460 prefixEnd_8215460 468719975309614689851977 := by
  unfold tailWord_8215460
  simp only [CollatzResearch.WordTrace]
  refine ⟨149821221408399491853749917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199761628544532655804999889 149821221408399491853749917)
  ·
    refine ⟨56182958028149809445156219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149821221408399491853749917 56182958028149809445156219)
    ·
      refine ⟨84274437042224714167734329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56182958028149809445156219 84274437042224714167734329)
      ·
        refine ⟨63205827781668535625800747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84274437042224714167734329 63205827781668535625800747)
        ·
          refine ⟨94808741672502803438701121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63205827781668535625800747 94808741672502803438701121)
          ·
            refine ⟨71106556254377102579025841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94808741672502803438701121 71106556254377102579025841)
            ·
              refine ⟨53329917190782826934269381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71106556254377102579025841 53329917190782826934269381)
              ·
                refine ⟨9999359473271780050175509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53329917190782826934269381 9999359473271780050175509)
                ·
                  refine ⟨468719975309614689851977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9999359473271780050175509 468719975309614689851977)
                  ·
                    rfl

theorem cell23_8215460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_8215460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215460 prefixEnd_8215460 := by exact prefixLift 8215460
  have htrace : WordTrace (prefixWord ++ tailWord_8215460) baseStart_8215460 baseEnd_8215460 := by
    simpa [prefixWord, tailWord_8215460, baseEnd_8215460] using wordTrace_append hprefix tailTrace_8215460
  have hstable : (prefixWord ++ tailWord_8215460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215460).length < 2 ^ (prefixWord ++ tailWord_8215460).sum := by decide
  have hdescent : baseEnd_8215460 < baseStart_8215460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215483 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_8215483 : Nat := 118140960795 + 8215483 * 2 ^ 59
def prefixEnd_8215483 : Nat := 4983230072969 + 3 ^ 40 * 8215483 * 2
def baseEnd_8215483 : Nat := 4218491587841585618680187

theorem tailTrace_8215483 : CollatzResearch.WordTrace tailWord_8215483 prefixEnd_8215483 4218491587841585618680187 := by
  unfold tailWord_8215483
  simp only [CollatzResearch.WordTrace]
  refine ⟨299643281695715658635587103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199762187797143772423724735 299643281695715658635587103)
  ·
    refine ⟨449464922543573487953380655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299643281695715658635587103 449464922543573487953380655)
    ·
      refine ⟨674197383815360231930070983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449464922543573487953380655 674197383815360231930070983)
      ·
        refine ⟨1011296075723040347895106475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674197383815360231930070983 1011296075723040347895106475)
        ·
          refine ⟨1516944113584560521842659713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011296075723040347895106475 1516944113584560521842659713)
          ·
            refine ⟨1137708085188420391381994785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516944113584560521842659713 1137708085188420391381994785)
            ·
              refine ⟨853281063891315293536496089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137708085188420391381994785 853281063891315293536496089)
              ·
                refine ⟨639960797918486470152372067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853281063891315293536496089 639960797918486470152372067)
                ·
                  refine ⟨959941196877729705228558101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639960797918486470152372067 959941196877729705228558101)
                  ·
                    refine ⟨44997243603643579932588661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 959941196877729705228558101 44997243603643579932588661)
                    ·
                      refine ⟨4218491587841585618680187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44997243603643579932588661 4218491587841585618680187)
                      ·
                        rfl

theorem cell23_8215483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_8215483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215483 prefixEnd_8215483 := by exact prefixLift 8215483
  have htrace : WordTrace (prefixWord ++ tailWord_8215483) baseStart_8215483 baseEnd_8215483 := by
    simpa [prefixWord, tailWord_8215483, baseEnd_8215483] using wordTrace_append hprefix tailTrace_8215483
  have hstable : (prefixWord ++ tailWord_8215483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215483).length < 2 ^ (prefixWord ++ tailWord_8215483).sum := by decide
  have hdescent : baseEnd_8215483 < baseStart_8215483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215504 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 1, 1, 3]
def baseStart_8215504 : Nat := 118140960795 + 8215504 * 2 ^ 59
def prefixEnd_8215504 : Nat := 4983230072969 + 3 ^ 40 * 8215504 * 2
def baseEnd_8215504 : Nat := 4218502370935330036517591

theorem tailTrace_8215504 : CollatzResearch.WordTrace tailWord_8215504 prefixEnd_8215504 4218502370935330036517591 := by
  unfold tailWord_8215504
  simp only [CollatzResearch.WordTrace]
  refine ⟨149822023814319789611050783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199762698419093052814734377 149822023814319789611050783)
  ·
    refine ⟨224733035721479684416576175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149822023814319789611050783 224733035721479684416576175)
    ·
      refine ⟨337099553582219526624864263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224733035721479684416576175 337099553582219526624864263)
      ·
        refine ⟨505649330373329289937296395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337099553582219526624864263 505649330373329289937296395)
        ·
          refine ⟨758473995559993934905944593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505649330373329289937296395 758473995559993934905944593)
          ·
            refine ⟨568855496669995451179458445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758473995559993934905944593 568855496669995451179458445)
            ·
              refine ⟨213320811251248294192296917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568855496669995451179458445 213320811251248294192296917)
              ·
                refine ⟨4999706513701131895131959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213320811251248294192296917 4999706513701131895131959)
                ·
                  refine ⟨7499559770551697842697939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999706513701131895131959 7499559770551697842697939)
                  ·
                    refine ⟨11249339655827546764046909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7499559770551697842697939 11249339655827546764046909)
                    ·
                      refine ⟨4218502370935330036517591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249339655827546764046909 4218502370935330036517591)
                      ·
                        rfl

theorem cell23_8215504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 1, 3].length) (baseStart_8215504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215504 prefixEnd_8215504 := by exact prefixLift 8215504
  have htrace : WordTrace (prefixWord ++ tailWord_8215504) baseStart_8215504 baseEnd_8215504 := by
    simpa [prefixWord, tailWord_8215504, baseEnd_8215504] using wordTrace_append hprefix tailTrace_8215504
  have hstable : (prefixWord ++ tailWord_8215504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215504).length < 2 ^ (prefixWord ++ tailWord_8215504).sum := by decide
  have hdescent : baseEnd_8215504 < baseStart_8215504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215514 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2]
def baseStart_8215514 : Nat := 118140960795 + 8215514 * 2 ^ 59
def prefixEnd_8215514 : Nat := 4983230072969 + 3 ^ 40 * 8215514 * 2
def baseEnd_8215514 : Nat := 4218507505741874997392545

theorem tailTrace_8215514 : CollatzResearch.WordTrace tailWord_8215514 prefixEnd_8215514 4218507505741874997392545 := by
  unfold tailWord_8215514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74911103089650837732491399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199762941572402233953310397 74911103089650837732491399)
  ·
    refine ⟨112366654634476256598737099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74911103089650837732491399 112366654634476256598737099)
    ·
      refine ⟨168549981951714384898105649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112366654634476256598737099 168549981951714384898105649)
      ·
        refine ⟨126412486463785788673579237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168549981951714384898105649 126412486463785788673579237)
        ·
          refine ⟨23702341211959835376296107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126412486463785788673579237 23702341211959835376296107)
          ·
            refine ⟨35553511817939753064444161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23702341211959835376296107 35553511817939753064444161)
            ·
              refine ⟨26665133863454814798333121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35553511817939753064444161 26665133863454814798333121)
              ·
                refine ⟨19998850397591111098749841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26665133863454814798333121 19998850397591111098749841)
                ·
                  refine ⟨14999137798193333324062381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19998850397591111098749841 14999137798193333324062381)
                  ·
                    refine ⟨5624676674322499996523393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14999137798193333324062381 5624676674322499996523393)
                    ·
                      refine ⟨4218507505741874997392545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624676674322499996523393 4218507505741874997392545)
                      ·
                        rfl

theorem cell23_8215514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_8215514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215514 prefixEnd_8215514 := by exact prefixLift 8215514
  have htrace : WordTrace (prefixWord ++ tailWord_8215514) baseStart_8215514 baseEnd_8215514 := by
    simpa [prefixWord, tailWord_8215514, baseEnd_8215514] using wordTrace_append hprefix tailTrace_8215514
  have hstable : (prefixWord ++ tailWord_8215514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215514).length < 2 ^ (prefixWord ++ tailWord_8215514).sum := by decide
  have hdescent : baseEnd_8215514 < baseStart_8215514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215527 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_8215527 : Nat := 118140960795 + 8215527 * 2 ^ 59
def prefixEnd_8215527 : Nat := 4983230072969 + 3 ^ 40 * 8215527 * 2
def baseEnd_8215527 : Nat := 4218514180990383446529985

theorem tailTrace_8215527 : CollatzResearch.WordTrace tailWord_8215527 prefixEnd_8215527 4218514180990383446529985 := by
  unfold tailWord_8215527
  simp only [CollatzResearch.WordTrace]
  refine ⟨299644886507556254150188835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199763257671704169433459223 299644886507556254150188835)
  ·
    refine ⟨449467329761334381225283253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299644886507556254150188835 449467329761334381225283253)
    ·
      refine ⟨42137562165125098239870305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449467329761334381225283253 42137562165125098239870305)
      ·
        refine ⟨31603171623843823679902729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42137562165125098239870305 31603171623843823679902729)
        ·
          refine ⟨23702378717882867759927047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31603171623843823679902729 23702378717882867759927047)
          ·
            refine ⟨35553568076824301639890571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23702378717882867759927047 35553568076824301639890571)
            ·
              refine ⟨53330352115236452459835857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35553568076824301639890571 53330352115236452459835857)
              ·
                refine ⟨39997764086427339344876893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53330352115236452459835857 39997764086427339344876893)
                ·
                  refine ⟨14999161532410252254328835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39997764086427339344876893 14999161532410252254328835)
                  ·
                    refine ⟨22498742298615378381493253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14999161532410252254328835 22498742298615378381493253)
                    ·
                      refine ⟨4218514180990383446529985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22498742298615378381493253 4218514180990383446529985)
                      ·
                        rfl

theorem cell23_8215527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_8215527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215527 prefixEnd_8215527 := by exact prefixLift 8215527
  have htrace : WordTrace (prefixWord ++ tailWord_8215527) baseStart_8215527 baseEnd_8215527 := by
    simpa [prefixWord, tailWord_8215527, baseEnd_8215527] using wordTrace_append hprefix tailTrace_8215527
  have hstable : (prefixWord ++ tailWord_8215527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215527).length < 2 ^ (prefixWord ++ tailWord_8215527).sum := by decide
  have hdescent : baseEnd_8215527 < baseStart_8215527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215537 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 1, 6]
def baseStart_8215537 : Nat := 118140960795 + 8215537 * 2 ^ 59
def prefixEnd_8215537 : Nat := 4983230072969 + 3 ^ 40 * 8215537 * 2
def baseEnd_8215537 : Nat := 1406173105265642802468313

theorem tailTrace_8215537 : CollatzResearch.WordTrace tailWord_8215537 prefixEnd_8215537 1406173105265642802468313 := by
  unfold tailWord_8215537
  simp only [CollatzResearch.WordTrace]
  refine ⟨299645251237520025858052865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199763500825013350572035243 299645251237520025858052865)
  ·
    refine ⟨224733938428140019393539649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299645251237520025858052865 224733938428140019393539649)
    ·
      refine ⟨168550453821105014545154737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224733938428140019393539649 168550453821105014545154737)
      ·
        refine ⟨126412840365828760908866053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168550453821105014545154737 126412840365828760908866053)
        ·
          refine ⟨23702407568592892670412385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126412840365828760908866053 23702407568592892670412385)
          ·
            refine ⟨17776805676444669502809289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23702407568592892670412385 17776805676444669502809289)
            ·
              refine ⟨13332604257333502127106967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17776805676444669502809289 13332604257333502127106967)
              ·
                refine ⟨19998906386000253190660451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332604257333502127106967 19998906386000253190660451)
                ·
                  refine ⟨29998359579000379785990677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19998906386000253190660451 29998359579000379785990677)
                  ·
                    refine ⟨1406173105265642802468313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29998359579000379785990677 1406173105265642802468313)
                    ·
                      rfl

theorem cell23_8215537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_8215537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215537 prefixEnd_8215537 := by exact prefixLift 8215537
  have htrace : WordTrace (prefixWord ++ tailWord_8215537) baseStart_8215537 baseEnd_8215537 := by
    simpa [prefixWord, tailWord_8215537, baseEnd_8215537] using wordTrace_append hprefix tailTrace_8215537
  have hstable : (prefixWord ++ tailWord_8215537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215537).length < 2 ^ (prefixWord ++ tailWord_8215537).sum := by decide
  have hdescent : baseEnd_8215537 < baseStart_8215537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215547 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 3]
def baseStart_8215547 : Nat := 118140960795 + 8215547 * 2 ^ 59
def prefixEnd_8215547 : Nat := 4983230072969 + 3 ^ 40 * 8215547 * 2
def baseEnd_8215547 : Nat := 4218524450603473368279893

theorem tailTrace_8215547 : CollatzResearch.WordTrace tailWord_8215547 prefixEnd_8215547 4218524450603473368279893 := by
  unfold tailWord_8215547
  simp only [CollatzResearch.WordTrace]
  refine ⟨299645615967483797565916895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199763743978322531710611263 299645615967483797565916895)
  ·
    refine ⟨449468423951225696348875343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299645615967483797565916895 449468423951225696348875343)
    ·
      refine ⟨674202635926838544523313015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449468423951225696348875343 674202635926838544523313015)
      ·
        refine ⟨1011303953890257816784969523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674202635926838544523313015 1011303953890257816784969523)
        ·
          refine ⟨1516955930835386725177454285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011303953890257816784969523 1516955930835386725177454285)
          ·
            refine ⟨568858474063270021941545357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1516955930835386725177454285 568858474063270021941545357)
            ·
              refine ⟨213321927773726258228079509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568858474063270021941545357 213321927773726258228079509)
              ·
                refine ⟨9999465364393418354441227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213321927773726258228079509 9999465364393418354441227)
                ·
                  refine ⟨14999198046590127531661841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9999465364393418354441227 14999198046590127531661841)
                  ·
                    refine ⟨11249398534942595648746381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14999198046590127531661841 11249398534942595648746381)
                    ·
                      refine ⟨4218524450603473368279893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249398534942595648746381 4218524450603473368279893)
                      ·
                        rfl

theorem cell23_8215547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 3].length) (baseStart_8215547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215547 prefixEnd_8215547 := by exact prefixLift 8215547
  have htrace : WordTrace (prefixWord ++ tailWord_8215547) baseStart_8215547 baseEnd_8215547 := by
    simpa [prefixWord, tailWord_8215547, baseEnd_8215547] using wordTrace_append hprefix tailTrace_8215547
  have hstable : (prefixWord ++ tailWord_8215547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215547).length < 2 ^ (prefixWord ++ tailWord_8215547).sum := by decide
  have hdescent : baseEnd_8215547 < baseStart_8215547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215564 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_8215564 : Nat := 118140960795 + 8215564 * 2 ^ 59
def prefixEnd_8215564 : Nat := 4983230072969 + 3 ^ 40 * 8215564 * 2
def baseEnd_8215564 : Nat := 4218533179774599801767315

theorem tailTrace_8215564 : CollatzResearch.WordTrace tailWord_8215564 prefixEnd_8215564 4218533179774599801767315 := by
  unfold tailWord_8215564
  simp only [CollatzResearch.WordTrace]
  refine ⟨149823118004211104734642873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199764157338948139646190497 149823118004211104734642873)
  ·
    refine ⟨112367338503158328550982155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149823118004211104734642873 112367338503158328550982155)
    ·
      refine ⟨168551007754737492826473233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112367338503158328550982155 168551007754737492826473233)
      ·
        refine ⟨126413255816053119619854925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168551007754737492826473233 126413255816053119619854925)
        ·
          refine ⟨47404970931019919857445597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126413255816053119619854925 47404970931019919857445597)
          ·
            refine ⟨17776864099132469946542099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47404970931019919857445597 17776864099132469946542099)
            ·
              refine ⟨26665296148698704919813149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17776864099132469946542099 26665296148698704919813149)
              ·
                refine ⟨9999486055762014344929931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26665296148698704919813149 9999486055762014344929931)
                ·
                  refine ⟨14999229083643021517394897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9999486055762014344929931 14999229083643021517394897)
                  ·
                    refine ⟨11249421812732266138046173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14999229083643021517394897 11249421812732266138046173)
                    ·
                      refine ⟨4218533179774599801767315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249421812732266138046173 4218533179774599801767315)
                      ·
                        rfl

theorem cell23_8215564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_8215564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215564 prefixEnd_8215564 := by exact prefixLift 8215564
  have htrace : WordTrace (prefixWord ++ tailWord_8215564) baseStart_8215564 baseEnd_8215564 := by
    simpa [prefixWord, tailWord_8215564, baseEnd_8215564] using wordTrace_append hprefix tailTrace_8215564
  have hstable : (prefixWord ++ tailWord_8215564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215564).length < 2 ^ (prefixWord ++ tailWord_8215564).sum := by decide
  have hdescent : baseEnd_8215564 < baseStart_8215564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215591 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_8215591 : Nat := 118140960795 + 8215591 * 2 ^ 59
def prefixEnd_8215591 : Nat := 4983230072969 + 3 ^ 40 * 8215591 * 2
def baseEnd_8215591 : Nat := 4218547043752271196129691

theorem tailTrace_8215591 : CollatzResearch.WordTrace tailWord_8215591 prefixEnd_8215591 4218547043752271196129691 := by
  unfold tailWord_8215591
  simp only [CollatzResearch.WordTrace]
  refine ⟨299647220779324393080518627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199764813852882928720345751 299647220779324393080518627)
  ·
    refine ⟨449470831168986589620777941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299647220779324393080518627 449470831168986589620777941)
    ·
      refine ⟨10534472605523123194236983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 449470831168986589620777941 10534472605523123194236983)
      ·
        refine ⟨15801708908284684791355475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10534472605523123194236983 15801708908284684791355475)
        ·
          refine ⟨23702563362427027187033213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801708908284684791355475 23702563362427027187033213)
          ·
            refine ⟨8888461260910135195137455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23702563362427027187033213 8888461260910135195137455)
            ·
              refine ⟨13332691891365202792706183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888461260910135195137455 13332691891365202792706183)
              ·
                refine ⟨19999037837047804189059275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332691891365202792706183 19999037837047804189059275)
                ·
                  refine ⟨29998556755571706283588913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19999037837047804189059275 29998556755571706283588913)
                  ·
                    refine ⟨22498917566678779712691685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29998556755571706283588913 22498917566678779712691685)
                    ·
                      refine ⟨4218547043752271196129691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22498917566678779712691685 4218547043752271196129691)
                      ·
                        rfl

theorem cell23_8215591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_8215591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215591 prefixEnd_8215591 := by exact prefixLift 8215591
  have htrace : WordTrace (prefixWord ++ tailWord_8215591) baseStart_8215591 baseEnd_8215591 := by
    simpa [prefixWord, tailWord_8215591, baseEnd_8215591] using wordTrace_append hprefix tailTrace_8215591
  have hstable : (prefixWord ++ tailWord_8215591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215591).length < 2 ^ (prefixWord ++ tailWord_8215591).sum := by decide
  have hdescent : baseEnd_8215591 < baseStart_8215591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215610 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_8215610 : Nat := 118140960795 + 8215610 * 2 ^ 59
def prefixEnd_8215610 : Nat := 4983230072969 + 3 ^ 40 * 8215610 * 2
def baseEnd_8215610 : Nat := 1406185599961568873930701

theorem tailTrace_8215610 : CollatzResearch.WordTrace tailWord_8215610 prefixEnd_8215610 1406185599961568873930701 := by
  unfold tailWord_8215610
  simp only [CollatzResearch.WordTrace]
  refine ⟨74911978441563889831365071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199765275844170372883640189 74911978441563889831365071)
  ·
    refine ⟨112367967662345834747047607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74911978441563889831365071 112367967662345834747047607)
    ·
      refine ⟨168551951493518752120571411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112367967662345834747047607 168551951493518752120571411)
      ·
        refine ⟨252827927240278128180857117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168551951493518752120571411 252827927240278128180857117)
        ·
          refine ⟨94810472715104298067821419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252827927240278128180857117 94810472715104298067821419)
          ·
            refine ⟨142215709072656447101732129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94810472715104298067821419 142215709072656447101732129)
            ·
              refine ⟨106661781804492335326299097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142215709072656447101732129 106661781804492335326299097)
              ·
                refine ⟨79996336353369251494724323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106661781804492335326299097 79996336353369251494724323)
                ·
                  refine ⟨119994504530053877242086485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79996336353369251494724323 119994504530053877242086485)
                  ·
                    refine ⟨1406185599961568873930701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119994504530053877242086485 1406185599961568873930701)
                    ·
                      rfl

theorem cell23_8215610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_8215610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215610 prefixEnd_8215610 := by exact prefixLift 8215610
  have htrace : WordTrace (prefixWord ++ tailWord_8215610) baseStart_8215610 baseEnd_8215610 := by
    simpa [prefixWord, tailWord_8215610, baseEnd_8215610] using wordTrace_append hprefix tailTrace_8215610
  have hstable : (prefixWord ++ tailWord_8215610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215610).length < 2 ^ (prefixWord ++ tailWord_8215610).sum := by decide
  have hdescent : baseEnd_8215610 < baseStart_8215610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215637 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_8215637 : Nat := 118140960795 + 8215637 * 2 ^ 59
def prefixEnd_8215637 : Nat := 4983230072969 + 3 ^ 40 * 8215637 * 2
def baseEnd_8215637 : Nat := 4218570663862378016154479

theorem tailTrace_8215637 : CollatzResearch.WordTrace tailWord_8215637 prefixEnd_8215637 4218570663862378016154479 := by
  unfold tailWord_8215637
  simp only [CollatzResearch.WordTrace]
  refine ⟨299648898537157742936693165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199765932358105161957795443 299648898537157742936693165)
  ·
    refine ⟨112368336951434153601259937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299648898537157742936693165 112368336951434153601259937)
    ·
      refine ⟨84276252713575615200944953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112368336951434153601259937 84276252713575615200944953)
      ·
        refine ⟨63207189535181711400708715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84276252713575615200944953 63207189535181711400708715)
        ·
          refine ⟨94810784302772567101063073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63207189535181711400708715 94810784302772567101063073)
          ·
            refine ⟨71108088227079425325797305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94810784302772567101063073 71108088227079425325797305)
            ·
              refine ⟨53331066170309568994347979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71108088227079425325797305 53331066170309568994347979)
              ·
                refine ⟨79996599255464353491521969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53331066170309568994347979 79996599255464353491521969)
                ·
                  refine ⟨59997449441598265118641477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79996599255464353491521969 59997449441598265118641477)
                  ·
                    refine ⟨11249521770299674709745277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59997449441598265118641477 11249521770299674709745277)
                    ·
                      refine ⟨4218570663862378016154479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249521770299674709745277 4218570663862378016154479)
                      ·
                        rfl

theorem cell23_8215637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_8215637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215637 prefixEnd_8215637 := by exact prefixLift 8215637
  have htrace : WordTrace (prefixWord ++ tailWord_8215637) baseStart_8215637 baseEnd_8215637 := by
    simpa [prefixWord, tailWord_8215637, baseEnd_8215637] using wordTrace_append hprefix tailTrace_8215637
  have hstable : (prefixWord ++ tailWord_8215637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215637).length < 2 ^ (prefixWord ++ tailWord_8215637).sum := by decide
  have hdescent : baseEnd_8215637 < baseStart_8215637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215737 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_8215737 : Nat := 118140960795 + 8215737 * 2 ^ 59
def prefixEnd_8215737 : Nat := 4983230072969 + 3 ^ 40 * 8215737 * 2
def baseEnd_8215737 : Nat := 4218622011927827624904019

theorem tailTrace_8215737 : CollatzResearch.WordTrace tailWord_8215737 prefixEnd_8215737 4218622011927827624904019 := by
  unfold tailWord_8215737
  simp only [CollatzResearch.WordTrace]
  refine ⟨299652545836795460015333465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199768363891196973343555643 299652545836795460015333465)
  ·
    refine ⟨224739409377596595011500099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299652545836795460015333465 224739409377596595011500099)
    ·
      refine ⟨337109114066394892517250149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224739409377596595011500099 337109114066394892517250149)
      ·
        refine ⟨63207958887449042346984403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337109114066394892517250149 63207958887449042346984403)
        ·
          refine ⟨94811938331173563520476605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63207958887449042346984403 94811938331173563520476605)
          ·
            refine ⟨35554476874190086320178727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94811938331173563520476605 35554476874190086320178727)
            ·
              refine ⟨53331715311285129480268091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35554476874190086320178727 53331715311285129480268091)
              ·
                refine ⟨79997572966927694220402137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53331715311285129480268091 79997572966927694220402137)
                ·
                  refine ⟨59998179725195770665301603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79997572966927694220402137 59998179725195770665301603)
                  ·
                    refine ⟨89997269587793655997952405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59998179725195770665301603 89997269587793655997952405)
                    ·
                      refine ⟨4218622011927827624904019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89997269587793655997952405 4218622011927827624904019)
                      ·
                        rfl

theorem cell23_8215737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_8215737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215737 prefixEnd_8215737 := by exact prefixLift 8215737
  have htrace : WordTrace (prefixWord ++ tailWord_8215737) baseStart_8215737 baseEnd_8215737 := by
    simpa [prefixWord, tailWord_8215737, baseEnd_8215737] using wordTrace_append hprefix tailTrace_8215737
  have hstable : (prefixWord ++ tailWord_8215737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215737).length < 2 ^ (prefixWord ++ tailWord_8215737).sum := by decide
  have hdescent : baseEnd_8215737 < baseStart_8215737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215747 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 6]
def baseStart_8215747 : Nat := 118140960795 + 8215747 * 2 ^ 59
def prefixEnd_8215747 : Nat := 4983230072969 + 3 ^ 40 * 8215747 * 2
def baseEnd_8215747 : Nat := 468736349637152509530997

theorem tailTrace_8215747 : CollatzResearch.WordTrace tailWord_8215747 prefixEnd_8215747 468736349637152509530997 := by
  unfold tailWord_8215747
  simp only [CollatzResearch.WordTrace]
  refine ⟨299652910566759231723197495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199768607044506154482131663 299652910566759231723197495)
  ·
    refine ⟨449479365850138847584796243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299652910566759231723197495 449479365850138847584796243)
    ·
      refine ⟨674219048775208271377194365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449479365850138847584796243 674219048775208271377194365)
      ·
        refine ⟨252832143290703101766447887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674219048775208271377194365 252832143290703101766447887)
        ·
          refine ⟨379248214936054652649671831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252832143290703101766447887 379248214936054652649671831)
          ·
            refine ⟨568872322404081978974507747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379248214936054652649671831 568872322404081978974507747)
            ·
              refine ⟨853308483606122968461761621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568872322404081978974507747 853308483606122968461761621)
              ·
                refine ⟨9999708792259253536661269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 853308483606122968461761621 9999708792259253536661269)
                ·
                  refine ⟨468736349637152509530997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9999708792259253536661269 468736349637152509530997)
                  ·
                    rfl

theorem cell23_8215747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 6].length) (baseStart_8215747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215747 prefixEnd_8215747 := by exact prefixLift 8215747
  have htrace : WordTrace (prefixWord ++ tailWord_8215747) baseStart_8215747 baseEnd_8215747 := by
    simpa [prefixWord, tailWord_8215747, baseEnd_8215747] using wordTrace_append hprefix tailTrace_8215747
  have hstable : (prefixWord ++ tailWord_8215747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215747).length < 2 ^ (prefixWord ++ tailWord_8215747).sum := by decide
  have hdescent : baseEnd_8215747 < baseStart_8215747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215801 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 2, 3, 2]
def baseStart_8215801 : Nat := 118140960795 + 8215801 * 2 ^ 59
def prefixEnd_8215801 : Nat := 4983230072969 + 3 ^ 40 * 8215801 * 2
def baseEnd_8215801 : Nat := 4218654874689715374503725

theorem tailTrace_8215801 : CollatzResearch.WordTrace tailWord_8215801 prefixEnd_8215801 4218654874689715374503725 := by
  unfold tailWord_8215801
  simp only [CollatzResearch.WordTrace]
  refine ⟨299654880108563598945663257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199769920072375732630442171 299654880108563598945663257)
  ·
    refine ⟨224741160081422699209247443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299654880108563598945663257 224741160081422699209247443)
    ·
      refine ⟨337111740122134048813871165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224741160081422699209247443 337111740122134048813871165)
      ·
        refine ⟨126416902545800268305201687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337111740122134048813871165 126416902545800268305201687)
        ·
          refine ⟨189625353818700402457802531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126416902545800268305201687 189625353818700402457802531)
          ·
            refine ⟨284438030728050603686703797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189625353818700402457802531 284438030728050603686703797)
            ·
              refine ⟨26666065380754744095628481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284438030728050603686703797 26666065380754744095628481)
              ·
                refine ⟨19999549035566058071721361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26666065380754744095628481 19999549035566058071721361)
                ·
                  refine ⟨14999661776674543553791021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19999549035566058071721361 14999661776674543553791021)
                  ·
                    refine ⟨5624873166252953832671633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14999661776674543553791021 5624873166252953832671633)
                    ·
                      refine ⟨4218654874689715374503725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624873166252953832671633 4218654874689715374503725)
                      ·
                        rfl

theorem cell23_8215801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_8215801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215801 prefixEnd_8215801 := by exact prefixLift 8215801
  have htrace : WordTrace (prefixWord ++ tailWord_8215801) baseStart_8215801 baseEnd_8215801 := by
    simpa [prefixWord, tailWord_8215801, baseEnd_8215801] using wordTrace_append hprefix tailTrace_8215801
  have hstable : (prefixWord ++ tailWord_8215801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215801).length < 2 ^ (prefixWord ++ tailWord_8215801).sum := by decide
  have hdescent : baseEnd_8215801 < baseStart_8215801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215858 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_8215858 : Nat := 118140960795 + 8215858 * 2 ^ 59
def prefixEnd_8215858 : Nat := 4983230072969 + 3 ^ 40 * 8215858 * 2
def baseEnd_8215858 : Nat := 1406228047695673883830321

theorem tailTrace_8215858 : CollatzResearch.WordTrace tailWord_8215858 prefixEnd_8215858 1406228047695673883830321 := by
  unfold tailWord_8215858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74914239767339274420122057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199771306046238065120325485 74914239767339274420122057)
  ·
    refine ⟨56185679825504455815091543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74914239767339274420122057 56185679825504455815091543)
    ·
      refine ⟨84278519738256683722637315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56185679825504455815091543 84278519738256683722637315)
      ·
        refine ⟨126417779607385025583955973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84278519738256683722637315 126417779607385025583955973)
        ·
          refine ⟨23703333676384692296991745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126417779607385025583955973 23703333676384692296991745)
          ·
            refine ⟨17777500257288519222743809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23703333676384692296991745 17777500257288519222743809)
            ·
              refine ⟨13333125192966389417057857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17777500257288519222743809 13333125192966389417057857)
              ·
                refine ⟨9999843894724792062793393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13333125192966389417057857 9999843894724792062793393)
                ·
                  refine ⟨7499882921043594047095045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9999843894724792062793393 7499882921043594047095045)
                  ·
                    refine ⟨1406228047695673883830321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499882921043594047095045 1406228047695673883830321)
                    ·
                      rfl

theorem cell23_8215858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_8215858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215858 prefixEnd_8215858 := by exact prefixLift 8215858
  have htrace : WordTrace (prefixWord ++ tailWord_8215858) baseStart_8215858 baseEnd_8215858 := by
    simpa [prefixWord, tailWord_8215858, baseEnd_8215858] using wordTrace_append hprefix tailTrace_8215858
  have hstable : (prefixWord ++ tailWord_8215858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215858).length < 2 ^ (prefixWord ++ tailWord_8215858).sum := by decide
  have hdescent : baseEnd_8215858 < baseStart_8215858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215864 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_8215864 : Nat := 118140960795 + 8215864 * 2 ^ 59
def prefixEnd_8215864 : Nat := 4983230072969 + 3 ^ 40 * 8215864 * 2
def baseEnd_8215864 : Nat := 4218687223970948628015935

theorem tailTrace_8215864 : CollatzResearch.WordTrace tailWord_8215864 prefixEnd_8215864 4218687223970948628015935 := by
  unfold tailWord_8215864
  simp only [CollatzResearch.WordTrace]
  refine ⟨149828588953667680352603323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199771451938223573803471097 149828588953667680352603323)
  ·
    refine ⟨224742883430501520528904985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149828588953667680352603323 224742883430501520528904985)
    ·
      refine ⟨168557162572876140396678739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224742883430501520528904985 168557162572876140396678739)
      ·
        refine ⟨252835743859314210595018109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168557162572876140396678739 252835743859314210595018109)
        ·
          refine ⟨94813403947242828973131791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252835743859314210595018109 94813403947242828973131791)
          ·
            refine ⟨142220105920864243459697687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94813403947242828973131791 142220105920864243459697687)
            ·
              refine ⟨213330158881296365189546531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142220105920864243459697687 213330158881296365189546531)
              ·
                refine ⟨319995238321944547784319797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213330158881296365189546531 319995238321944547784319797)
                ·
                  refine ⟨29999553592682301354779981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319995238321944547784319797 29999553592682301354779981)
                  ·
                    refine ⟨11249832597255863008042493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29999553592682301354779981 11249832597255863008042493)
                    ·
                      refine ⟨4218687223970948628015935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11249832597255863008042493 4218687223970948628015935)
                      ·
                        rfl

theorem cell23_8215864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_8215864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215864 prefixEnd_8215864 := by exact prefixLift 8215864
  have htrace : WordTrace (prefixWord ++ tailWord_8215864) baseStart_8215864 baseEnd_8215864 := by
    simpa [prefixWord, tailWord_8215864, baseEnd_8215864] using wordTrace_append hprefix tailTrace_8215864
  have hstable : (prefixWord ++ tailWord_8215864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215864).length < 2 ^ (prefixWord ++ tailWord_8215864).sum := by decide
  have hdescent : baseEnd_8215864 < baseStart_8215864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215891 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 3, 3, 2]
def baseStart_8215891 : Nat := 118140960795 + 8215891 * 2 ^ 59
def prefixEnd_8215891 : Nat := 4983230072969 + 3 ^ 40 * 8215891 * 2
def baseEnd_8215891 : Nat := 4218701087948620022378311

theorem tailTrace_8215891 : CollatzResearch.WordTrace tailWord_8215891 prefixEnd_8215891 4218701087948620022378311 := by
  unfold tailWord_8215891
  simp only [CollatzResearch.WordTrace]
  refine ⟨299658162678237544316439527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199772108452158362877626351 299658162678237544316439527)
  ·
    refine ⟨449487244017356316474659291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299658162678237544316439527 449487244017356316474659291)
    ·
      refine ⟨674230866026034474711988937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449487244017356316474659291 674230866026034474711988937)
      ·
        refine ⟨505673149519525856033991703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674230866026034474711988937 505673149519525856033991703)
        ·
          refine ⟨758509724279288784050987555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505673149519525856033991703 758509724279288784050987555)
          ·
            refine ⟨1137764586418933176076481333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758509724279288784050987555 1137764586418933176076481333)
            ·
              refine ⟨106665429976774985257170125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1137764586418933176076481333 106665429976774985257170125)
              ·
                refine ⟨39999536241290619471438797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106665429976774985257170125 39999536241290619471438797)
                ·
                  refine ⟨14999826090483982301789549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39999536241290619471438797 14999826090483982301789549)
                  ·
                    refine ⟨5624934783931493363171081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14999826090483982301789549 5624934783931493363171081)
                    ·
                      refine ⟨4218701087948620022378311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624934783931493363171081 4218701087948620022378311)
                      ·
                        rfl

theorem cell23_8215891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3, 2].length) (baseStart_8215891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215891 prefixEnd_8215891 := by exact prefixLift 8215891
  have htrace : WordTrace (prefixWord ++ tailWord_8215891) baseStart_8215891 baseEnd_8215891 := by
    simpa [prefixWord, tailWord_8215891, baseEnd_8215891] using wordTrace_append hprefix tailTrace_8215891
  have hstable : (prefixWord ++ tailWord_8215891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215891).length < 2 ^ (prefixWord ++ tailWord_8215891).sum := by decide
  have hdescent : baseEnd_8215891 < baseStart_8215891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215921 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 3, 4, 2]
def baseStart_8215921 : Nat := 118140960795 + 8215921 * 2 ^ 59
def prefixEnd_8215921 : Nat := 4983230072969 + 3 ^ 40 * 8215921 * 2
def baseEnd_8215921 : Nat := 4218716492368254905003173

theorem tailTrace_8215921 : CollatzResearch.WordTrace tailWord_8215921 prefixEnd_8215921 4218716492368254905003173 := by
  unfold tailWord_8215921
  simp only [CollatzResearch.WordTrace]
  refine ⟨299659256868128859440031617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199772837912085906293354411 299659256868128859440031617)
  ·
    refine ⟨224744442651096644580023713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299659256868128859440031617 224744442651096644580023713)
    ·
      refine ⟨168558331988322483435017785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224744442651096644580023713 168558331988322483435017785)
      ·
        refine ⟨126418748991241862576263339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168558331988322483435017785 126418748991241862576263339)
        ·
          refine ⟨189628123486862793864395009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126418748991241862576263339 189628123486862793864395009)
          ·
            refine ⟨142221092615147095398296257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189628123486862793864395009 142221092615147095398296257)
            ·
              refine ⟨106665819461360321548722193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142221092615147095398296257 106665819461360321548722193)
              ·
                refine ⟨79999364596020241161541645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106665819461360321548722193 79999364596020241161541645)
                ·
                  refine ⟨29999761723507590435578117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79999364596020241161541645 29999761723507590435578117)
                  ·
                    refine ⟨5624955323157673206670897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29999761723507590435578117 5624955323157673206670897)
                    ·
                      refine ⟨4218716492368254905003173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624955323157673206670897 4218716492368254905003173)
                      ·
                        rfl

theorem cell23_8215921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_8215921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215921 prefixEnd_8215921 := by exact prefixLift 8215921
  have htrace : WordTrace (prefixWord ++ tailWord_8215921) baseStart_8215921 baseEnd_8215921 := by
    simpa [prefixWord, tailWord_8215921, baseEnd_8215921] using wordTrace_append hprefix tailTrace_8215921
  have hstable : (prefixWord ++ tailWord_8215921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215921).length < 2 ^ (prefixWord ++ tailWord_8215921).sum := by decide
  have hdescent : baseEnd_8215921 < baseStart_8215921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215989 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_8215989 : Nat := 118140960795 + 8215989 * 2 ^ 59
def prefixEnd_8215989 : Nat := 4983230072969 + 3 ^ 40 * 8215989 * 2
def baseEnd_8215989 : Nat := 4218751409052760638952861

theorem tailTrace_8215989 : CollatzResearch.WordTrace tailWord_8215989 prefixEnd_8215989 4218751409052760638952861 := by
  unfold tailWord_8215989
  simp only [CollatzResearch.WordTrace]
  refine ⟨299661737031882507053507021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199774491354588338035671347 299661737031882507053507021)
  ·
    refine ⟨112373151386955940145065133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299661737031882507053507021 112373151386955940145065133)
    ·
      refine ⟨42139931770108477554399425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112373151386955940145065133 42139931770108477554399425)
      ·
        refine ⟨31604948827581358165799569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42139931770108477554399425 31604948827581358165799569)
        ·
          refine ⟨23703711620686018624349677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31604948827581358165799569 23703711620686018624349677)
          ·
            refine ⟨8888891857757256984131129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23703711620686018624349677 8888891857757256984131129)
            ·
              refine ⟨6666668893317942738098347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8888891857757256984131129 6666668893317942738098347)
              ·
                refine ⟨10000003339976914107147521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666668893317942738098347 10000003339976914107147521)
                ·
                  refine ⟨7500002504982685580360641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10000003339976914107147521 7500002504982685580360641)
                  ·
                    refine ⟨5625001878737014185270481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7500002504982685580360641 5625001878737014185270481)
                    ·
                      refine ⟨4218751409052760638952861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625001878737014185270481 4218751409052760638952861)
                      ·
                        rfl

theorem cell23_8215989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_8215989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215989 prefixEnd_8215989 := by exact prefixLift 8215989
  have htrace : WordTrace (prefixWord ++ tailWord_8215989) baseStart_8215989 baseEnd_8215989 := by
    simpa [prefixWord, tailWord_8215989, baseEnd_8215989] using wordTrace_append hprefix tailTrace_8215989
  have hstable : (prefixWord ++ tailWord_8215989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215989).length < 2 ^ (prefixWord ++ tailWord_8215989).sum := by decide
  have hdescent : baseEnd_8215989 < baseStart_8215989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216011 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 4]
def baseStart_8216011 : Nat := 118140960795 + 8216011 * 2 ^ 59
def prefixEnd_8216011 : Nat := 4983230072969 + 3 ^ 40 * 8216011 * 2
def baseEnd_8216011 : Nat := 4218762705627159552877759

theorem tailTrace_8216011 : CollatzResearch.WordTrace tailWord_8216011 prefixEnd_8216011 4218762705627159552877759 := by
  unfold tailWord_8216011
  simp only [CollatzResearch.WordTrace]
  refine ⟨299662539437802804810807887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199775026291868536540538591 299662539437802804810807887)
  ·
    refine ⟨449493809156704207216211831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299662539437802804810807887 449493809156704207216211831)
    ·
      refine ⟨674240713735056310824317747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449493809156704207216211831 674240713735056310824317747)
      ·
        refine ⟨1011361070602584466236476621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674240713735056310824317747 1011361070602584466236476621)
        ·
          refine ⟨379260401475969174838678733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1011361070602584466236476621 379260401475969174838678733)
          ·
            refine ⟨142222650553488440564504525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379260401475969174838678733 142222650553488440564504525)
            ·
              refine ⟨53333493957558165211689197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142222650553488440564504525 53333493957558165211689197)
              ·
                refine ⟨20000060234084311954383449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53333493957558165211689197 20000060234084311954383449)
                ·
                  refine ⟨15000045175563233965787587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20000060234084311954383449 15000045175563233965787587)
                  ·
                    refine ⟨22500067763344850948681381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15000045175563233965787587 22500067763344850948681381)
                    ·
                      refine ⟨4218762705627159552877759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22500067763344850948681381 4218762705627159552877759)
                      ·
                        rfl

theorem cell23_8216011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 4].length) (baseStart_8216011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216011 prefixEnd_8216011 := by exact prefixLift 8216011
  have htrace : WordTrace (prefixWord ++ tailWord_8216011) baseStart_8216011 baseEnd_8216011 := by
    simpa [prefixWord, tailWord_8216011, baseEnd_8216011] using wordTrace_append hprefix tailTrace_8216011
  have hstable : (prefixWord ++ tailWord_8216011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216011).length < 2 ^ (prefixWord ++ tailWord_8216011).sum := by decide
  have hdescent : baseEnd_8216011 < baseStart_8216011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216138 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_8216138 : Nat := 118140960795 + 8216138 * 2 ^ 59
def prefixEnd_8216138 : Nat := 4983230072969 + 3 ^ 40 * 8216138 * 2
def baseEnd_8216138 : Nat := 4218827917670280555989675

theorem tailTrace_8216138 : CollatzResearch.WordTrace tailWord_8216138 prefixEnd_8216138 4218827917670280555989675 := by
  unfold tailWord_8216138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74916792877085676375170267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199778114338895137000454045 74916792877085676375170267)
  ·
    refine ⟨112375189315628514562755401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74916792877085676375170267 112375189315628514562755401)
    ·
      refine ⟨84281391986721385922066551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112375189315628514562755401 84281391986721385922066551)
      ·
        refine ⟨126422087980082078883099827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84281391986721385922066551 126422087980082078883099827)
        ·
          refine ⟨189633131970123118324649741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126422087980082078883099827 189633131970123118324649741)
          ·
            refine ⟨71112424488796169371743653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189633131970123118324649741 71112424488796169371743653)
            ·
              refine ⟨13333579591649281757201935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71112424488796169371743653 13333579591649281757201935)
              ·
                refine ⟨20000369387473922635802903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13333579591649281757201935 20000369387473922635802903)
                ·
                  refine ⟨30000554081210883953704355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20000369387473922635802903 30000554081210883953704355)
                  ·
                    refine ⟨45000831121816325930556533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30000554081210883953704355 45000831121816325930556533)
                    ·
                      refine ⟨4218827917670280555989675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45000831121816325930556533 4218827917670280555989675)
                      ·
                        rfl

theorem cell23_8216138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_8216138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216138 prefixEnd_8216138 := by exact prefixLift 8216138
  have htrace : WordTrace (prefixWord ++ tailWord_8216138) baseStart_8216138 baseEnd_8216138 := by
    simpa [prefixWord, tailWord_8216138, baseEnd_8216138] using wordTrace_append hprefix tailTrace_8216138
  have hstable : (prefixWord ++ tailWord_8216138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216138).length < 2 ^ (prefixWord ++ tailWord_8216138).sum := by decide
  have hdescent : baseEnd_8216138 < baseStart_8216138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216161 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_8216161 : Nat := 118140960795 + 8216161 * 2 ^ 59
def prefixEnd_8216161 : Nat := 4983230072969 + 3 ^ 40 * 8216161 * 2
def baseEnd_8216161 : Nat := 4218839727725333966002069

theorem tailTrace_8216161 : CollatzResearch.WordTrace tailWord_8216161 prefixEnd_8216161 4218839727725333966002069 := by
  unfold tailWord_8216161
  simp only [CollatzResearch.WordTrace]
  refine ⟨299668010387259380428768337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199778673591506253619178891 299668010387259380428768337)
  ·
    refine ⟨224751007790444535321576253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299668010387259380428768337 224751007790444535321576253)
    ·
      refine ⟨84281627921416700745591095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224751007790444535321576253 84281627921416700745591095)
      ·
        refine ⟨126422441882125051118386643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84281627921416700745591095 126422441882125051118386643)
        ·
          refine ⟨189633662823187576677579965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126422441882125051118386643 189633662823187576677579965)
          ·
            refine ⟨71112623558695341254092487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189633662823187576677579965 71112623558695341254092487)
            ·
              refine ⟨106668935338043011881138731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71112623558695341254092487 106668935338043011881138731)
              ·
                refine ⟨160003403007064517821708097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106668935338043011881138731 160003403007064517821708097)
                ·
                  refine ⟨120002552255298388366281073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160003403007064517821708097 120002552255298388366281073)
                  ·
                    refine ⟨90001914191473791274710805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120002552255298388366281073 90001914191473791274710805)
                    ·
                      refine ⟨4218839727725333966002069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90001914191473791274710805 4218839727725333966002069)
                      ·
                        rfl

theorem cell23_8216161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_8216161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216161 prefixEnd_8216161 := by exact prefixLift 8216161
  have htrace : WordTrace (prefixWord ++ tailWord_8216161) baseStart_8216161 baseEnd_8216161 := by
    simpa [prefixWord, tailWord_8216161, baseEnd_8216161] using wordTrace_append hprefix tailTrace_8216161
  have hstable : (prefixWord ++ tailWord_8216161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216161).length < 2 ^ (prefixWord ++ tailWord_8216161).sum := by decide
  have hdescent : baseEnd_8216161 < baseStart_8216161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216202 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_8216202 : Nat := 118140960795 + 8216202 * 2 ^ 59
def prefixEnd_8216202 : Nat := 4983230072969 + 3 ^ 40 * 8216202 * 2
def baseEnd_8216202 : Nat := 4218860780432168305589381

theorem tailTrace_8216202 : CollatzResearch.WordTrace tailWord_8216202 prefixEnd_8216202 4218860780432168305589381 := by
  unfold tailWord_8216202
  simp only [CollatzResearch.WordTrace]
  refine ⟨74917376445027711107752715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199779670520073896287340573 74917376445027711107752715)
  ·
    refine ⟨112376064667541566661629073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74917376445027711107752715 112376064667541566661629073)
    ·
      refine ⟨84282048500656174996221805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112376064667541566661629073 84282048500656174996221805)
      ·
        refine ⟨31605768187746065623583177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84282048500656174996221805 31605768187746065623583177)
        ·
          refine ⟨23704326140809549217687383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31605768187746065623583177 23704326140809549217687383)
          ·
            refine ⟨35556489211214323826531075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23704326140809549217687383 35556489211214323826531075)
            ·
              refine ⟨53334733816821485739796613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35556489211214323826531075 53334733816821485739796613)
              ·
                refine ⟨10000262590654028576211865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53334733816821485739796613 10000262590654028576211865)
                ·
                  refine ⟨7500196942990521432158899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10000262590654028576211865 7500196942990521432158899)
                  ·
                    refine ⟨11250295414485782148238349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7500196942990521432158899 11250295414485782148238349)
                    ·
                      refine ⟨4218860780432168305589381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11250295414485782148238349 4218860780432168305589381)
                      ·
                        rfl

theorem cell23_8216202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_8216202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216202 prefixEnd_8216202 := by exact prefixLift 8216202
  have htrace : WordTrace (prefixWord ++ tailWord_8216202) baseStart_8216202 baseEnd_8216202 := by
    simpa [prefixWord, tailWord_8216202, baseEnd_8216202] using wordTrace_append hprefix tailTrace_8216202
  have hstable : (prefixWord ++ tailWord_8216202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216202).length < 2 ^ (prefixWord ++ tailWord_8216202).sum := by decide
  have hdescent : baseEnd_8216202 < baseStart_8216202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216246 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_8216246 : Nat := 118140960795 + 8216246 * 2 ^ 59
def prefixEnd_8216246 : Nat := 4983230072969 + 3 ^ 40 * 8216246 * 2
def baseEnd_8216246 : Nat := 4218883373580966133439179

theorem tailTrace_8216246 : CollatzResearch.WordTrace tailWord_8216246 prefixEnd_8216246 4218883373580966133439179 := by
  unfold tailWord_8216246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18729444411996964996600787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199780740394634293297075061 18729444411996964996600787)
  ·
    refine ⟨28094166617995447494901181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18729444411996964996600787 28094166617995447494901181)
    ·
      refine ⟨10535312481748292810587943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28094166617995447494901181 10535312481748292810587943)
      ·
        refine ⟨15802968722622439215881915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535312481748292810587943 15802968722622439215881915)
        ·
          refine ⟨23704453083933658823822873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15802968722622439215881915 23704453083933658823822873)
          ·
            refine ⟨17778339812950244117867155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23704453083933658823822873 17778339812950244117867155)
            ·
              refine ⟨26667509719425366176800733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17778339812950244117867155 26667509719425366176800733)
              ·
                refine ⟨10000316144784512316300275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26667509719425366176800733 10000316144784512316300275)
                ·
                  refine ⟨15000474217176768474450413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10000316144784512316300275 15000474217176768474450413)
                  ·
                    refine ⟨5625177831441288177918905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15000474217176768474450413 5625177831441288177918905)
                    ·
                      refine ⟨4218883373580966133439179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625177831441288177918905 4218883373580966133439179)
                      ·
                        rfl

theorem cell23_8216246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_8216246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216246 prefixEnd_8216246 := by exact prefixLift 8216246
  have htrace : WordTrace (prefixWord ++ tailWord_8216246) baseStart_8216246 baseEnd_8216246 := by
    simpa [prefixWord, tailWord_8216246, baseEnd_8216246] using wordTrace_append hprefix tailTrace_8216246
  have hstable : (prefixWord ++ tailWord_8216246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216246).length < 2 ^ (prefixWord ++ tailWord_8216246).sum := by decide
  have hdescent : baseEnd_8216246 < baseStart_8216246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216315 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 2, 4, 2]
def baseStart_8216315 : Nat := 118140960795 + 8216315 * 2 ^ 59
def prefixEnd_8216315 : Nat := 4983230072969 + 3 ^ 40 * 8216315 * 2
def baseEnd_8216315 : Nat := 4218918803746126363476361

theorem tailTrace_8216315 : CollatzResearch.WordTrace tailWord_8216315 prefixEnd_8216315 4218918803746126363476361 := by
  unfold tailWord_8216315
  simp only [CollatzResearch.WordTrace]
  refine ⟨299673627228701464729874399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199782418152467643153249599 299673627228701464729874399)
  ·
    refine ⟨449510440843052197094811599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299673627228701464729874399 449510440843052197094811599)
    ·
      refine ⟨674265661264578295642217399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449510440843052197094811599 674265661264578295642217399)
      ·
        refine ⟨1011398491896867443463326099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674265661264578295642217399 1011398491896867443463326099)
        ·
          refine ⟨1517097737845301165194989149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011398491896867443463326099 1517097737845301165194989149)
          ·
            refine ⟨568911651691987936948120931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1517097737845301165194989149 568911651691987936948120931)
            ·
              refine ⟨853367477537981905422181397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568911651691987936948120931 853367477537981905422181397)
              ·
                refine ⟨40001600509592901816664753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 853367477537981905422181397 40001600509592901816664753)
                ·
                  refine ⟨30001200382194676362498565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40001600509592901816664753 30001200382194676362498565)
                  ·
                    refine ⟨5625225071661501817968481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30001200382194676362498565 5625225071661501817968481)
                    ·
                      refine ⟨4218918803746126363476361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625225071661501817968481 4218918803746126363476361)
                      ·
                        rfl

theorem cell23_8216315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4, 2].length) (baseStart_8216315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216315 prefixEnd_8216315 := by exact prefixLift 8216315
  have htrace : WordTrace (prefixWord ++ tailWord_8216315) baseStart_8216315 baseEnd_8216315 := by
    simpa [prefixWord, tailWord_8216315, baseEnd_8216315] using wordTrace_append hprefix tailTrace_8216315
  have hstable : (prefixWord ++ tailWord_8216315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216315).length < 2 ^ (prefixWord ++ tailWord_8216315).sum := by decide
  have hdescent : baseEnd_8216315 < baseStart_8216315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216352 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_8216352 : Nat := 118140960795 + 8216352 * 2 ^ 59
def prefixEnd_8216352 : Nat := 4983230072969 + 3 ^ 40 * 8216352 * 2
def baseEnd_8216352 : Nat := 4218937802530342718713691

theorem tailTrace_8216352 : CollatzResearch.WordTrace tailWord_8216352 prefixEnd_8216352 4218937802530342718713691 := by
  unfold tailWord_8216352
  simp only [CollatzResearch.WordTrace]
  refine ⟨149837488364783710024485655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199783317819711613365980873 149837488364783710024485655)
  ·
    refine ⟨224756232547175565036728483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149837488364783710024485655 224756232547175565036728483)
    ·
      refine ⟨337134348820763347555092725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224756232547175565036728483 337134348820763347555092725)
      ·
        refine ⟨31606345201946563833289943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337134348820763347555092725 31606345201946563833289943)
        ·
          refine ⟨47409517802919845749934915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31606345201946563833289943 47409517802919845749934915)
          ·
            refine ⟨71114276704379768624902373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47409517802919845749934915 71114276704379768624902373)
            ·
              refine ⟨13333926882071206617169195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71114276704379768624902373 13333926882071206617169195)
              ·
                refine ⟨20000890323106809925753793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13333926882071206617169195 20000890323106809925753793)
                ·
                  refine ⟨15000667742330107444315345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20000890323106809925753793 15000667742330107444315345)
                  ·
                    refine ⟨11250500806747580583236509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15000667742330107444315345 11250500806747580583236509)
                    ·
                      refine ⟨4218937802530342718713691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11250500806747580583236509 4218937802530342718713691)
                      ·
                        rfl

theorem cell23_8216352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_8216352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216352 prefixEnd_8216352 := by exact prefixLift 8216352
  have htrace : WordTrace (prefixWord ++ tailWord_8216352) baseStart_8216352 baseEnd_8216352 := by
    simpa [prefixWord, tailWord_8216352, baseEnd_8216352] using wordTrace_append hprefix tailTrace_8216352
  have hstable : (prefixWord ++ tailWord_8216352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216352).length < 2 ^ (prefixWord ++ tailWord_8216352).sum := by decide
  have hdescent : baseEnd_8216352 < baseStart_8216352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216372 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 6]
def baseStart_8216372 : Nat := 118140960795 + 8216372 * 2 ^ 59
def prefixEnd_8216372 : Nat := 4983230072969 + 3 ^ 40 * 8216372 * 2
def baseEnd_8216372 : Nat := 468772008015936960051511

theorem tailTrace_8216372 : CollatzResearch.WordTrace tailWord_8216372 prefixEnd_8216372 468772008015936960051511 := by
  unfold tailWord_8216372
  simp only [CollatzResearch.WordTrace]
  refine ⟨149837853094747481732349685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199783804126329975643132913 149837853094747481732349685)
  ·
    refine ⟨14047298727632576412407783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149837853094747481732349685 14047298727632576412407783)
    ·
      refine ⟨21070948091448864618611675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14047298727632576412407783 21070948091448864618611675)
      ·
        refine ⟨31606422137173296927917513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21070948091448864618611675 31606422137173296927917513)
        ·
          refine ⟨23704816602879972695938135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31606422137173296927917513 23704816602879972695938135)
          ·
            refine ⟨35557224904319959043907203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23704816602879972695938135 35557224904319959043907203)
            ·
              refine ⟨53335837356479938565860805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35557224904319959043907203 53335837356479938565860805)
              ·
                refine ⟨10000469504339988481098901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53335837356479938565860805 10000469504339988481098901)
                ·
                  refine ⟨468772008015936960051511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10000469504339988481098901 468772008015936960051511)
                  ·
                    rfl

theorem cell23_8216372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_8216372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216372 prefixEnd_8216372 := by exact prefixLift 8216372
  have htrace : WordTrace (prefixWord ++ tailWord_8216372) baseStart_8216372 baseEnd_8216372 := by
    simpa [prefixWord, tailWord_8216372, baseEnd_8216372] using wordTrace_append hprefix tailTrace_8216372
  have hstable : (prefixWord ++ tailWord_8216372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216372).length < 2 ^ (prefixWord ++ tailWord_8216372).sum := by decide
  have hdescent : baseEnd_8216372 < baseStart_8216372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216376 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 1, 4]
def baseStart_8216376 : Nat := 118140960795 + 8216376 * 2 ^ 59
def prefixEnd_8216376 : Nat := 4983230072969 + 3 ^ 40 * 8216376 * 2
def baseEnd_8216376 : Nat := 1406316708688683541604527

theorem tailTrace_8216376 : CollatzResearch.WordTrace tailWord_8216376 prefixEnd_8216376 1406316708688683541604527 := by
  unfold tailWord_8216376
  simp only [CollatzResearch.WordTrace]
  refine ⟨149837926040740236073922491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199783901387653648098563321 149837926040740236073922491)
  ·
    refine ⟨224756889061110354110883737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149837926040740236073922491 224756889061110354110883737)
    ·
      refine ⟨168567666795832765583162803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224756889061110354110883737 168567666795832765583162803)
      ·
        refine ⟨252851500193749148374744205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168567666795832765583162803 252851500193749148374744205)
        ·
          refine ⟨94819312572655930640529077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252851500193749148374744205 94819312572655930640529077)
          ·
            refine ⟨8889310553686493497549601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94819312572655930640529077 8889310553686493497549601)
            ·
              refine ⟨6666982915264870123162201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889310553686493497549601 6666982915264870123162201)
              ·
                refine ⟨5000237186448652592371651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6666982915264870123162201 5000237186448652592371651)
                ·
                  refine ⟨7500355779672978888557477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000237186448652592371651 7500355779672978888557477)
                  ·
                    refine ⟨1406316708688683541604527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500355779672978888557477 1406316708688683541604527)
                    ·
                      rfl

theorem cell23_8216376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_8216376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216376 prefixEnd_8216376 := by exact prefixLift 8216376
  have htrace : WordTrace (prefixWord ++ tailWord_8216376) baseStart_8216376 baseEnd_8216376 := by
    simpa [prefixWord, tailWord_8216376, baseEnd_8216376] using wordTrace_append hprefix tailTrace_8216376
  have hstable : (prefixWord ++ tailWord_8216376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216376).length < 2 ^ (prefixWord ++ tailWord_8216376).sum := by decide
  have hdescent : baseEnd_8216376 < baseStart_8216376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216415 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 1, 6]
def baseStart_8216415 : Nat := 118140960795 + 8216415 * 2 ^ 59
def prefixEnd_8216415 : Nat := 4983230072969 + 3 ^ 40 * 8216415 * 2
def baseEnd_8216415 : Nat := 1406323383937191990741967

theorem tailTrace_8216415 : CollatzResearch.WordTrace tailWord_8216415 prefixEnd_8216415 1406323383937191990741967 := by
  unfold tailWord_8216415
  simp only [CollatzResearch.WordTrace]
  refine ⟨299677274528339181808514699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199784849685559454539009799 299677274528339181808514699)
  ·
    refine ⟨449515911792508772712772049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299677274528339181808514699 449515911792508772712772049)
    ·
      refine ⟨337136933844381579534579037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449515911792508772712772049 337136933844381579534579037)
      ·
        refine ⟨126426350191643092325467139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337136933844381579534579037 126426350191643092325467139)
        ·
          refine ⟨189639525287464638488200709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126426350191643092325467139 189639525287464638488200709)
          ·
            refine ⟨35557410991399619716537633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189639525287464638488200709 35557410991399619716537633)
            ·
              refine ⟨26668058243549714787403225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35557410991399619716537633 26668058243549714787403225)
              ·
                refine ⟨20001043682662286090552419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26668058243549714787403225 20001043682662286090552419)
                ·
                  refine ⟨30001565523993429135828629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20001043682662286090552419 30001565523993429135828629)
                  ·
                    refine ⟨1406323383937191990741967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30001565523993429135828629 1406323383937191990741967)
                    ·
                      rfl

theorem cell23_8216415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_8216415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216415 prefixEnd_8216415 := by exact prefixLift 8216415
  have htrace : WordTrace (prefixWord ++ tailWord_8216415) baseStart_8216415 baseEnd_8216415 := by
    simpa [prefixWord, tailWord_8216415, baseEnd_8216415] using wordTrace_append hprefix tailTrace_8216415
  have hstable : (prefixWord ++ tailWord_8216415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216415).length < 2 ^ (prefixWord ++ tailWord_8216415).sum := by decide
  have hdescent : baseEnd_8216415 < baseStart_8216415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216416 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 1, 1, 3]
def baseStart_8216416 : Nat := 118140960795 + 8216416 * 2 ^ 59
def prefixEnd_8216416 : Nat := 4983230072969 + 3 ^ 40 * 8216416 * 2
def baseEnd_8216416 : Nat := 4218970665292230468313397

theorem tailTrace_8216416 : CollatzResearch.WordTrace tailWord_8216416 prefixEnd_8216416 4218970665292230468313397 := by
  unfold tailWord_8216416
  simp only [CollatzResearch.WordTrace]
  refine ⟨149838655500667779489650551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199784874000890372652867401 149838655500667779489650551)
  ·
    refine ⟨224757983251001669234475827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149838655500667779489650551 224757983251001669234475827)
    ·
      refine ⟨337136974876502503851713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224757983251001669234475827 337136974876502503851713741)
      ·
        refine ⟨126426365578688438944392653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337136974876502503851713741 126426365578688438944392653)
        ·
          refine ⟨47409887092008164604147245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126426365578688438944392653 47409887092008164604147245)
          ·
            refine ⟨17778707659503061726555217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47409887092008164604147245 17778707659503061726555217)
            ·
              refine ⟨13334030744627296294916413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17778707659503061726555217 13334030744627296294916413)
              ·
                refine ⟨5000261529235236110593655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13334030744627296294916413 5000261529235236110593655)
                ·
                  refine ⟨7500392293852854165890483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000261529235236110593655 7500392293852854165890483)
                  ·
                    refine ⟨11250588440779281248835725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7500392293852854165890483 11250588440779281248835725)
                    ·
                      refine ⟨4218970665292230468313397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11250588440779281248835725 4218970665292230468313397)
                      ·
                        rfl

theorem cell23_8216416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_8216416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216416 prefixEnd_8216416 := by exact prefixLift 8216416
  have htrace : WordTrace (prefixWord ++ tailWord_8216416) baseStart_8216416 baseEnd_8216416 := by
    simpa [prefixWord, tailWord_8216416, baseEnd_8216416] using wordTrace_append hprefix tailTrace_8216416
  have hstable : (prefixWord ++ tailWord_8216416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216416).length < 2 ^ (prefixWord ++ tailWord_8216416).sum := by decide
  have hdescent : baseEnd_8216416 < baseStart_8216416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216452 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_8216452 : Nat := 118140960795 + 8216452 * 2 ^ 59
def prefixEnd_8216452 : Nat := 4983230072969 + 3 ^ 40 * 8216452 * 2
def baseEnd_8216452 : Nat := 4218989150595792327463231

theorem tailTrace_8216452 : CollatzResearch.WordTrace tailWord_8216452 prefixEnd_8216452 4218989150595792327463231 := by
  unfold tailWord_8216452
  simp only [CollatzResearch.WordTrace]
  refine ⟨149839312014602568563805805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199785749352803424751741073 149839312014602568563805805)
  ·
    refine ⟨56189742005475963211427177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149839312014602568563805805 56189742005475963211427177)
    ·
      refine ⟨42142306504106972408570383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56189742005475963211427177 42142306504106972408570383)
      ·
        refine ⟨63213459756160458612855575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42142306504106972408570383 63213459756160458612855575)
        ·
          refine ⟨94820189634240687919283363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63213459756160458612855575 94820189634240687919283363)
          ·
            refine ⟨142230284451361031878925045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94820189634240687919283363 142230284451361031878925045)
            ·
              refine ⟨13334089167315096738649223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142230284451361031878925045 13334089167315096738649223)
              ·
                refine ⟨20001133750972645107973835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13334089167315096738649223 20001133750972645107973835)
                ·
                  refine ⟨30001700626458967661960753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20001133750972645107973835 30001700626458967661960753)
                  ·
                    refine ⟨22501275469844225746470565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30001700626458967661960753 22501275469844225746470565)
                    ·
                      refine ⟨4218989150595792327463231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22501275469844225746470565 4218989150595792327463231)
                      ·
                        rfl

theorem cell23_8216452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_8216452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216452 prefixEnd_8216452 := by exact prefixLift 8216452
  have htrace : WordTrace (prefixWord ++ tailWord_8216452) baseStart_8216452 baseEnd_8216452 := by
    simpa [prefixWord, tailWord_8216452, baseEnd_8216452] using wordTrace_append hprefix tailTrace_8216452
  have hstable : (prefixWord ++ tailWord_8216452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216452).length < 2 ^ (prefixWord ++ tailWord_8216452).sum := by decide
  have hdescent : baseEnd_8216452 < baseStart_8216452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216495 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_8216495 : Nat := 118140960795 + 8216495 * 2 ^ 59
def prefixEnd_8216495 : Nat := 4983230072969 + 3 ^ 40 * 8216495 * 2
def baseEnd_8216495 : Nat := 4219011230263935659225533

theorem tailTrace_8216495 : CollatzResearch.WordTrace tailWord_8216495 prefixEnd_8216495 4219011230263935659225533 := by
  unfold tailWord_8216495
  simp only [CollatzResearch.WordTrace]
  refine ⟨299680192368049355471426939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199786794912032903647617959 299680192368049355471426939)
  ·
    refine ⟨449520288552074033207140409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299680192368049355471426939 449520288552074033207140409)
    ·
      refine ⟨337140216414055524905355307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449520288552074033207140409 337140216414055524905355307)
      ·
        refine ⟨505710324621083287358032961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337140216414055524905355307 505710324621083287358032961)
        ·
          refine ⟨379282743465812465518524721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505710324621083287358032961 379282743465812465518524721)
          ·
            refine ⟨284462057599359349138893541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379282743465812465518524721 284462057599359349138893541)
            ·
              refine ⟨53336635799879877963542539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284462057599359349138893541 53336635799879877963542539)
              ·
                refine ⟨80004953699819816945313809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53336635799879877963542539 80004953699819816945313809)
                ·
                  refine ⟨60003715274864862708985357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80004953699819816945313809 60003715274864862708985357)
                  ·
                    refine ⟨22501393228074323515869509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60003715274864862708985357 22501393228074323515869509)
                    ·
                      refine ⟨4219011230263935659225533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22501393228074323515869509 4219011230263935659225533)
                      ·
                        rfl

theorem cell23_8216495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_8216495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216495 prefixEnd_8216495 := by exact prefixLift 8216495
  have htrace : WordTrace (prefixWord ++ tailWord_8216495) baseStart_8216495 baseEnd_8216495 := by
    simpa [prefixWord, tailWord_8216495, baseEnd_8216495] using wordTrace_append hprefix tailTrace_8216495
  have hstable : (prefixWord ++ tailWord_8216495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216495).length < 2 ^ (prefixWord ++ tailWord_8216495).sum := by decide
  have hdescent : baseEnd_8216495 < baseStart_8216495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216500 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_8216500 : Nat := 118140960795 + 8216500 * 2 ^ 59
def prefixEnd_8216500 : Nat := 4983230072969 + 3 ^ 40 * 8216500 * 2
def baseEnd_8216500 : Nat := 1406337932555736046554337

theorem tailTrace_8216500 : CollatzResearch.WordTrace tailWord_8216500 prefixEnd_8216500 1406337932555736046554337 := by
  unfold tailWord_8216500
  simp only [CollatzResearch.WordTrace]
  refine ⟨149840187366515620662679477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199786916488687494216905969 149840187366515620662679477)
  ·
    refine ⟨14047517565610839437126201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149840187366515620662679477 14047517565610839437126201)
    ·
      refine ⟨10535638174208129577844651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14047517565610839437126201 10535638174208129577844651)
      ·
        refine ⟨15803457261312194366766977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535638174208129577844651 15803457261312194366766977)
        ·
          refine ⟨11852592945984145775075233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15803457261312194366766977 11852592945984145775075233)
          ·
            refine ⟨8889444709488109331306425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11852592945984145775075233 8889444709488109331306425)
            ·
              refine ⟨6667083532116081998479819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889444709488109331306425 6667083532116081998479819)
              ·
                refine ⟨10000625298174122997719729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667083532116081998479819 10000625298174122997719729)
                ·
                  refine ⟨7500468973630592248289797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10000625298174122997719729 7500468973630592248289797)
                  ·
                    refine ⟨1406337932555736046554337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500468973630592248289797 1406337932555736046554337)
                    ·
                      rfl

theorem cell23_8216500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_8216500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216500 prefixEnd_8216500 := by exact prefixLift 8216500
  have htrace : WordTrace (prefixWord ++ tailWord_8216500) baseStart_8216500 baseEnd_8216500 := by
    simpa [prefixWord, tailWord_8216500, baseEnd_8216500] using wordTrace_append hprefix tailTrace_8216500
  have hstable : (prefixWord ++ tailWord_8216500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216500).length < 2 ^ (prefixWord ++ tailWord_8216500).sum := by decide
  have hdescent : baseEnd_8216500 < baseStart_8216500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216505 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_8216505 : Nat := 118140960795 + 8216505 * 2 ^ 59
def prefixEnd_8216505 : Nat := 4983230072969 + 3 ^ 40 * 8216505 * 2
def baseEnd_8216505 : Nat := 1406338788356826873366829

theorem tailTrace_8216505 : CollatzResearch.WordTrace tailWord_8216505 prefixEnd_8216505 1406338788356826873366829 := by
  unfold tailWord_8216505
  simp only [CollatzResearch.WordTrace]
  refine ⟨299680557098013127179290969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199787038065342084786193979 299680557098013127179290969)
  ·
    refine ⟨224760417823509845384468227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299680557098013127179290969 224760417823509845384468227)
    ·
      refine ⟨337140626735264768076702341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224760417823509845384468227 337140626735264768076702341)
      ·
        refine ⟨63213867512862144014381689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337140626735264768076702341 63213867512862144014381689)
        ·
          refine ⟨47410400634646608010786267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63213867512862144014381689 47410400634646608010786267)
          ·
            refine ⟨71115600951969912016179401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47410400634646608010786267 71115600951969912016179401)
            ·
              refine ⟨53336700713977434012134551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71115600951969912016179401 53336700713977434012134551)
              ·
                refine ⟨80005051070966151018201827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53336700713977434012134551 80005051070966151018201827)
                ·
                  refine ⟨120007576606449226527302741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80005051070966151018201827 120007576606449226527302741)
                  ·
                    refine ⟨1406338788356826873366829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120007576606449226527302741 1406338788356826873366829)
                    ·
                      rfl

theorem cell23_8216505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_8216505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216505 prefixEnd_8216505 := by exact prefixLift 8216505
  have htrace : WordTrace (prefixWord ++ tailWord_8216505) baseStart_8216505 baseEnd_8216505 := by
    simpa [prefixWord, tailWord_8216505, baseEnd_8216505] using wordTrace_append hprefix tailTrace_8216505
  have hstable : (prefixWord ++ tailWord_8216505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216505).length < 2 ^ (prefixWord ++ tailWord_8216505).sum := by decide
  have hdescent : baseEnd_8216505 < baseStart_8216505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216529 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 4, 2, 2]
def baseStart_8216529 : Nat := 118140960795 + 8216529 * 2 ^ 59
def prefixEnd_8216529 : Nat := 4983230072969 + 3 ^ 40 * 8216529 * 2
def baseEnd_8216529 : Nat := 4219028688606188526200377

theorem tailTrace_8216529 : CollatzResearch.WordTrace tailWord_8216529 prefixEnd_8216529 4219028688606188526200377 := by
  unfold tailWord_8216529
  simp only [CollatzResearch.WordTrace]
  refine ⟨299681432449926179278164641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199787621633284119518776427 299681432449926179278164641)
  ·
    refine ⟨224761074337444634458623481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299681432449926179278164641 224761074337444634458623481)
    ·
      refine ⟨168570805753083475843967611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224761074337444634458623481 168570805753083475843967611)
      ·
        refine ⟨252856208629625213765951417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168570805753083475843967611 252856208629625213765951417)
        ·
          refine ⟨189642156472218910324463563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252856208629625213765951417 189642156472218910324463563)
          ·
            refine ⟨284463234708328365486695345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189642156472218910324463563 284463234708328365486695345)
            ·
              refine ⟨213347426031246274115021509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284463234708328365486695345 213347426031246274115021509)
              ·
                refine ⟨40002642380858676396566533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213347426031246274115021509 40002642380858676396566533)
                ·
                  refine ⟨7500495446411001824356225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40002642380858676396566533 7500495446411001824356225)
                  ·
                    refine ⟨5625371584808251368267169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7500495446411001824356225 5625371584808251368267169)
                    ·
                      refine ⟨4219028688606188526200377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625371584808251368267169 4219028688606188526200377)
                      ·
                        rfl

theorem cell23_8216529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_8216529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216529 prefixEnd_8216529 := by exact prefixLift 8216529
  have htrace : WordTrace (prefixWord ++ tailWord_8216529) baseStart_8216529 baseEnd_8216529 := by
    simpa [prefixWord, tailWord_8216529, baseEnd_8216529] using wordTrace_append hprefix tailTrace_8216529
  have hstable : (prefixWord ++ tailWord_8216529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216529).length < 2 ^ (prefixWord ++ tailWord_8216529).sum := by decide
  have hdescent : baseEnd_8216529 < baseStart_8216529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216532 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_8216532 : Nat := 118140960795 + 8216532 * 2 ^ 59
def prefixEnd_8216532 : Nat := 4983230072969 + 3 ^ 40 * 8216532 * 2
def baseEnd_8216532 : Nat := 4219030229048152014462863

theorem tailTrace_8216532 : CollatzResearch.WordTrace tailWord_8216532 prefixEnd_8216532 4219030229048152014462863 := by
  unfold tailWord_8216532
  simp only [CollatzResearch.WordTrace]
  refine ⟨149840770934457655395261925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199787694579276873860349233 149840770934457655395261925)
  ·
    refine ⟨28095144550210810386611611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149840770934457655395261925 28095144550210810386611611)
    ·
      refine ⟨42142716825316215579917417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28095144550210810386611611 42142716825316215579917417)
      ·
        refine ⟨31607037618987161684938063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42142716825316215579917417 31607037618987161684938063)
        ·
          refine ⟨47410556428480742527407095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31607037618987161684938063 47410556428480742527407095)
          ·
            refine ⟨71115834642721113791110643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47410556428480742527407095 71115834642721113791110643)
            ·
              refine ⟨106673751964081670686665965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71115834642721113791110643 106673751964081670686665965)
              ·
                refine ⟨40002656986530626507499737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106673751964081670686665965 40002656986530626507499737)
                ·
                  refine ⟨30001992739897969880624803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40002656986530626507499737 30001992739897969880624803)
                  ·
                    refine ⟨45002989109846954820937205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30001992739897969880624803 45002989109846954820937205)
                    ·
                      refine ⟨4219030229048152014462863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45002989109846954820937205 4219030229048152014462863)
                      ·
                        rfl

theorem cell23_8216532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_8216532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216532 prefixEnd_8216532 := by exact prefixLift 8216532
  have htrace : WordTrace (prefixWord ++ tailWord_8216532) baseStart_8216532 baseEnd_8216532 := by
    simpa [prefixWord, tailWord_8216532, baseEnd_8216532] using wordTrace_append hprefix tailTrace_8216532
  have hstable : (prefixWord ++ tailWord_8216532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216532).length < 2 ^ (prefixWord ++ tailWord_8216532).sum := by decide
  have hdescent : baseEnd_8216532 < baseStart_8216532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216533 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_8216533 : Nat := 118140960795 + 8216533 * 2 ^ 59
def prefixEnd_8216533 : Nat := 4983230072969 + 3 ^ 40 * 8216533 * 2
def baseEnd_8216533 : Nat := 4219030742528806510550359

theorem tailTrace_8216533 : CollatzResearch.WordTrace tailWord_8216533 prefixEnd_8216533 4219030742528806510550359 := by
  unfold tailWord_8216533
  simp only [CollatzResearch.WordTrace]
  refine ⟨299681578341911687961310253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199787718894607791974206835 299681578341911687961310253)
  ·
    refine ⟨112380591878216882985491345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299681578341911687961310253 112380591878216882985491345)
    ·
      refine ⟨84285443908662662239118509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112380591878216882985491345 84285443908662662239118509)
      ·
        refine ⟨31607041465748498339669441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84285443908662662239118509 31607041465748498339669441)
        ·
          refine ⟨23705281099311373754752081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31607041465748498339669441 23705281099311373754752081)
          ·
            refine ⟨17778960824483530316064061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23705281099311373754752081 17778960824483530316064061)
            ·
              refine ⟨6667110309181323868524023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17778960824483530316064061 6667110309181323868524023)
              ·
                refine ⟨10000665463771985802786035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667110309181323868524023 10000665463771985802786035)
                ·
                  refine ⟨15000998195657978704179053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10000665463771985802786035 15000998195657978704179053)
                  ·
                    refine ⟨5625374323371742014067145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15000998195657978704179053 5625374323371742014067145)
                    ·
                      refine ⟨4219030742528806510550359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625374323371742014067145 4219030742528806510550359)
                      ·
                        rfl

theorem cell23_8216533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_8216533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216533 prefixEnd_8216533 := by exact prefixLift 8216533
  have htrace : WordTrace (prefixWord ++ tailWord_8216533) baseStart_8216533 baseEnd_8216533 := by
    simpa [prefixWord, tailWord_8216533, baseEnd_8216533] using wordTrace_append hprefix tailTrace_8216533
  have hstable : (prefixWord ++ tailWord_8216533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216533).length < 2 ^ (prefixWord ++ tailWord_8216533).sum := by decide
  have hdescent : baseEnd_8216533 < baseStart_8216533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216545 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_8216545 : Nat := 118140960795 + 8216545 * 2 ^ 59
def prefixEnd_8216545 : Nat := 4983230072969 + 3 ^ 40 * 8216545 * 2
def baseEnd_8216545 : Nat := 4219036904296660463600303

theorem tailTrace_8216545 : CollatzResearch.WordTrace tailWord_8216545 prefixEnd_8216545 4219036904296660463600303 := by
  unfold tailWord_8216545
  simp only [CollatzResearch.WordTrace]
  refine ⟨299682016017868214010747089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199788010678578809340498059 299682016017868214010747089)
  ·
    refine ⟨224761512013401160508060317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299682016017868214010747089 224761512013401160508060317)
    ·
      refine ⟨84285567005025435190522619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224761512013401160508060317 84285567005025435190522619)
      ·
        refine ⟨126428350507538152785783929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84285567005025435190522619 126428350507538152785783929)
        ·
          refine ⟨94821262880653614589337947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126428350507538152785783929 94821262880653614589337947)
          ·
            refine ⟨142231894320980421884006921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94821262880653614589337947 142231894320980421884006921)
            ·
              refine ⟨106673920740735316413005191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142231894320980421884006921 106673920740735316413005191)
              ·
                refine ⟨160010881111102974619507787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106673920740735316413005191 160010881111102974619507787)
                ·
                  refine ⟨240016321666654461929261681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160010881111102974619507787 240016321666654461929261681)
                  ·
                    refine ⟨180012241249990846446946261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240016321666654461929261681 180012241249990846446946261)
                    ·
                      refine ⟨4219036904296660463600303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180012241249990846446946261 4219036904296660463600303)
                      ·
                        rfl

theorem cell23_8216545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_8216545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216545 prefixEnd_8216545 := by exact prefixLift 8216545
  have htrace : WordTrace (prefixWord ++ tailWord_8216545) baseStart_8216545 baseEnd_8216545 := by
    simpa [prefixWord, tailWord_8216545, baseEnd_8216545] using wordTrace_append hprefix tailTrace_8216545
  have hstable : (prefixWord ++ tailWord_8216545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216545).length < 2 ^ (prefixWord ++ tailWord_8216545).sum := by decide
  have hdescent : baseEnd_8216545 < baseStart_8216545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216575 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_8216575 : Nat := 118140960795 + 8216575 * 2 ^ 59
def prefixEnd_8216575 : Nat := 4983230072969 + 3 ^ 40 * 8216575 * 2
def baseEnd_8216575 : Nat := 4219052308716295346225165

theorem tailTrace_8216575 : CollatzResearch.WordTrace tailWord_8216575 prefixEnd_8216575 4219052308716295346225165 := by
  unfold tailWord_8216575
  simp only [CollatzResearch.WordTrace]
  refine ⟨299683110207759529134339179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199788740138506352756226119 299683110207759529134339179)
  ·
    refine ⟨449524665311639293701508769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299683110207759529134339179 449524665311639293701508769)
    ·
      refine ⟨337143498983729470276131577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449524665311639293701508769 337143498983729470276131577)
      ·
        refine ⟨252857624237797102707098683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337143498983729470276131577 252857624237797102707098683)
        ·
          refine ⟨379286436356695654060648025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252857624237797102707098683 379286436356695654060648025)
          ·
            refine ⟨284464827267521740545486019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379286436356695654060648025 284464827267521740545486019)
            ·
              refine ⟨426697240901282610818229029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284464827267521740545486019 426697240901282610818229029)
              ·
                refine ⟨80005732668990489528417943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426697240901282610818229029 80005732668990489528417943)
                ·
                  refine ⟨120008599003485734292626915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80005732668990489528417943 120008599003485734292626915)
                  ·
                    refine ⟨180012898505228601438940373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120008599003485734292626915 180012898505228601438940373)
                    ·
                      refine ⟨4219052308716295346225165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180012898505228601438940373 4219052308716295346225165)
                      ·
                        rfl

theorem cell23_8216575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_8216575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216575 prefixEnd_8216575 := by exact prefixLift 8216575
  have htrace : WordTrace (prefixWord ++ tailWord_8216575) baseStart_8216575 baseEnd_8216575 := by
    simpa [prefixWord, tailWord_8216575, baseEnd_8216575] using wordTrace_append hprefix tailTrace_8216575
  have hstable : (prefixWord ++ tailWord_8216575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216575).length < 2 ^ (prefixWord ++ tailWord_8216575).sum := by decide
  have hdescent : baseEnd_8216575 < baseStart_8216575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216586 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_8216586 : Nat := 118140960795 + 8216586 * 2 ^ 59
def prefixEnd_8216586 : Nat := 4983230072969 + 3 ^ 40 * 8216586 * 2
def baseEnd_8216586 : Nat := 468784217444832755909735

theorem tailTrace_8216586 : CollatzResearch.WordTrace tailWord_8216586 prefixEnd_8216586 468784217444832755909735 := by
  unfold tailWord_8216586
  simp only [CollatzResearch.WordTrace]
  refine ⟨74920877852679919503247403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199789007607146452008659741 74920877852679919503247403)
  ·
    refine ⟨112381316779019879254871105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74920877852679919503247403 112381316779019879254871105)
    ·
      refine ⟨84285987584264909441153329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112381316779019879254871105 84285987584264909441153329)
      ·
        refine ⟨63214490688198682080864997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84285987584264909441153329 63214490688198682080864997)
        ·
          refine ⟨11852717004037252890162187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63214490688198682080864997 11852717004037252890162187)
          ·
            refine ⟨17779075506055879335243281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11852717004037252890162187 17779075506055879335243281)
            ·
              refine ⟨13334306629541909501432461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17779075506055879335243281 13334306629541909501432461)
              ·
                refine ⟨5000364986078216063037173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13334306629541909501432461 5000364986078216063037173)
                ·
                  refine ⟨468784217444832755909735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5000364986078216063037173 468784217444832755909735)
                  ·
                    rfl

theorem cell23_8216586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_8216586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216586 prefixEnd_8216586 := by exact prefixLift 8216586
  have htrace : WordTrace (prefixWord ++ tailWord_8216586) baseStart_8216586 baseEnd_8216586 := by
    simpa [prefixWord, tailWord_8216586, baseEnd_8216586] using wordTrace_append hprefix tailTrace_8216586
  have hstable : (prefixWord ++ tailWord_8216586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216586).length < 2 ^ (prefixWord ++ tailWord_8216586).sum := by decide
  have hdescent : baseEnd_8216586 < baseStart_8216586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216629 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_8216629 : Nat := 118140960795 + 8216629 * 2 ^ 59
def prefixEnd_8216629 : Nat := 4983230072969 + 3 ^ 40 * 8216629 * 2
def baseEnd_8216629 : Nat := 1406360012223879378316639

theorem tailTrace_8216629 : CollatzResearch.WordTrace tailWord_8216629 prefixEnd_8216629 1406360012223879378316639 := by
  unfold tailWord_8216629
  simp only [CollatzResearch.WordTrace]
  refine ⟨299685079749563896356804941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199790053166375930904536627 299685079749563896356804941)
  ·
    refine ⟨112381904906086461133801853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299685079749563896356804941 112381904906086461133801853)
    ·
      refine ⟨42143214339782422925175695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112381904906086461133801853 42143214339782422925175695)
      ·
        refine ⟨63214821509673634387763543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42143214339782422925175695 63214821509673634387763543)
        ·
          refine ⟨94822232264510451581645315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63214821509673634387763543 94822232264510451581645315)
          ·
            refine ⟨142233348396765677372467973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94822232264510451581645315 142233348396765677372467973)
            ·
              refine ⟨26668752824393564507337745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142233348396765677372467973 26668752824393564507337745)
              ·
                refine ⟨20001564618295173380503309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26668752824393564507337745 20001564618295173380503309)
                ·
                  refine ⟨7500586731860690017688741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20001564618295173380503309 7500586731860690017688741)
                  ·
                    refine ⟨1406360012223879378316639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500586731860690017688741 1406360012223879378316639)
                    ·
                      rfl

theorem cell23_8216629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_8216629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216629 prefixEnd_8216629 := by exact prefixLift 8216629
  have htrace : WordTrace (prefixWord ++ tailWord_8216629) baseStart_8216629 baseEnd_8216629 := by
    simpa [prefixWord, tailWord_8216629, baseEnd_8216629] using wordTrace_append hprefix tailTrace_8216629
  have hstable : (prefixWord ++ tailWord_8216629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216629).length < 2 ^ (prefixWord ++ tailWord_8216629).sum := by decide
  have hdescent : baseEnd_8216629 < baseStart_8216629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216686 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_8216686 : Nat := 118140960795 + 8216686 * 2 ^ 59
def prefixEnd_8216686 : Nat := 4983230072969 + 3 ^ 40 * 8216686 * 2
def baseEnd_8216686 : Nat := 4219109305068944411937155

theorem tailTrace_8216686 : CollatzResearch.WordTrace tailWord_8216686 prefixEnd_8216686 4219109305068944411937155 := by
  unfold tailWord_8216686
  simp only [CollatzResearch.WordTrace]
  refine ⟨37460894838794674386453739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199791439140238263394419941 37460894838794674386453739)
  ·
    refine ⟨56191342258192011579680609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37460894838794674386453739 56191342258192011579680609)
    ·
      refine ⟨42143506693644008684760457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56191342258192011579680609 42143506693644008684760457)
      ·
        refine ⟨31607630020233006513570343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42143506693644008684760457 31607630020233006513570343)
        ·
          refine ⟨47411445030349509770355515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31607630020233006513570343 47411445030349509770355515)
          ·
            refine ⟨71117167545524264655533273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47411445030349509770355515 71117167545524264655533273)
            ·
              refine ⟨53337875659143198491649955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71117167545524264655533273 53337875659143198491649955)
              ·
                refine ⟨80006813488714797737474933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53337875659143198491649955 80006813488714797737474933)
                ·
                  refine ⟨7500638764567012287888275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80006813488714797737474933 7500638764567012287888275)
                  ·
                    refine ⟨11250958146850518431832413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7500638764567012287888275 11250958146850518431832413)
                    ·
                      refine ⟨4219109305068944411937155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11250958146850518431832413 4219109305068944411937155)
                      ·
                        rfl

theorem cell23_8216686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_8216686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216686 prefixEnd_8216686 := by exact prefixLift 8216686
  have htrace : WordTrace (prefixWord ++ tailWord_8216686) baseStart_8216686 baseEnd_8216686 := by
    simpa [prefixWord, tailWord_8216686, baseEnd_8216686] using wordTrace_append hprefix tailTrace_8216686
  have hstable : (prefixWord ++ tailWord_8216686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216686).length < 2 ^ (prefixWord ++ tailWord_8216686).sum := by decide
  have hdescent : baseEnd_8216686 < baseStart_8216686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216736 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 2, 4]
def baseStart_8216736 : Nat := 118140960795 + 8216736 * 2 ^ 59
def prefixEnd_8216736 : Nat := 4983230072969 + 3 ^ 40 * 8216736 * 2
def baseEnd_8216736 : Nat := 1406378326367223072103975

theorem tailTrace_8216736 : CollatzResearch.WordTrace tailWord_8216736 prefixEnd_8216736 1406378326367223072103975 := by
  unfold tailWord_8216736
  simp only [CollatzResearch.WordTrace]
  refine ⟨149844491180088126815475031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199792654906784169087300041 149844491180088126815475031)
  ·
    refine ⟨224766736770132190223212547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149844491180088126815475031 224766736770132190223212547)
    ·
      refine ⟨337150105155198285334818821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224766736770132190223212547 337150105155198285334818821)
      ·
        refine ⟨63215644716599678500278529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337150105155198285334818821 63215644716599678500278529)
        ·
          refine ⟨47411733537449758875208897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63215644716599678500278529 47411733537449758875208897)
          ·
            refine ⟨35558800153087319156406673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47411733537449758875208897 35558800153087319156406673)
            ·
              refine ⟨26669100114815489367305005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35558800153087319156406673 26669100114815489367305005)
              ·
                refine ⟨10000912543055808512739377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26669100114815489367305005 10000912543055808512739377)
                ·
                  refine ⟨7500684407291856384554533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10000912543055808512739377 7500684407291856384554533)
                  ·
                    refine ⟨1406378326367223072103975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500684407291856384554533 1406378326367223072103975)
                    ·
                      rfl

theorem cell23_8216736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_8216736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216736 prefixEnd_8216736 := by exact prefixLift 8216736
  have htrace : WordTrace (prefixWord ++ tailWord_8216736) baseStart_8216736 baseEnd_8216736 := by
    simpa [prefixWord, tailWord_8216736, baseEnd_8216736] using wordTrace_append hprefix tailTrace_8216736
  have hstable : (prefixWord ++ tailWord_8216736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216736).length < 2 ^ (prefixWord ++ tailWord_8216736).sum := by decide
  have hdescent : baseEnd_8216736 < baseStart_8216736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216757 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_8216757 : Nat := 118140960795 + 8216757 * 2 ^ 59
def prefixEnd_8216757 : Nat := 4983230072969 + 3 ^ 40 * 8216757 * 2
def baseEnd_8216757 : Nat := 1406381920731804544716443

theorem tailTrace_8216757 : CollatzResearch.WordTrace tailWord_8216757 prefixEnd_8216757 1406381920731804544716443 := by
  unfold tailWord_8216757
  simp only [CollatzResearch.WordTrace]
  refine ⟨299689748293100174217464525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199793165528733449478309683 299689748293100174217464525)
  ·
    refine ⟨112383655609912565331549197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299689748293100174217464525 112383655609912565331549197)
    ·
      refine ⟨42143870853717211999330949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112383655609912565331549197 42143870853717211999330949)
      ·
        refine ⟨7901975785071977249874553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42143870853717211999330949 7901975785071977249874553)
        ·
          refine ⟨5926481838803982937405915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7901975785071977249874553 5926481838803982937405915)
          ·
            refine ⟨8889722758205974406108873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926481838803982937405915 8889722758205974406108873)
            ·
              refine ⟨6667292068654480804581655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889722758205974406108873 6667292068654480804581655)
              ·
                refine ⟨10000938102981721206872483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667292068654480804581655 10000938102981721206872483)
                ·
                  refine ⟨15001407154472581810308725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10000938102981721206872483 15001407154472581810308725)
                  ·
                    refine ⟨1406381920731804544716443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15001407154472581810308725 1406381920731804544716443)
                    ·
                      rfl

theorem cell23_8216757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_8216757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216757 prefixEnd_8216757 := by exact prefixLift 8216757
  have htrace : WordTrace (prefixWord ++ tailWord_8216757) baseStart_8216757 baseEnd_8216757 := by
    simpa [prefixWord, tailWord_8216757, baseEnd_8216757] using wordTrace_append hprefix tailTrace_8216757
  have hstable : (prefixWord ++ tailWord_8216757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216757).length < 2 ^ (prefixWord ++ tailWord_8216757).sum := by decide
  have hdescent : baseEnd_8216757 < baseStart_8216757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216760 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 1, 2, 2]
def baseStart_8216760 : Nat := 118140960795 + 8216760 * 2 ^ 59
def prefixEnd_8216760 : Nat := 4983230072969 + 3 ^ 40 * 8216760 * 2
def baseEnd_8216760 : Nat := 4219147302637377122411815

theorem tailTrace_8216760 : CollatzResearch.WordTrace tailWord_8216760 prefixEnd_8216760 4219147302637377122411815 := by
  unfold tailWord_8216760
  simp only [CollatzResearch.WordTrace]
  refine ⟨149844928856044652864911867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199793238474726203819882489 149844928856044652864911867)
  ·
    refine ⟨224767393284066979297367801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149844928856044652864911867 224767393284066979297367801)
    ·
      refine ⟨168575544963050234473025851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224767393284066979297367801 168575544963050234473025851)
      ·
        refine ⟨252863317444575351709538777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168575544963050234473025851 252863317444575351709538777)
        ·
          refine ⟨189647488083431513782154083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252863317444575351709538777 189647488083431513782154083)
          ·
            refine ⟨284471232125147270673231125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189647488083431513782154083 284471232125147270673231125)
            ·
              refine ⟨13334589005866278312807709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284471232125147270673231125 13334589005866278312807709)
              ·
                refine ⟨5000470877199854367302891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13334589005866278312807709 5000470877199854367302891)
                ·
                  refine ⟨7500706315799781550954337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000470877199854367302891 7500706315799781550954337)
                  ·
                    refine ⟨5625529736849836163215753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7500706315799781550954337 5625529736849836163215753)
                    ·
                      refine ⟨4219147302637377122411815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625529736849836163215753 4219147302637377122411815)
                      ·
                        rfl

theorem cell23_8216760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_8216760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216760 prefixEnd_8216760 := by exact prefixLift 8216760
  have htrace : WordTrace (prefixWord ++ tailWord_8216760) baseStart_8216760 baseEnd_8216760 := by
    simpa [prefixWord, tailWord_8216760, baseEnd_8216760] using wordTrace_append hprefix tailTrace_8216760
  have hstable : (prefixWord ++ tailWord_8216760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216760).length < 2 ^ (prefixWord ++ tailWord_8216760).sum := by decide
  have hdescent : baseEnd_8216760 < baseStart_8216760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216770 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_8216770 : Nat := 118140960795 + 8216770 * 2 ^ 59
def prefixEnd_8216770 : Nat := 4983230072969 + 3 ^ 40 * 8216770 * 2
def baseEnd_8216770 : Nat := 1406384145814640694428923

theorem tailTrace_8216770 : CollatzResearch.WordTrace tailWord_8216770 prefixEnd_8216770 1406384145814640694428923 := by
  unfold tailWord_8216770
  simp only [CollatzResearch.WordTrace]
  refine ⟨74922555610513269359421941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199793481628035384958458509 74922555610513269359421941)
  ·
    refine ⟨7023989588485619002445807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74922555610513269359421941 7023989588485619002445807)
    ·
      refine ⟨10535984382728428503668711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7023989588485619002445807 10535984382728428503668711)
      ·
        refine ⟨15803976574092642755503067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535984382728428503668711 15803976574092642755503067)
        ·
          refine ⟨23705964861138964133254601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15803976574092642755503067 23705964861138964133254601)
          ·
            refine ⟨17779473645854223099940951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23705964861138964133254601 17779473645854223099940951)
            ·
              refine ⟨26669210468781334649911427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17779473645854223099940951 26669210468781334649911427)
              ·
                refine ⟨40003815703172001974867141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26669210468781334649911427 40003815703172001974867141)
                ·
                  refine ⟨7500715444344750370287589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40003815703172001974867141 7500715444344750370287589)
                  ·
                    refine ⟨1406384145814640694428923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500715444344750370287589 1406384145814640694428923)
                    ·
                      rfl

theorem cell23_8216770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_8216770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216770 prefixEnd_8216770 := by exact prefixLift 8216770
  have htrace : WordTrace (prefixWord ++ tailWord_8216770) baseStart_8216770 baseEnd_8216770 := by
    simpa [prefixWord, tailWord_8216770, baseEnd_8216770] using wordTrace_append hprefix tailTrace_8216770
  have hstable : (prefixWord ++ tailWord_8216770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216770).length < 2 ^ (prefixWord ++ tailWord_8216770).sum := by decide
  have hdescent : baseEnd_8216770 < baseStart_8216770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216790 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_8216790 : Nat := 118140960795 + 8216790 * 2 ^ 59
def prefixEnd_8216790 : Nat := 4983230072969 + 3 ^ 40 * 8216790 * 2
def baseEnd_8216790 : Nat := 4219162707057012005036677

theorem tailTrace_8216790 : CollatzResearch.WordTrace tailWord_8216790 prefixEnd_8216790 4219162707057012005036677 := by
  unfold tailWord_8216790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730684493873788803338489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199793967934653747235610549 18730684493873788803338489)
  ·
    refine ⟨14048013370405341602503867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18730684493873788803338489 14048013370405341602503867)
    ·
      refine ⟨21072020055608012403755801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14048013370405341602503867 21072020055608012403755801)
      ·
        refine ⟨15804015041706009302816851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21072020055608012403755801 15804015041706009302816851)
        ·
          refine ⟨23706022562559013954225277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15804015041706009302816851 23706022562559013954225277)
          ·
            refine ⟨8889758460959630232834479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23706022562559013954225277 8889758460959630232834479)
            ·
              refine ⟨13334637691439445349251719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889758460959630232834479 13334637691439445349251719)
              ·
                refine ⟨20001956537159168023877579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13334637691439445349251719 20001956537159168023877579)
                ·
                  refine ⟨30002934805738752035816369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20001956537159168023877579 30002934805738752035816369)
                  ·
                    refine ⟨22502201104304064026862277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30002934805738752035816369 22502201104304064026862277)
                    ·
                      refine ⟨4219162707057012005036677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22502201104304064026862277 4219162707057012005036677)
                      ·
                        rfl

theorem cell23_8216790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_8216790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216790 prefixEnd_8216790 := by exact prefixLift 8216790
  have htrace : WordTrace (prefixWord ++ tailWord_8216790) baseStart_8216790 baseEnd_8216790 := by
    simpa [prefixWord, tailWord_8216790, baseEnd_8216790] using wordTrace_append hprefix tailTrace_8216790
  have hstable : (prefixWord ++ tailWord_8216790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216790).length < 2 ^ (prefixWord ++ tailWord_8216790).sum := by decide
  have hdescent : baseEnd_8216790 < baseStart_8216790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216816 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 1, 4, 2]
def baseStart_8216816 : Nat := 118140960795 + 8216816 * 2 ^ 59
def prefixEnd_8216816 : Nat := 4983230072969 + 3 ^ 40 * 8216816 * 2
def baseEnd_8216816 : Nat := 4219176057554028903311557

theorem tailTrace_8216816 : CollatzResearch.WordTrace tailWord_8216816 prefixEnd_8216816 4219176057554028903311557 := by
  unfold tailWord_8216816
  simp only [CollatzResearch.WordTrace]
  refine ⟨149845950099943213646931151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199794600133257618195908201 149845950099943213646931151)
  ·
    refine ⟨224768925149914820470396727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149845950099943213646931151 224768925149914820470396727)
    ·
      refine ⟨337153387724872230705595091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224768925149914820470396727 337153387724872230705595091)
      ·
        refine ⟨505730081587308346058392637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337153387724872230705595091 505730081587308346058392637)
        ·
          refine ⟨189648780595240629771897239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505730081587308346058392637 189648780595240629771897239)
          ·
            refine ⟨284473170892860944657845859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189648780595240629771897239 284473170892860944657845859)
            ·
              refine ⟨426709756339291416986768789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284473170892860944657845859 426709756339291416986768789)
              ·
                refine ⟨20002019828404285171254787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 426709756339291416986768789 20002019828404285171254787)
                ·
                  refine ⟨30003029742606427756882181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20002019828404285171254787 30003029742606427756882181)
                  ·
                    refine ⟨5625568076738705204415409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30003029742606427756882181 5625568076738705204415409)
                    ·
                      refine ⟨4219176057554028903311557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625568076738705204415409 4219176057554028903311557)
                      ·
                        rfl

theorem cell23_8216816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 4, 2].length) (baseStart_8216816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216816 prefixEnd_8216816 := by exact prefixLift 8216816
  have htrace : WordTrace (prefixWord ++ tailWord_8216816) baseStart_8216816 baseEnd_8216816 := by
    simpa [prefixWord, tailWord_8216816, baseEnd_8216816] using wordTrace_append hprefix tailTrace_8216816
  have hstable : (prefixWord ++ tailWord_8216816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216816).length < 2 ^ (prefixWord ++ tailWord_8216816).sum := by decide
  have hdescent : baseEnd_8216816 < baseStart_8216816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216819 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5]
def baseStart_8216819 : Nat := 118140960795 + 8216819 * 2 ^ 59
def prefixEnd_8216819 : Nat := 4983230072969 + 3 ^ 40 * 8216819 * 2
def baseEnd_8216819 : Nat := 4219177597995992391574043

theorem tailTrace_8216819 : CollatzResearch.WordTrace tailWord_8216819 prefixEnd_8216819 4219177597995992391574043 := by
  unfold tailWord_8216819
  simp only [CollatzResearch.WordTrace]
  refine ⟨299692009618875558806221511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199794673079250372537481007 299692009618875558806221511)
  ·
    refine ⟨449538014428313338209332267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299692009618875558806221511 449538014428313338209332267)
    ·
      refine ⟨674307021642470007313998401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449538014428313338209332267 674307021642470007313998401)
      ·
        refine ⟨505730266231852505485498801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674307021642470007313998401 505730266231852505485498801)
        ·
          refine ⟨379297699673889379114124101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505730266231852505485498801 379297699673889379114124101)
          ·
            refine ⟨71118318688854258583898269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379297699673889379114124101 71118318688854258583898269)
            ·
              refine ⟨26669369508320346968961851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71118318688854258583898269 26669369508320346968961851)
              ·
                refine ⟨40004054262480520453442777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26669369508320346968961851 40004054262480520453442777)
                ·
                  refine ⟨30003040696860390340082083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40004054262480520453442777 30003040696860390340082083)
                  ·
                    refine ⟨45004561045290585510123125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30003040696860390340082083 45004561045290585510123125)
                    ·
                      refine ⟨4219177597995992391574043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45004561045290585510123125 4219177597995992391574043)
                      ·
                        rfl

theorem cell23_8216819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_8216819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216819 prefixEnd_8216819 := by exact prefixLift 8216819
  have htrace : WordTrace (prefixWord ++ tailWord_8216819) baseStart_8216819 baseEnd_8216819 := by
    simpa [prefixWord, tailWord_8216819, baseEnd_8216819] using wordTrace_append hprefix tailTrace_8216819
  have hstable : (prefixWord ++ tailWord_8216819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216819).length < 2 ^ (prefixWord ++ tailWord_8216819).sum := by decide
  have hdescent : baseEnd_8216819 < baseStart_8216819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216829 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_8216829 : Nat := 118140960795 + 8216829 * 2 ^ 59
def prefixEnd_8216829 : Nat := 4983230072969 + 3 ^ 40 * 8216829 * 2
def baseEnd_8216829 : Nat := 4219182732802537352448997

theorem tailTrace_8216829 : CollatzResearch.WordTrace tailWord_8216829 prefixEnd_8216829 4219182732802537352448997 := by
  unfold tailWord_8216829
  simp only [CollatzResearch.WordTrace]
  refine ⟨299692374348839330514085541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199794916232559553676057027 299692374348839330514085541)
  ·
    refine ⟨56192320190407374471391039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299692374348839330514085541 56192320190407374471391039)
    ·
      refine ⟨84288480285611061707086559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56192320190407374471391039 84288480285611061707086559)
      ·
        refine ⟨126432720428416592560629839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84288480285611061707086559 126432720428416592560629839)
        ·
          refine ⟨189649080642624888840944759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126432720428416592560629839 189649080642624888840944759)
          ·
            refine ⟨284473620963937333261417139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189649080642624888840944759 284473620963937333261417139)
            ·
              refine ⟨426710431445905999892125709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284473620963937333261417139 426710431445905999892125709)
              ·
                refine ⟨160016411792214749959547141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426710431445905999892125709 160016411792214749959547141)
                ·
                  refine ⟨30003077211040265617415089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160016411792214749959547141 30003077211040265617415089)
                  ·
                    refine ⟨22502307908280199213061317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30003077211040265617415089 22502307908280199213061317)
                    ·
                      refine ⟨4219182732802537352448997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22502307908280199213061317 4219182732802537352448997)
                      ·
                        rfl

theorem cell23_8216829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_8216829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216829 prefixEnd_8216829 := by exact prefixLift 8216829
  have htrace : WordTrace (prefixWord ++ tailWord_8216829) baseStart_8216829 baseEnd_8216829 := by
    simpa [prefixWord, tailWord_8216829, baseEnd_8216829] using wordTrace_append hprefix tailTrace_8216829
  have hstable : (prefixWord ++ tailWord_8216829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216829).length < 2 ^ (prefixWord ++ tailWord_8216829).sum := by decide
  have hdescent : baseEnd_8216829 < baseStart_8216829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216833 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_8216833 : Nat := 118140960795 + 8216833 * 2 ^ 59
def prefixEnd_8216833 : Nat := 4983230072969 + 3 ^ 40 * 8216833 * 2
def baseEnd_8216833 : Nat := 4219184786725155336798979

theorem tailTrace_8216833 : CollatzResearch.WordTrace tailWord_8216833 prefixEnd_8216833 4219184786725155336798979 := by
  unfold tailWord_8216833
  simp only [CollatzResearch.WordTrace]
  refine ⟨299692520240824839197231153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199795013493883226131487435 299692520240824839197231153)
  ·
    refine ⟨224769390180618629397923365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299692520240824839197231153 224769390180618629397923365)
    ·
      refine ⟨42144260658865993012110631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224769390180618629397923365 42144260658865993012110631)
      ·
        refine ⟨63216390988298989518165947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42144260658865993012110631 63216390988298989518165947)
        ·
          refine ⟨94824586482448484277248921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63216390988298989518165947 94824586482448484277248921)
          ·
            refine ⟨71118439861836363207936691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94824586482448484277248921 71118439861836363207936691)
            ·
              refine ⟨106677659792754544811905037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71118439861836363207936691 106677659792754544811905037)
              ·
                refine ⟨40004122422282954304464389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106677659792754544811905037 40004122422282954304464389)
                ·
                  refine ⟨7500772954178053932087073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40004122422282954304464389 7500772954178053932087073)
                  ·
                    refine ⟨5625579715633540449065305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7500772954178053932087073 5625579715633540449065305)
                    ·
                      refine ⟨4219184786725155336798979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625579715633540449065305 4219184786725155336798979)
                      ·
                        rfl

theorem cell23_8216833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_8216833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216833 prefixEnd_8216833 := by exact prefixLift 8216833
  have htrace : WordTrace (prefixWord ++ tailWord_8216833) baseStart_8216833 baseEnd_8216833 := by
    simpa [prefixWord, tailWord_8216833, baseEnd_8216833] using wordTrace_append hprefix tailTrace_8216833
  have hstable : (prefixWord ++ tailWord_8216833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216833).length < 2 ^ (prefixWord ++ tailWord_8216833).sum := by decide
  have hdescent : baseEnd_8216833 < baseStart_8216833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216871 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_8216871 : Nat := 118140960795 + 8216871 * 2 ^ 59
def prefixEnd_8216871 : Nat := 4983230072969 + 3 ^ 40 * 8216871 * 2
def baseEnd_8216871 : Nat := 4219204298990026188123805

theorem tailTrace_8216871 : CollatzResearch.WordTrace tailWord_8216871 prefixEnd_8216871 4219204298990026188123805 := by
  unfold tailWord_8216871
  simp only [CollatzResearch.WordTrace]
  refine ⟨299693906214687171687114467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199795937476458114458076311 299693906214687171687114467)
  ·
    refine ⟨449540859322030757530671701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299693906214687171687114467 449540859322030757530671701)
    ·
      refine ⟨5268056945180047939812559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 449540859322030757530671701 5268056945180047939812559)
      ·
        refine ⟨7902085417770071909718839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268056945180047939812559 7902085417770071909718839)
        ·
          refine ⟨11853128126655107864578259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902085417770071909718839 11853128126655107864578259)
          ·
            refine ⟨17779692189982661796867389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853128126655107864578259 17779692189982661796867389)
            ·
              refine ⟨6667384571243498173825271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17779692189982661796867389 6667384571243498173825271)
              ·
                refine ⟨10001076856865247260737907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667384571243498173825271 10001076856865247260737907)
                ·
                  refine ⟨15001615285297870891106861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10001076856865247260737907 15001615285297870891106861)
                  ·
                    refine ⟨5625605731986701584165073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15001615285297870891106861 5625605731986701584165073)
                    ·
                      refine ⟨4219204298990026188123805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625605731986701584165073 4219204298990026188123805)
                      ·
                        rfl

theorem cell23_8216871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_8216871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216871 prefixEnd_8216871 := by exact prefixLift 8216871
  have htrace : WordTrace (prefixWord ++ tailWord_8216871) baseStart_8216871 baseEnd_8216871 := by
    simpa [prefixWord, tailWord_8216871, baseEnd_8216871] using wordTrace_append hprefix tailTrace_8216871
  have hstable : (prefixWord ++ tailWord_8216871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216871).length < 2 ^ (prefixWord ++ tailWord_8216871).sum := by decide
  have hdescent : baseEnd_8216871 < baseStart_8216871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216879 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_8216879 : Nat := 118140960795 + 8216879 * 2 ^ 59
def prefixEnd_8216879 : Nat := 4983230072969 + 3 ^ 40 * 8216879 * 2
def baseEnd_8216879 : Nat := 4219208406835262156823767

theorem tailTrace_8216879 : CollatzResearch.WordTrace tailWord_8216879 prefixEnd_8216879 4219208406835262156823767 := by
  unfold tailWord_8216879
  simp only [CollatzResearch.WordTrace]
  refine ⟨299694197998658189053405691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199796131999105459368937127 299694197998658189053405691)
  ·
    refine ⟨449541296997987283580108537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299694197998658189053405691 449541296997987283580108537)
    ·
      refine ⟨337155972748490462685081403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449541296997987283580108537 337155972748490462685081403)
      ·
        refine ⟨505733959122735694027622105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337155972748490462685081403 505733959122735694027622105)
        ·
          refine ⟨379300469342051770520716579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505733959122735694027622105 379300469342051770520716579)
          ·
            refine ⟨568950704013077655781074869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379300469342051770520716579 568950704013077655781074869)
            ·
              refine ⟨53339128501226030229475769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 568950704013077655781074869 53339128501226030229475769)
              ·
                refine ⟨40004346375919522672106827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53339128501226030229475769 40004346375919522672106827)
                ·
                  refine ⟨60006519563879284008160241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40004346375919522672106827 60006519563879284008160241)
                  ·
                    refine ⟨45004889672909463006120181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60006519563879284008160241 45004889672909463006120181)
                    ·
                      refine ⟨4219208406835262156823767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45004889672909463006120181 4219208406835262156823767)
                      ·
                        rfl

theorem cell23_8216879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_8216879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216879 prefixEnd_8216879 := by exact prefixLift 8216879
  have htrace : WordTrace (prefixWord ++ tailWord_8216879) baseStart_8216879 baseEnd_8216879 := by
    simpa [prefixWord, tailWord_8216879, baseEnd_8216879] using wordTrace_append hprefix tailTrace_8216879
  have hstable : (prefixWord ++ tailWord_8216879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216879).length < 2 ^ (prefixWord ++ tailWord_8216879).sum := by decide
  have hdescent : baseEnd_8216879 < baseStart_8216879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216890 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_8216890 : Nat := 118140960795 + 8216890 * 2 ^ 59
def prefixEnd_8216890 : Nat := 4983230072969 + 3 ^ 40 * 8216890 * 2
def baseEnd_8216890 : Nat := 468801561680273512642913

theorem tailTrace_8216890 : CollatzResearch.WordTrace tailWord_8216890 prefixEnd_8216890 468801561680273512642913 := by
  unfold tailWord_8216890
  simp only [CollatzResearch.WordTrace]
  refine ⟨74923649800404584483014031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199796399467745558621370749 74923649800404584483014031)
  ·
    refine ⟨112385474700606876724521047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74923649800404584483014031 112385474700606876724521047)
    ·
      refine ⟨168578212050910315086781571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112385474700606876724521047 168578212050910315086781571)
      ·
        refine ⟨252867318076365472630172357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168578212050910315086781571 252867318076365472630172357)
        ·
          refine ⟨47412622139318526118157317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252867318076365472630172357 47412622139318526118157317)
          ·
            refine ⟨8889866651122223647154497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47412622139318526118157317 8889866651122223647154497)
            ·
              refine ⟨6667399988341667735365873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889866651122223647154497 6667399988341667735365873)
              ·
                refine ⟨5000549991256250801524405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6667399988341667735365873 5000549991256250801524405)
                ·
                  refine ⟨468801561680273512642913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5000549991256250801524405 468801561680273512642913)
                  ·
                    rfl

theorem cell23_8216890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_8216890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216890 prefixEnd_8216890 := by exact prefixLift 8216890
  have htrace : WordTrace (prefixWord ++ tailWord_8216890) baseStart_8216890 baseEnd_8216890 := by
    simpa [prefixWord, tailWord_8216890, baseEnd_8216890] using wordTrace_append hprefix tailTrace_8216890
  have hstable : (prefixWord ++ tailWord_8216890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216890).length < 2 ^ (prefixWord ++ tailWord_8216890).sum := by decide
  have hdescent : baseEnd_8216890 < baseStart_8216890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216900 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_8216900 : Nat := 118140960795 + 8216900 * 2 ^ 59
def prefixEnd_8216900 : Nat := 4983230072969 + 3 ^ 40 * 8216900 * 2
def baseEnd_8216900 : Nat := 4219219189929006574661171

theorem tailTrace_8216900 : CollatzResearch.WordTrace tailWord_8216900 prefixEnd_8216900 4219219189929006574661171 := by
  unfold tailWord_8216900
  simp only [CollatzResearch.WordTrace]
  refine ⟨149847481965791054819960077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199796642621054739759946769 149847481965791054819960077)
  ·
    refine ⟨56192805737171645557485029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149847481965791054819960077 56192805737171645557485029)
    ·
      refine ⟨10536151075719683542028443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56192805737171645557485029 10536151075719683542028443)
      ·
        refine ⟨15804226613579525313042665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536151075719683542028443 15804226613579525313042665)
        ·
          refine ⟨11853169960184643984781999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15804226613579525313042665 11853169960184643984781999)
          ·
            refine ⟨17779754940276965977172999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853169960184643984781999 17779754940276965977172999)
            ·
              refine ⟨26669632410415448965759499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17779754940276965977172999 26669632410415448965759499)
              ·
                refine ⟨40004448615623173448639249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26669632410415448965759499 40004448615623173448639249)
                ·
                  refine ⟨30003336461717380086479437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40004448615623173448639249 30003336461717380086479437)
                  ·
                    refine ⟨11251251173144017532429789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30003336461717380086479437 11251251173144017532429789)
                    ·
                      refine ⟨4219219189929006574661171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251251173144017532429789 4219219189929006574661171)
                      ·
                        rfl

theorem cell23_8216900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_8216900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216900 prefixEnd_8216900 := by exact prefixLift 8216900
  have htrace : WordTrace (prefixWord ++ tailWord_8216900) baseStart_8216900 baseEnd_8216900 := by
    simpa [prefixWord, tailWord_8216900, baseEnd_8216900] using wordTrace_append hprefix tailTrace_8216900
  have hstable : (prefixWord ++ tailWord_8216900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216900).length < 2 ^ (prefixWord ++ tailWord_8216900).sum := by decide
  have hdescent : baseEnd_8216900 < baseStart_8216900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216936 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_8216936 : Nat := 118140960795 + 8216936 * 2 ^ 59
def prefixEnd_8216936 : Nat := 4983230072969 + 3 ^ 40 * 8216936 * 2
def baseEnd_8216936 : Nat := 4219237675232568433811005

theorem tailTrace_8216936 : CollatzResearch.WordTrace tailWord_8216936 prefixEnd_8216936 4219237675232568433811005 := by
  unfold tailWord_8216936
  simp only [CollatzResearch.WordTrace]
  refine ⟨149848138479725843894115331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199797517972967791858820441 149848138479725843894115331)
  ·
    refine ⟨224772207719588765841172997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149848138479725843894115331 224772207719588765841172997)
    ·
      refine ⟨42144788947422893595219937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224772207719588765841172997 42144788947422893595219937)
      ·
        refine ⟨31608591710567170196414953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42144788947422893595219937 31608591710567170196414953)
        ·
          refine ⟨23706443782925377647311215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31608591710567170196414953 23706443782925377647311215)
          ·
            refine ⟨35559665674388066470966823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23706443782925377647311215 35559665674388066470966823)
            ·
              refine ⟨53339498511582099706450235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35559665674388066470966823 53339498511582099706450235)
              ·
                refine ⟨80009247767373149559675353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53339498511582099706450235 80009247767373149559675353)
                ·
                  refine ⟨60006935825529862169756515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80009247767373149559675353 60006935825529862169756515)
                  ·
                    refine ⟨90010403738294793254634773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60006935825529862169756515 90010403738294793254634773)
                    ·
                      refine ⟨4219237675232568433811005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90010403738294793254634773 4219237675232568433811005)
                      ·
                        rfl

theorem cell23_8216936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_8216936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216936 prefixEnd_8216936 := by exact prefixLift 8216936
  have htrace : WordTrace (prefixWord ++ tailWord_8216936) baseStart_8216936 baseEnd_8216936 := by
    simpa [prefixWord, tailWord_8216936, baseEnd_8216936] using wordTrace_append hprefix tailTrace_8216936
  have hstable : (prefixWord ++ tailWord_8216936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216936).length < 2 ^ (prefixWord ++ tailWord_8216936).sum := by decide
  have hdescent : baseEnd_8216936 < baseStart_8216936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216946 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_8216946 : Nat := 118140960795 + 8216946 * 2 ^ 59
def prefixEnd_8216946 : Nat := 4983230072969 + 3 ^ 40 * 8216946 * 2
def baseEnd_8216946 : Nat := 468804756671012599409551

theorem tailTrace_8216946 : CollatzResearch.WordTrace tailWord_8216946 prefixEnd_8216946 468804756671012599409551 := by
  unfold tailWord_8216946
  simp only [CollatzResearch.WordTrace]
  refine ⟨74924160422353864874023673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199797761126276972997396461 74924160422353864874023673)
  ·
    refine ⟨56193120316765398655517755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74924160422353864874023673 56193120316765398655517755)
    ·
      refine ⟨84289680475148097983276633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56193120316765398655517755 84289680475148097983276633)
      ·
        refine ⟨63217260356361073487457475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84289680475148097983276633 63217260356361073487457475)
        ·
          refine ⟨94825890534541610231186213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63217260356361073487457475 94825890534541610231186213)
          ·
            refine ⟨17779854475226551918347415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94825890534541610231186213 17779854475226551918347415)
            ·
              refine ⟨26669781712839827877521123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17779854475226551918347415 26669781712839827877521123)
              ·
                refine ⟨40004672569259741816281685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26669781712839827877521123 40004672569259741816281685)
                ·
                  refine ⟨468804756671012599409551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40004672569259741816281685 468804756671012599409551)
                  ·
                    rfl

theorem cell23_8216946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_8216946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216946 prefixEnd_8216946 := by exact prefixLift 8216946
  have htrace : WordTrace (prefixWord ++ tailWord_8216946) baseStart_8216946 baseEnd_8216946 := by
    simpa [prefixWord, tailWord_8216946, baseEnd_8216946] using wordTrace_append hprefix tailTrace_8216946
  have hstable : (prefixWord ++ tailWord_8216946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216946).length < 2 ^ (prefixWord ++ tailWord_8216946).sum := by decide
  have hdescent : baseEnd_8216946 < baseStart_8216946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216983 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 1, 5, 2]
def baseStart_8216983 : Nat := 118140960795 + 8216983 * 2 ^ 59
def prefixEnd_8216983 : Nat := 4983230072969 + 3 ^ 40 * 8216983 * 2
def baseEnd_8216983 : Nat := 4219261808823329749923289

theorem tailTrace_8216983 : CollatzResearch.WordTrace tailWord_8216983 prefixEnd_8216983 4219261808823329749923289 := by
  unfold tailWord_8216983
  simp only [CollatzResearch.WordTrace]
  refine ⟨299697991190281414815191603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199798660793520943210127735 299697991190281414815191603)
  ·
    refine ⟨449546986785422122222787405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299697991190281414815191603 449546986785422122222787405)
    ·
      refine ⟨168580120044533295833545277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449546986785422122222787405 168580120044533295833545277)
      ·
        refine ⟨63217545016699985937579479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168580120044533295833545277 63217545016699985937579479)
        ·
          refine ⟨94826317525049978906369219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63217545016699985937579479 94826317525049978906369219)
          ·
            refine ⟨142239476287574968359553829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94826317525049978906369219 142239476287574968359553829)
            ·
              refine ⟨26669901803920306567416343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142239476287574968359553829 26669901803920306567416343)
              ·
                refine ⟨40004852705880459851124515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26669901803920306567416343 40004852705880459851124515)
                ·
                  refine ⟨60007279058820689776686773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40004852705880459851124515 60007279058820689776686773)
                  ·
                    refine ⟨5625682411764439666564385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60007279058820689776686773 5625682411764439666564385)
                    ·
                      refine ⟨4219261808823329749923289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625682411764439666564385 4219261808823329749923289)
                      ·
                        rfl

theorem cell23_8216983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_8216983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216983 prefixEnd_8216983 := by exact prefixLift 8216983
  have htrace : WordTrace (prefixWord ++ tailWord_8216983) baseStart_8216983 baseEnd_8216983 := by
    simpa [prefixWord, tailWord_8216983, baseEnd_8216983] using wordTrace_append hprefix tailTrace_8216983
  have hstable : (prefixWord ++ tailWord_8216983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216983).length < 2 ^ (prefixWord ++ tailWord_8216983).sum := by decide
  have hdescent : baseEnd_8216983 < baseStart_8216983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217016 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_8217016 : Nat := 118140960795 + 8217016 * 2 ^ 59
def prefixEnd_8217016 : Nat := 4983230072969 + 3 ^ 40 * 8217016 * 2
def baseEnd_8217016 : Nat := 4219278753684928120810637

theorem tailTrace_8217016 : CollatzResearch.WordTrace tailWord_8217016 prefixEnd_8217016 4219278753684928120810637 := by
  unfold tailWord_8217016
  simp only [CollatzResearch.WordTrace]
  refine ⟨149849597399580930725571451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199799463199441240967428601 149849597399580930725571451)
  ·
    refine ⟨224774396099371396088357177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149849597399580930725571451 224774396099371396088357177)
    ·
      refine ⟨168580797074528547066267883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224774396099371396088357177 168580797074528547066267883)
      ·
        refine ⟨252871195611792820599401825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168580797074528547066267883 252871195611792820599401825)
        ·
          refine ⟨189653396708844615449551369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252871195611792820599401825 189653396708844615449551369)
          ·
            refine ⟨142240047531633461587163527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189653396708844615449551369 142240047531633461587163527)
            ·
              refine ⟨213360071297450192380745291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142240047531633461587163527 213360071297450192380745291)
              ·
                refine ⟨320040106946175288571117937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213360071297450192380745291 320040106946175288571117937)
                ·
                  refine ⟨240030080209631466428338453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320040106946175288571117937 240030080209631466428338453)
                  ·
                    refine ⟨11251410009826474988828365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 240030080209631466428338453 11251410009826474988828365)
                    ·
                      refine ⟨4219278753684928120810637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251410009826474988828365 4219278753684928120810637)
                      ·
                        rfl

theorem cell23_8217016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_8217016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217016 prefixEnd_8217016 := by exact prefixLift 8217016
  have htrace : WordTrace (prefixWord ++ tailWord_8217016) baseStart_8217016 baseEnd_8217016 := by
    simpa [prefixWord, tailWord_8217016, baseEnd_8217016] using wordTrace_append hprefix tailTrace_8217016
  have hstable : (prefixWord ++ tailWord_8217016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217016).length < 2 ^ (prefixWord ++ tailWord_8217016).sum := by decide
  have hdescent : baseEnd_8217016 < baseStart_8217016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217063 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_8217063 : Nat := 118140960795 + 8217063 * 2 ^ 59
def prefixEnd_8217063 : Nat := 4983230072969 + 3 ^ 40 * 8217063 * 2
def baseEnd_8217063 : Nat := 4219302887275689436922921

theorem tailTrace_8217063 : CollatzResearch.WordTrace tailWord_8217063 prefixEnd_8217063 4219302887275689436922921 := by
  unfold tailWord_8217063
  simp only [CollatzResearch.WordTrace]
  refine ⟨299700909029991588478103843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199800606019994392318735895 299700909029991588478103843)
  ·
    refine ⟨449551363544987382717155765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299700909029991588478103843 449551363544987382717155765)
    ·
      refine ⟨42145440332342567129733353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449551363544987382717155765 42145440332342567129733353)
      ·
        refine ⟨31609080249256925347300015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42145440332342567129733353 31609080249256925347300015)
        ·
          refine ⟨47413620373885388020950023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31609080249256925347300015 47413620373885388020950023)
          ·
            refine ⟨71120430560828082031425035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47413620373885388020950023 71120430560828082031425035)
            ·
              refine ⟨106680645841242123047137553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71120430560828082031425035 106680645841242123047137553)
              ·
                refine ⟨80010484380931592285353165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106680645841242123047137553 80010484380931592285353165)
                ·
                  refine ⟨30003931642849347107007437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80010484380931592285353165 30003931642849347107007437)
                  ·
                    refine ⟨11251474366068505165127789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30003931642849347107007437 11251474366068505165127789)
                    ·
                      refine ⟨4219302887275689436922921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251474366068505165127789 4219302887275689436922921)
                      ·
                        rfl

theorem cell23_8217063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_8217063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217063 prefixEnd_8217063 := by exact prefixLift 8217063
  have htrace : WordTrace (prefixWord ++ tailWord_8217063) baseStart_8217063 baseEnd_8217063 := by
    simpa [prefixWord, tailWord_8217063, baseEnd_8217063] using wordTrace_append hprefix tailTrace_8217063
  have hstable : (prefixWord ++ tailWord_8217063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217063).length < 2 ^ (prefixWord ++ tailWord_8217063).sum := by decide
  have hdescent : baseEnd_8217063 < baseStart_8217063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217064 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_8217064 : Nat := 118140960795 + 8217064 * 2 ^ 59
def prefixEnd_8217064 : Nat := 4983230072969 + 3 ^ 40 * 8217064 * 2
def baseEnd_8217064 : Nat := 4219303400756343933010417

theorem tailTrace_8217064 : CollatzResearch.WordTrace tailWord_8217064 prefixEnd_8217064 4219303400756343933010417 := by
  unfold tailWord_8217064
  simp only [CollatzResearch.WordTrace]
  refine ⟨149850472751493982824445123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199800630335325310432593497 149850472751493982824445123)
  ·
    refine ⟨224775709127240974236667685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149850472751493982824445123 224775709127240974236667685)
    ·
      refine ⟨42145445461357682669375191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224775709127240974236667685 42145445461357682669375191)
      ·
        refine ⟨63218168192036524004062787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42145445461357682669375191 63218168192036524004062787)
        ·
          refine ⟨94827252288054786006094181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63218168192036524004062787 94827252288054786006094181)
          ·
            refine ⟨17780109804010272376142659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94827252288054786006094181 17780109804010272376142659)
            ·
              refine ⟨26670164706015408564213989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17780109804010272376142659 26670164706015408564213989)
              ·
                refine ⟨5000655882377889105790123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26670164706015408564213989 5000655882377889105790123)
                ·
                  refine ⟨7500983823566833658685185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000655882377889105790123 7500983823566833658685185)
                  ·
                    refine ⟨5625737867675125244013889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7500983823566833658685185 5625737867675125244013889)
                    ·
                      refine ⟨4219303400756343933010417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625737867675125244013889 4219303400756343933010417)
                      ·
                        rfl

theorem cell23_8217064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_8217064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217064 prefixEnd_8217064 := by exact prefixLift 8217064
  have htrace : WordTrace (prefixWord ++ tailWord_8217064) baseStart_8217064 baseEnd_8217064 := by
    simpa [prefixWord, tailWord_8217064, baseEnd_8217064] using wordTrace_append hprefix tailTrace_8217064
  have hstable : (prefixWord ++ tailWord_8217064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217064).length < 2 ^ (prefixWord ++ tailWord_8217064).sum := by decide
  have hdescent : baseEnd_8217064 < baseStart_8217064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217077 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_8217077 : Nat := 118140960795 + 8217077 * 2 ^ 59
def prefixEnd_8217077 : Nat := 4983230072969 + 3 ^ 40 * 8217077 * 2
def baseEnd_8217077 : Nat := 4219310076004852382147857

theorem tailTrace_8217077 : CollatzResearch.WordTrace tailWord_8217077 prefixEnd_8217077 4219310076004852382147857 := by
  unfold tailWord_8217077
  simp only [CollatzResearch.WordTrace]
  refine ⟨299701419651940868869113485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199800946434627245912742323 299701419651940868869113485)
  ·
    refine ⟨112388032369477825825917557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299701419651940868869113485 112388032369477825825917557)
    ·
      refine ⟨10536378034638546171179771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112388032369477825825917557 10536378034638546171179771)
      ·
        refine ⟨15804567051957819256769657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536378034638546171179771 15804567051957819256769657)
        ·
          refine ⟨11853425288968364442577243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15804567051957819256769657 11853425288968364442577243)
          ·
            refine ⟨17780137933452546663865865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853425288968364442577243 17780137933452546663865865)
            ·
              refine ⟨13335103450089409997899399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17780137933452546663865865 13335103450089409997899399)
              ·
                refine ⟨20002655175134114996849099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13335103450089409997899399 20002655175134114996849099)
                ·
                  refine ⟨30003982762701172495273649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20002655175134114996849099 30003982762701172495273649)
                  ·
                    refine ⟨22502987072025879371455237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30003982762701172495273649 22502987072025879371455237)
                    ·
                      refine ⟨4219310076004852382147857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22502987072025879371455237 4219310076004852382147857)
                      ·
                        rfl

theorem cell23_8217077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_8217077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217077 prefixEnd_8217077 := by exact prefixLift 8217077
  have htrace : WordTrace (prefixWord ++ tailWord_8217077) baseStart_8217077 baseEnd_8217077 := by
    simpa [prefixWord, tailWord_8217077, baseEnd_8217077] using wordTrace_append hprefix tailTrace_8217077
  have hstable : (prefixWord ++ tailWord_8217077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217077).length < 2 ^ (prefixWord ++ tailWord_8217077).sum := by decide
  have hdescent : baseEnd_8217077 < baseStart_8217077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217080 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_8217080 : Nat := 118140960795 + 8217080 * 2 ^ 59
def prefixEnd_8217080 : Nat := 4983230072969 + 3 ^ 40 * 8217080 * 2
def baseEnd_8217080 : Nat := 4219311616446815870410343

theorem tailTrace_8217080 : CollatzResearch.WordTrace tailWord_8217080 prefixEnd_8217080 4219311616446815870410343 := by
  unfold tailWord_8217080
  simp only [CollatzResearch.WordTrace]
  refine ⟨149850764535465000190736347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199801019380620000254315129 149850764535465000190736347)
  ·
    refine ⟨224776146803197500286104521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149850764535465000190736347 224776146803197500286104521)
    ·
      refine ⟨168582110102398125214578391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224776146803197500286104521 168582110102398125214578391)
      ·
        refine ⟨252873165153597187821867587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168582110102398125214578391 252873165153597187821867587)
        ·
          refine ⟨379309747730395781732801381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252873165153597187821867587 379309747730395781732801381)
          ·
            refine ⟨71120577699449209074900259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379309747730395781732801381 71120577699449209074900259)
            ·
              refine ⟨106680866549173813612350389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71120577699449209074900259 106680866549173813612350389)
              ·
                refine ⟨10001331238985045026157849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106680866549173813612350389 10001331238985045026157849)
                ·
                  refine ⟨7500998429238783769618387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10001331238985045026157849 7500998429238783769618387)
                  ·
                    refine ⟨11251497643858175654427581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7500998429238783769618387 11251497643858175654427581)
                    ·
                      refine ⟨4219311616446815870410343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251497643858175654427581 4219311616446815870410343)
                      ·
                        rfl

theorem cell23_8217080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_8217080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217080 prefixEnd_8217080 := by exact prefixLift 8217080
  have htrace : WordTrace (prefixWord ++ tailWord_8217080) baseStart_8217080 baseEnd_8217080 := by
    simpa [prefixWord, tailWord_8217080, baseEnd_8217080] using wordTrace_append hprefix tailTrace_8217080
  have hstable : (prefixWord ++ tailWord_8217080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217080).length < 2 ^ (prefixWord ++ tailWord_8217080).sum := by decide
  have hdescent : baseEnd_8217080 < baseStart_8217080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217094 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_8217094 : Nat := 118140960795 + 8217094 * 2 ^ 59
def prefixEnd_8217094 : Nat := 4983230072969 + 3 ^ 40 * 8217094 * 2
def baseEnd_8217094 : Nat := 4219318805175978815635279

theorem tailTrace_8217094 : CollatzResearch.WordTrace tailWord_8217094 prefixEnd_8217094 4219318805175978815635279 := by
  unfold tailWord_8217094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365688740402477524140073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199801359795252853848321557 9365688740402477524140073)
  ·
    refine ⟨7024266555301858143105055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9365688740402477524140073 7024266555301858143105055)
    ·
      refine ⟨10536399832952787214657583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024266555301858143105055 10536399832952787214657583)
      ·
        refine ⟨15804599749429180821986375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536399832952787214657583 15804599749429180821986375)
        ·
          refine ⟨23706899624143771232979563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15804599749429180821986375 23706899624143771232979563)
          ·
            refine ⟨35560349436215656849469345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23706899624143771232979563 35560349436215656849469345)
            ·
              refine ⟨26670262077161742637102009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35560349436215656849469345 26670262077161742637102009)
              ·
                refine ⟨20002696557871306977826507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26670262077161742637102009 20002696557871306977826507)
                ·
                  refine ⟨30004044836806960466739761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20002696557871306977826507 30004044836806960466739761)
                  ·
                    refine ⟨22503033627605220350054821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30004044836806960466739761 22503033627605220350054821)
                    ·
                      refine ⟨4219318805175978815635279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22503033627605220350054821 4219318805175978815635279)
                      ·
                        rfl

theorem cell23_8217094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_8217094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217094 prefixEnd_8217094 := by exact prefixLift 8217094
  have htrace : WordTrace (prefixWord ++ tailWord_8217094) baseStart_8217094 baseEnd_8217094 := by
    simpa [prefixWord, tailWord_8217094, baseEnd_8217094] using wordTrace_append hprefix tailTrace_8217094
  have hstable : (prefixWord ++ tailWord_8217094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217094).length < 2 ^ (prefixWord ++ tailWord_8217094).sum := by decide
  have hdescent : baseEnd_8217094 < baseStart_8217094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217096 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_8217096 : Nat := 118140960795 + 8217096 * 2 ^ 59
def prefixEnd_8217096 : Nat := 4983230072969 + 3 ^ 40 * 8217096 * 2
def baseEnd_8217096 : Nat := 1406439944045762602603423

theorem tailTrace_8217096 : CollatzResearch.WordTrace tailWord_8217096 prefixEnd_8217096 1406439944045762602603423 := by
  unfold tailWord_8217096
  simp only [CollatzResearch.WordTrace]
  refine ⟨149851056319436017557027571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199801408425914690076036761 149851056319436017557027571)
  ·
    refine ⟨224776584479154026335541357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149851056319436017557027571 224776584479154026335541357)
    ·
      refine ⟨84291219179682759875828009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224776584479154026335541357 84291219179682759875828009)
      ·
        refine ⟨63218414384762069906871007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84291219179682759875828009 63218414384762069906871007)
        ·
          refine ⟨94827621577143104860306511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63218414384762069906871007 94827621577143104860306511)
          ·
            refine ⟨142241432365714657290459767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94827621577143104860306511 142241432365714657290459767)
            ·
              refine ⟨213362148548571985935689651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142241432365714657290459767 213362148548571985935689651)
              ·
                refine ⟨320043222822857978903534477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213362148548571985935689651 320043222822857978903534477)
                ·
                  refine ⟨120016208558571742088825429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320043222822857978903534477 120016208558571742088825429)
                  ·
                    refine ⟨1406439944045762602603423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120016208558571742088825429 1406439944045762602603423)
                    ·
                      rfl

theorem cell23_8217096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_8217096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217096 prefixEnd_8217096 := by exact prefixLift 8217096
  have htrace : WordTrace (prefixWord ++ tailWord_8217096) baseStart_8217096 baseEnd_8217096 := by
    simpa [prefixWord, tailWord_8217096, baseEnd_8217096] using wordTrace_append hprefix tailTrace_8217096
  have hstable : (prefixWord ++ tailWord_8217096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217096).length < 2 ^ (prefixWord ++ tailWord_8217096).sum := by decide
  have hdescent : baseEnd_8217096 < baseStart_8217096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217101 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_8217101 : Nat := 118140960795 + 8217101 * 2 ^ 59
def prefixEnd_8217101 : Nat := 4983230072969 + 3 ^ 40 * 8217101 * 2
def baseEnd_8217101 : Nat := 4219322399540560288247747

theorem tailTrace_8217101 : CollatzResearch.WordTrace tailWord_8217101 prefixEnd_8217101 4219322399540560288247747 := by
  unfold tailWord_8217101
  simp only [CollatzResearch.WordTrace]
  refine ⟨299702295003853920967987157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199801530002569280645324771 299702295003853920967987157)
  ·
    refine ⟨7024272539152826272687199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 299702295003853920967987157 7024272539152826272687199)
    ·
      refine ⟨10536408808729239409030799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024272539152826272687199 10536408808729239409030799)
      ·
        refine ⟨15804613213093859113546199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536408808729239409030799 15804613213093859113546199)
        ·
          refine ⟨23706919819640788670319299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15804613213093859113546199 23706919819640788670319299)
          ·
            refine ⟨35560379729461183005478949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23706919819640788670319299 35560379729461183005478949)
            ·
              refine ⟨6667571199273971813527303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35560379729461183005478949 6667571199273971813527303)
              ·
                refine ⟨10001356798910957720290955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667571199273971813527303 10001356798910957720290955)
                ·
                  refine ⟨15002035198366436580436433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10001356798910957720290955 15002035198366436580436433)
                  ·
                    refine ⟨11251526398774827435327325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15002035198366436580436433 11251526398774827435327325)
                    ·
                      refine ⟨4219322399540560288247747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251526398774827435327325 4219322399540560288247747)
                      ·
                        rfl

theorem cell23_8217101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_8217101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217101 prefixEnd_8217101 := by exact prefixLift 8217101
  have htrace : WordTrace (prefixWord ++ tailWord_8217101) baseStart_8217101 baseEnd_8217101 := by
    simpa [prefixWord, tailWord_8217101, baseEnd_8217101] using wordTrace_append hprefix tailTrace_8217101
  have hstable : (prefixWord ++ tailWord_8217101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217101).length < 2 ^ (prefixWord ++ tailWord_8217101).sum := by decide
  have hdescent : baseEnd_8217101 < baseStart_8217101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217137 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 2, 2, 2]
def baseStart_8217137 : Nat := 118140960795 + 8217137 * 2 ^ 59
def prefixEnd_8217137 : Nat := 4983230072969 + 3 ^ 40 * 8217137 * 2
def baseEnd_8217137 : Nat := 4219340884844122147397581

theorem tailTrace_8217137 : CollatzResearch.WordTrace tailWord_8217137 prefixEnd_8217137 4219340884844122147397581 := by
  unfold tailWord_8217137
  simp only [CollatzResearch.WordTrace]
  refine ⟨299703608031723499116297665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199802405354482332744198443 299703608031723499116297665)
  ·
    refine ⟨224777706023792624337223249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299703608031723499116297665 224777706023792624337223249)
    ·
      refine ⟨168583279517844468252917437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224777706023792624337223249 168583279517844468252917437)
      ·
        refine ⟨63218729819191675594844039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168583279517844468252917437 63218729819191675594844039)
        ·
          refine ⟨94828094728787513392266059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63218729819191675594844039 94828094728787513392266059)
          ·
            refine ⟨142242142093181270088399089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94828094728787513392266059 142242142093181270088399089)
            ·
              refine ⟨106681606569885952566299317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142242142093181270088399089 106681606569885952566299317)
              ·
                refine ⟨10001400615926808053090561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106681606569885952566299317 10001400615926808053090561)
                ·
                  refine ⟨7501050461945106039817921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10001400615926808053090561 7501050461945106039817921)
                  ·
                    refine ⟨5625787846458829529863441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7501050461945106039817921 5625787846458829529863441)
                    ·
                      refine ⟨4219340884844122147397581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625787846458829529863441 4219340884844122147397581)
                      ·
                        rfl

theorem cell23_8217137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_8217137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217137 prefixEnd_8217137 := by exact prefixLift 8217137
  have htrace : WordTrace (prefixWord ++ tailWord_8217137) baseStart_8217137 baseEnd_8217137 := by
    simpa [prefixWord, tailWord_8217137, baseEnd_8217137] using wordTrace_append hprefix tailTrace_8217137
  have hstable : (prefixWord ++ tailWord_8217137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217137).length < 2 ^ (prefixWord ++ tailWord_8217137).sum := by decide
  have hdescent : baseEnd_8217137 < baseStart_8217137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217173 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_8217173 : Nat := 118140960795 + 8217173 * 2 ^ 59
def prefixEnd_8217173 : Nat := 4983230072969 + 3 ^ 40 * 8217173 * 2
def baseEnd_8217173 : Nat := 1406453123382561335515805

theorem tailTrace_8217173 : CollatzResearch.WordTrace tailWord_8217173 prefixEnd_8217173 1406453123382561335515805 := by
  unfold tailWord_8217173
  simp only [CollatzResearch.WordTrace]
  refine ⟨299704921059593077264608173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199803280706395384843072115 299704921059593077264608173)
  ·
    refine ⟨112389345397347403974228065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299704921059593077264608173 112389345397347403974228065)
    ·
      refine ⟨84292009048010552980671049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112389345397347403974228065 84292009048010552980671049)
      ·
        refine ⟨63219006786007914735503287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84292009048010552980671049 63219006786007914735503287)
        ·
          refine ⟨94828510179011872103254931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63219006786007914735503287 94828510179011872103254931)
          ·
            refine ⟨142242765268517808154882397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94828510179011872103254931 142242765268517808154882397)
            ·
              refine ⟨53341036975694178058080899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142242765268517808154882397 53341036975694178058080899)
              ·
                refine ⟨80011555463541267087121349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53341036975694178058080899 80011555463541267087121349)
                ·
                  refine ⟨15002166649413987578835253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80011555463541267087121349 15002166649413987578835253)
                  ·
                    refine ⟨1406453123382561335515805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15002166649413987578835253 1406453123382561335515805)
                    ·
                      rfl

theorem cell23_8217173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_8217173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217173 prefixEnd_8217173 := by exact prefixLift 8217173
  have htrace : WordTrace (prefixWord ++ tailWord_8217173) baseStart_8217173 baseEnd_8217173 := by
    simpa [prefixWord, tailWord_8217173, baseEnd_8217173] using wordTrace_append hprefix tailTrace_8217173
  have hstable : (prefixWord ++ tailWord_8217173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217173).length < 2 ^ (prefixWord ++ tailWord_8217173).sum := by decide
  have hdescent : baseEnd_8217173 < baseStart_8217173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217182 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_8217182 : Nat := 118140960795 + 8217182 * 2 ^ 59
def prefixEnd_8217182 : Nat := 4983230072969 + 3 ^ 40 * 8217182 * 2
def baseEnd_8217182 : Nat := 4219363991473574471334875

theorem tailTrace_8217182 : CollatzResearch.WordTrace tailWord_8217182 prefixEnd_8217182 4219363991473574471334875 := by
  unfold tailWord_8217182
  simp only [CollatzResearch.WordTrace]
  refine ⟨37463156164570058975210725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199803499544373647867790533 37463156164570058975210725)
  ·
    refine ⟨7024341780856886057852011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37463156164570058975210725 7024341780856886057852011)
    ·
      refine ⟨10536512671285329086778017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024341780856886057852011 10536512671285329086778017)
      ·
        refine ⟨7902384503463996815083513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10536512671285329086778017 7902384503463996815083513)
        ·
          refine ⟨5926788377597997611312635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7902384503463996815083513 5926788377597997611312635)
          ·
            refine ⟨8890182566396996416968953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926788377597997611312635 8890182566396996416968953)
            ·
              refine ⟨6667636924797747312726715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890182566396996416968953 6667636924797747312726715)
              ·
                refine ⟨10001455387196620969090073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667636924797747312726715 10001455387196620969090073)
                ·
                  refine ⟨7501091540397465726817555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10001455387196620969090073 7501091540397465726817555)
                  ·
                    refine ⟨11251637310596198590226333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501091540397465726817555 11251637310596198590226333)
                    ·
                      refine ⟨4219363991473574471334875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251637310596198590226333 4219363991473574471334875)
                      ·
                        rfl

theorem cell23_8217182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_8217182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217182 prefixEnd_8217182 := by exact prefixLift 8217182
  have htrace : WordTrace (prefixWord ++ tailWord_8217182) baseStart_8217182 baseEnd_8217182 := by
    simpa [prefixWord, tailWord_8217182, baseEnd_8217182] using wordTrace_append hprefix tailTrace_8217182
  have hstable : (prefixWord ++ tailWord_8217182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217182).length < 2 ^ (prefixWord ++ tailWord_8217182).sum := by decide
  have hdescent : baseEnd_8217182 < baseStart_8217182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217193 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_8217193 : Nat := 118140960795 + 8217193 * 2 ^ 59
def prefixEnd_8217193 : Nat := 4983230072969 + 3 ^ 40 * 8217193 * 2
def baseEnd_8217193 : Nat := 4219369639760773928297323

theorem tailTrace_8217193 : CollatzResearch.WordTrace tailWord_8217193 prefixEnd_8217193 4219369639760773928297323 := by
  unfold tailWord_8217193
  simp only [CollatzResearch.WordTrace]
  refine ⟨299705650519520620680336233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199803767013013747120224155 299705650519520620680336233)
  ·
    refine ⟨224779237889640465510252175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299705650519520620680336233 224779237889640465510252175)
    ·
      refine ⟨337168856834460698265378263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224779237889640465510252175 337168856834460698265378263)
      ·
        refine ⟨505753285251691047398067395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337168856834460698265378263 505753285251691047398067395)
        ·
          refine ⟨758629927877536571097101093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505753285251691047398067395 758629927877536571097101093)
          ·
            refine ⟨142243111477038107080706455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 758629927877536571097101093 142243111477038107080706455)
            ·
              refine ⟨213364667215557160621059683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142243111477038107080706455 213364667215557160621059683)
              ·
                refine ⟨320047000823335740931589525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213364667215557160621059683 320047000823335740931589525)
                ·
                  refine ⟨15002203163593862856168259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320047000823335740931589525 15002203163593862856168259)
                  ·
                    refine ⟨22503304745390794284252389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15002203163593862856168259 22503304745390794284252389)
                    ·
                      refine ⟨4219369639760773928297323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22503304745390794284252389 4219369639760773928297323)
                      ·
                        rfl

theorem cell23_8217193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_8217193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217193 prefixEnd_8217193 := by exact prefixLift 8217193
  have htrace : WordTrace (prefixWord ++ tailWord_8217193) baseStart_8217193 baseEnd_8217193 := by
    simpa [prefixWord, tailWord_8217193, baseEnd_8217193] using wordTrace_append hprefix tailTrace_8217193
  have hstable : (prefixWord ++ tailWord_8217193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217193).length < 2 ^ (prefixWord ++ tailWord_8217193).sum := by decide
  have hdescent : baseEnd_8217193 < baseStart_8217193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217223 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_8217223 : Nat := 118140960795 + 8217223 * 2 ^ 59
def prefixEnd_8217223 : Nat := 4983230072969 + 3 ^ 40 * 8217223 * 2
def baseEnd_8217223 : Nat := 4219385044180408810922185

theorem tailTrace_8217223 : CollatzResearch.WordTrace tailWord_8217223 prefixEnd_8217223 4219385044180408810922185 := by
  unfold tailWord_8217223
  simp only [CollatzResearch.WordTrace]
  refine ⟨299706744709411935803928323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199804496472941290535952215 299706744709411935803928323)
  ·
    refine ⟨449560117064117903705892485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299706744709411935803928323 449560117064117903705892485)
    ·
      refine ⟨84292521949522106944854841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449560117064117903705892485 84292521949522106944854841)
      ·
        refine ⟨63219391462141580208641131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84292521949522106944854841 63219391462141580208641131)
        ·
          refine ⟨94829087193212370312961697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63219391462141580208641131 94829087193212370312961697)
          ·
            refine ⟨71121815394909277734721273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94829087193212370312961697 71121815394909277734721273)
            ·
              refine ⟨53341361546181958301040955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71121815394909277734721273 53341361546181958301040955)
              ·
                refine ⟨80012042319272937451561433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53341361546181958301040955 80012042319272937451561433)
                ·
                  refine ⟨60009031739454703088671075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80012042319272937451561433 60009031739454703088671075)
                  ·
                    refine ⟨90013547609182054633006613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60009031739454703088671075 90013547609182054633006613)
                    ·
                      refine ⟨4219385044180408810922185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90013547609182054633006613 4219385044180408810922185)
                      ·
                        rfl

theorem cell23_8217223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_8217223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217223 prefixEnd_8217223 := by exact prefixLift 8217223
  have htrace : WordTrace (prefixWord ++ tailWord_8217223) baseStart_8217223 baseEnd_8217223 := by
    simpa [prefixWord, tailWord_8217223, baseEnd_8217223] using wordTrace_append hprefix tailTrace_8217223
  have hstable : (prefixWord ++ tailWord_8217223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217223).length < 2 ^ (prefixWord ++ tailWord_8217223).sum := by decide
  have hdescent : baseEnd_8217223 < baseStart_8217223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217243 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 3]
def baseStart_8217243 : Nat := 118140960795 + 8217243 * 2 ^ 59
def prefixEnd_8217243 : Nat := 4983230072969 + 3 ^ 40 * 8217243 * 2
def baseEnd_8217243 : Nat := 4219395313793498732672093

theorem tailTrace_8217243 : CollatzResearch.WordTrace tailWord_8217243 prefixEnd_8217243 4219395313793498732672093 := by
  unfold tailWord_8217243
  simp only [CollatzResearch.WordTrace]
  refine ⟨299707474169339479219656383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199804982779559652813104255 299707474169339479219656383)
  ·
    refine ⟨449561211254009218829484575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299707474169339479219656383 449561211254009218829484575)
    ·
      refine ⟨674341816881013828244226863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449561211254009218829484575 674341816881013828244226863)
      ·
        refine ⟨1011512725321520742366340295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674341816881013828244226863 1011512725321520742366340295)
        ·
          refine ⟨1517269087982281113549510443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011512725321520742366340295 1517269087982281113549510443)
          ·
            refine ⟨2275903631973421670324265665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517269087982281113549510443 2275903631973421670324265665)
            ·
              refine ⟨1706927723980066252743199249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275903631973421670324265665 1706927723980066252743199249)
              ·
                refine ⟨1280195792985049689557399437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706927723980066252743199249 1280195792985049689557399437)
                ·
                  refine ⟨480073422369393633584024789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1280195792985049689557399437 480073422369393633584024789)
                  ·
                    refine ⟨11251720836782663287125581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 480073422369393633584024789 11251720836782663287125581)
                    ·
                      refine ⟨4219395313793498732672093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251720836782663287125581 4219395313793498732672093)
                      ·
                        rfl

theorem cell23_8217243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 3].length) (baseStart_8217243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217243 prefixEnd_8217243 := by exact prefixLift 8217243
  have htrace : WordTrace (prefixWord ++ tailWord_8217243) baseStart_8217243 baseEnd_8217243 := by
    simpa [prefixWord, tailWord_8217243, baseEnd_8217243] using wordTrace_append hprefix tailTrace_8217243
  have hstable : (prefixWord ++ tailWord_8217243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217243).length < 2 ^ (prefixWord ++ tailWord_8217243).sum := by decide
  have hdescent : baseEnd_8217243 < baseStart_8217243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217273 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_8217273 : Nat := 118140960795 + 8217273 * 2 ^ 59
def prefixEnd_8217273 : Nat := 4983230072969 + 3 ^ 40 * 8217273 * 2
def baseEnd_8217273 : Nat := 4219410718213133615296955

theorem tailTrace_8217273 : CollatzResearch.WordTrace tailWord_8217273 prefixEnd_8217273 4219410718213133615296955 := by
  unfold tailWord_8217273
  simp only [CollatzResearch.WordTrace]
  refine ⟨299708568359230794343248473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199805712239487196228832315 299708568359230794343248473)
  ·
    refine ⟨224781426269423095757436355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299708568359230794343248473 224781426269423095757436355)
    ·
      refine ⟨337172139404134643636154533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224781426269423095757436355 337172139404134643636154533)
      ·
        refine ⟨63219776138275245681778975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337172139404134643636154533 63219776138275245681778975)
        ·
          refine ⟨94829664207412868522668463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63219776138275245681778975 94829664207412868522668463)
          ·
            refine ⟨142244496311119302784002695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94829664207412868522668463 142244496311119302784002695)
            ·
              refine ⟨213366744466678954176004043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142244496311119302784002695 213366744466678954176004043)
              ·
                refine ⟨320050116700018431264006065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213366744466678954176004043 320050116700018431264006065)
                ·
                  refine ⟨240037587525013823448004549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320050116700018431264006065 240037587525013823448004549)
                  ·
                    refine ⟨45007047660940091896500853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240037587525013823448004549 45007047660940091896500853)
                    ·
                      refine ⟨4219410718213133615296955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45007047660940091896500853 4219410718213133615296955)
                      ·
                        rfl

theorem cell23_8217273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_8217273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217273 prefixEnd_8217273 := by exact prefixLift 8217273
  have htrace : WordTrace (prefixWord ++ tailWord_8217273) baseStart_8217273 baseEnd_8217273 := by
    simpa [prefixWord, tailWord_8217273, baseEnd_8217273] using wordTrace_append hprefix tailTrace_8217273
  have hstable : (prefixWord ++ tailWord_8217273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217273).length < 2 ^ (prefixWord ++ tailWord_8217273).sum := by decide
  have hdescent : baseEnd_8217273 < baseStart_8217273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217294 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_8217294 : Nat := 118140960795 + 8217294 * 2 ^ 59
def prefixEnd_8217294 : Nat := 4983230072969 + 3 ^ 40 * 8217294 * 2
def baseEnd_8217294 : Nat := 4219421501306878033134359

theorem tailTrace_8217294 : CollatzResearch.WordTrace tailWord_8217294 prefixEnd_8217294 4219421501306878033134359 := by
  unfold tailWord_8217294
  simp only [CollatzResearch.WordTrace]
  refine ⟨37463666786519339366220367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199806222861436476619841957 37463666786519339366220367)
  ·
    refine ⟨56195500179779009049330551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37463666786519339366220367 56195500179779009049330551)
    ·
      refine ⟨84293250269668513573995827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56195500179779009049330551 84293250269668513573995827)
      ·
        refine ⟨126439875404502770360993741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84293250269668513573995827 126439875404502770360993741)
        ·
          refine ⟨47414953276688538885372653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126439875404502770360993741 47414953276688538885372653)
          ·
            refine ⟨17780607478758202082014745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47414953276688538885372653 17780607478758202082014745)
            ·
              refine ⟨13335455609068651561511059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17780607478758202082014745 13335455609068651561511059)
              ·
                refine ⟨20003183413602977342266589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13335455609068651561511059 20003183413602977342266589)
                ·
                  refine ⟨7501193780101116503349971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20003183413602977342266589 7501193780101116503349971)
                  ·
                    refine ⟨11251790670151674755024957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501193780101116503349971 11251790670151674755024957)
                    ·
                      refine ⟨4219421501306878033134359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11251790670151674755024957 4219421501306878033134359)
                      ·
                        rfl

theorem cell23_8217294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_8217294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217294 prefixEnd_8217294 := by exact prefixLift 8217294
  have htrace : WordTrace (prefixWord ++ tailWord_8217294) baseStart_8217294 baseEnd_8217294 := by
    simpa [prefixWord, tailWord_8217294, baseEnd_8217294] using wordTrace_append hprefix tailTrace_8217294
  have hstable : (prefixWord ++ tailWord_8217294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217294).length < 2 ^ (prefixWord ++ tailWord_8217294).sum := by decide
  have hdescent : baseEnd_8217294 < baseStart_8217294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217317 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_8217317 : Nat := 118140960795 + 8217317 * 2 ^ 59
def prefixEnd_8217317 : Nat := 4983230072969 + 3 ^ 40 * 8217317 * 2
def baseEnd_8217317 : Nat := 4219433311361931443146753

theorem tailTrace_8217317 : CollatzResearch.WordTrace tailWord_8217317 prefixEnd_8217317 4219433311361931443146753 := by
  unfold tailWord_8217317
  simp only [CollatzResearch.WordTrace]
  refine ⟨299710173171071389857850205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199806782114047593238566803 299710173171071389857850205)
  ·
    refine ⟨112391314939151771196693827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299710173171071389857850205 112391314939151771196693827)
    ·
      refine ⟨168586972408727656795040741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112391314939151771196693827 168586972408727656795040741)
      ·
        refine ⟨31610057326636435649070139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168586972408727656795040741 31610057326636435649070139)
        ·
          refine ⟨47415085989954653473605209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31610057326636435649070139 47415085989954653473605209)
          ·
            refine ⟨35561314492465990105203907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47415085989954653473605209 35561314492465990105203907)
            ·
              refine ⟨53341971738698985157805861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35561314492465990105203907 53341971738698985157805861)
              ·
                refine ⟨10001619701006059717088599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53341971738698985157805861 10001619701006059717088599)
                ·
                  refine ⟨15002429551509089575632899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10001619701006059717088599 15002429551509089575632899)
                  ·
                    refine ⟨22503644327263634363449349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15002429551509089575632899 22503644327263634363449349)
                    ·
                      refine ⟨4219433311361931443146753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22503644327263634363449349 4219433311361931443146753)
                      ·
                        rfl

theorem cell23_8217317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_8217317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217317 prefixEnd_8217317 := by exact prefixLift 8217317
  have htrace : WordTrace (prefixWord ++ tailWord_8217317) baseStart_8217317 baseEnd_8217317 := by
    simpa [prefixWord, tailWord_8217317, baseEnd_8217317] using wordTrace_append hprefix tailTrace_8217317
  have hstable : (prefixWord ++ tailWord_8217317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217317).length < 2 ^ (prefixWord ++ tailWord_8217317).sum := by decide
  have hdescent : baseEnd_8217317 < baseStart_8217317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217340 : List Nat := [2, 2, 2, 1, 3, 4, 9]
def baseStart_8217340 : Nat := 118140960795 + 8217340 * 2 ^ 59
def prefixEnd_8217340 : Nat := 4983230072969 + 3 ^ 40 * 8217340 * 2
def baseEnd_8217340 : Nat := 52091915079222035224187

theorem tailTrace_8217340 : CollatzResearch.WordTrace tailWord_8217340 prefixEnd_8217340 52091915079222035224187 := by
  unfold tailWord_8217340
  simp only [CollatzResearch.WordTrace]
  refine ⟨149855506024994032392968737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199807341366658709857291649 149855506024994032392968737)
  ·
    refine ⟨112391629518745524294726553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149855506024994032392968737 112391629518745524294726553)
    ·
      refine ⟨84293722139059143221044915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112391629518745524294726553 84293722139059143221044915)
      ·
        refine ⟨126440583208588714831567373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84293722139059143221044915 126440583208588714831567373)
        ·
          refine ⟨47415218703220768061837765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126440583208588714831567373 47415218703220768061837765)
          ·
            refine ⟨8890353506853894011594581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47415218703220768061837765 8890353506853894011594581)
            ·
              refine ⟨52091915079222035224187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8890353506853894011594581 52091915079222035224187)
              ·
                rfl

theorem cell23_8217340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 9].length) (baseStart_8217340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217340 prefixEnd_8217340 := by exact prefixLift 8217340
  have htrace : WordTrace (prefixWord ++ tailWord_8217340) baseStart_8217340 baseEnd_8217340 := by
    simpa [prefixWord, tailWord_8217340, baseEnd_8217340] using wordTrace_append hprefix tailTrace_8217340
  have hstable : (prefixWord ++ tailWord_8217340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217340).length < 2 ^ (prefixWord ++ tailWord_8217340).sum := by decide
  have hdescent : baseEnd_8217340 < baseStart_8217340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217351 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_8217351 : Nat := 118140960795 + 8217351 * 2 ^ 59
def prefixEnd_8217351 : Nat := 4983230072969 + 3 ^ 40 * 8217351 * 2
def baseEnd_8217351 : Nat := 4219450769704184310121597

theorem tailTrace_8217351 : CollatzResearch.WordTrace tailWord_8217351 prefixEnd_8217351 4219450769704184310121597 := by
  unfold tailWord_8217351
  simp only [CollatzResearch.WordTrace]
  refine ⟨299711413252948213664587907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199807608835298809109725271 299711413252948213664587907)
  ·
    refine ⟨449567119879422320496881861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299711413252948213664587907 449567119879422320496881861)
    ·
      refine ⟨84293834977391685093165349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449567119879422320496881861 84293834977391685093165349)
      ·
        refine ⟨15805094058260940954968503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84293834977391685093165349 15805094058260940954968503)
        ·
          refine ⟨23707641087391411432452755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15805094058260940954968503 23707641087391411432452755)
          ·
            refine ⟨35561461631087117148679133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23707641087391411432452755 35561461631087117148679133)
            ·
              refine ⟨13335548111657668930754675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35561461631087117148679133 13335548111657668930754675)
              ·
                refine ⟨20003322167486503396132013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13335548111657668930754675 20003322167486503396132013)
                ·
                  refine ⟨7501245812807438773549505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20003322167486503396132013 7501245812807438773549505)
                  ·
                    refine ⟨5625934359605579080162129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7501245812807438773549505 5625934359605579080162129)
                    ·
                      refine ⟨4219450769704184310121597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625934359605579080162129 4219450769704184310121597)
                      ·
                        rfl

theorem cell23_8217351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_8217351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217351 prefixEnd_8217351 := by exact prefixLift 8217351
  have htrace : WordTrace (prefixWord ++ tailWord_8217351) baseStart_8217351 baseEnd_8217351 := by
    simpa [prefixWord, tailWord_8217351, baseEnd_8217351] using wordTrace_append hprefix tailTrace_8217351
  have hstable : (prefixWord ++ tailWord_8217351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217351).length < 2 ^ (prefixWord ++ tailWord_8217351).sum := by decide
  have hdescent : baseEnd_8217351 < baseStart_8217351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217400 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_8217400 : Nat := 118140960795 + 8217400 * 2 ^ 59
def prefixEnd_8217400 : Nat := 4983230072969 + 3 ^ 40 * 8217400 * 2
def baseEnd_8217400 : Nat := 1406491976752084872802957

theorem tailTrace_8217400 : CollatzResearch.WordTrace tailWord_8217400 prefixEnd_8217400 1406491976752084872802957 := by
  unfold tailWord_8217400
  simp only [CollatzResearch.WordTrace]
  refine ⟨149856600214885347516560827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199808800286513796688747769 149856600214885347516560827)
  ·
    refine ⟨224784900322328021274841241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149856600214885347516560827 224784900322328021274841241)
    ·
      refine ⟨168588675241746015956130931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224784900322328021274841241 168588675241746015956130931)
      ·
        refine ⟨252883012862619023934196397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168588675241746015956130931 252883012862619023934196397)
        ·
          refine ⟨94831129823482133975323649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252883012862619023934196397 94831129823482133975323649)
          ·
            refine ⟨71123347367611600481492737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94831129823482133975323649 71123347367611600481492737)
            ·
              refine ⟨53342510525708700361119553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71123347367611600481492737 53342510525708700361119553)
              ·
                refine ⟨40006882894281525270839665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53342510525708700361119553 40006882894281525270839665)
                ·
                  refine ⟨30005162170711143953129749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40006882894281525270839665 30005162170711143953129749)
                  ·
                    refine ⟨1406491976752084872802957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30005162170711143953129749 1406491976752084872802957)
                    ·
                      rfl

theorem cell23_8217400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_8217400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217400 prefixEnd_8217400 := by exact prefixLift 8217400
  have htrace : WordTrace (prefixWord ++ tailWord_8217400) baseStart_8217400 baseEnd_8217400 := by
    simpa [prefixWord, tailWord_8217400, baseEnd_8217400] using wordTrace_append hprefix tailTrace_8217400
  have hstable : (prefixWord ++ tailWord_8217400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217400).length < 2 ^ (prefixWord ++ tailWord_8217400).sum := by decide
  have hdescent : baseEnd_8217400 < baseStart_8217400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217402 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2]
def baseStart_8217402 : Nat := 118140960795 + 8217402 * 2 ^ 59
def prefixEnd_8217402 : Nat := 4983230072969 + 3 ^ 40 * 8217402 * 2
def baseEnd_8217402 : Nat := 4219476957217563610583863

theorem tailTrace_8217402 : CollatzResearch.WordTrace tailWord_8217402 prefixEnd_8217402 4219476957217563610583863 := by
  unfold tailWord_8217402
  simp only [CollatzResearch.WordTrace]
  refine ⟨74928318343940862343673615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199808848917175632916462973 74928318343940862343673615)
  ·
    refine ⟨112392477515911293515510423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74928318343940862343673615 112392477515911293515510423)
    ·
      refine ⟨168588716273866940273265635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112392477515911293515510423 168588716273866940273265635)
      ·
        refine ⟨252883074410800410409898453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168588716273866940273265635 252883074410800410409898453)
        ·
          refine ⟨5926947056503134618981995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 252883074410800410409898453 5926947056503134618981995)
          ·
            refine ⟨8890420584754701928472993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926947056503134618981995 8890420584754701928472993)
            ·
              refine ⟨6667815438566026446354745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890420584754701928472993 6667815438566026446354745)
              ·
                refine ⟨5000861578924519834766059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6667815438566026446354745 5000861578924519834766059)
                ·
                  refine ⟨7501292368386779752149089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000861578924519834766059 7501292368386779752149089)
                  ·
                    refine ⟨5625969276290084814111817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7501292368386779752149089 5625969276290084814111817)
                    ·
                      refine ⟨4219476957217563610583863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5625969276290084814111817 4219476957217563610583863)
                      ·
                        rfl

theorem cell23_8217402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_8217402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217402 prefixEnd_8217402 := by exact prefixLift 8217402
  have htrace : WordTrace (prefixWord ++ tailWord_8217402) baseStart_8217402 baseEnd_8217402 := by
    simpa [prefixWord, tailWord_8217402, baseEnd_8217402] using wordTrace_append hprefix tailTrace_8217402
  have hstable : (prefixWord ++ tailWord_8217402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217402).length < 2 ^ (prefixWord ++ tailWord_8217402).sum := by decide
  have hdescent : baseEnd_8217402 < baseStart_8217402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217457 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_8217457 : Nat := 118140960795 + 8217457 * 2 ^ 59
def prefixEnd_8217457 : Nat := 4983230072969 + 3 ^ 40 * 8217457 * 2
def baseEnd_8217457 : Nat := 4219505198653560895396109

theorem tailTrace_8217457 : CollatzResearch.WordTrace tailWord_8217457 prefixEnd_8217457 4219505198653560895396109 := by
  unfold tailWord_8217457
  simp only [CollatzResearch.WordTrace]
  refine ⟨299715279390564193767946625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199810186260376129178631083 299715279390564193767946625)
  ·
    refine ⟨224786459542923145325959969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299715279390564193767946625 224786459542923145325959969)
    ·
      refine ⟨168589844657192358994469977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224786459542923145325959969 168589844657192358994469977)
      ·
        refine ⟨126442383492894269245852483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168589844657192358994469977 126442383492894269245852483)
        ·
          refine ⟨189663575239341403868778725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126442383492894269245852483 189663575239341403868778725)
          ·
            refine ⟨35561920357376513225396011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189663575239341403868778725 35561920357376513225396011)
            ·
              refine ⟨53342880536064769838094017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35561920357376513225396011 53342880536064769838094017)
              ·
                refine ⟨40007160402048577378570513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53342880536064769838094017 40007160402048577378570513)
                ·
                  refine ⟨30005370301536433033927885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40007160402048577378570513 30005370301536433033927885)
                  ·
                    refine ⟨11252013863076162387722957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30005370301536433033927885 11252013863076162387722957)
                    ·
                      refine ⟨4219505198653560895396109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252013863076162387722957 4219505198653560895396109)
                      ·
                        rfl

theorem cell23_8217457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_8217457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217457 prefixEnd_8217457 := by exact prefixLift 8217457
  have htrace : WordTrace (prefixWord ++ tailWord_8217457) baseStart_8217457 baseEnd_8217457 := by
    simpa [prefixWord, tailWord_8217457, baseEnd_8217457] using wordTrace_append hprefix tailTrace_8217457
  have hstable : (prefixWord ++ tailWord_8217457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217457).length < 2 ^ (prefixWord ++ tailWord_8217457).sum := by decide
  have hdescent : baseEnd_8217457 < baseStart_8217457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217467 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 7, 2]
def baseStart_8217467 : Nat := 118140960795 + 8217467 * 2 ^ 59
def prefixEnd_8217467 : Nat := 4983230072969 + 3 ^ 40 * 8217467 * 2
def baseEnd_8217467 : Nat := 4219510333460105856271063

theorem tailTrace_8217467 : CollatzResearch.WordTrace tailWord_8217467 prefixEnd_8217467 4219510333460105856271063 := by
  unfold tailWord_8217467
  simp only [CollatzResearch.WordTrace]
  refine ⟨299715644120527965475810655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199810429413685310317207103 299715644120527965475810655)
  ·
    refine ⟨449573466180791948213715983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299715644120527965475810655 449573466180791948213715983)
    ·
      refine ⟨674360199271187922320573975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449573466180791948213715983 674360199271187922320573975)
      ·
        refine ⟨1011540298906781883480860963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674360199271187922320573975 1011540298906781883480860963)
        ·
          refine ⟨1517310448360172825221291445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011540298906781883480860963 1517310448360172825221291445)
          ·
            refine ⟨142247854533766202364496073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1517310448360172825221291445 142247854533766202364496073)
            ·
              refine ⟨106685890900324651773372055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142247854533766202364496073 106685890900324651773372055)
              ·
                refine ⟨160028836350486977660058083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106685890900324651773372055 160028836350486977660058083)
                ·
                  refine ⟨240043254525730466490087125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160028836350486977660058083 240043254525730466490087125)
                  ·
                    refine ⟨5626013777946807808361417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240043254525730466490087125 5626013777946807808361417)
                    ·
                      refine ⟨4219510333460105856271063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626013777946807808361417 4219510333460105856271063)
                      ·
                        rfl

theorem cell23_8217467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7, 2].length) (baseStart_8217467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217467 prefixEnd_8217467 := by exact prefixLift 8217467
  have htrace : WordTrace (prefixWord ++ tailWord_8217467) baseStart_8217467 baseEnd_8217467 := by
    simpa [prefixWord, tailWord_8217467, baseEnd_8217467] using wordTrace_append hprefix tailTrace_8217467
  have hstable : (prefixWord ++ tailWord_8217467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217467).length < 2 ^ (prefixWord ++ tailWord_8217467).sum := by decide
  have hdescent : baseEnd_8217467 < baseStart_8217467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217497 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_8217497 : Nat := 118140960795 + 8217497 * 2 ^ 59
def prefixEnd_8217497 : Nat := 4983230072969 + 3 ^ 40 * 8217497 * 2
def baseEnd_8217497 : Nat := 4219525737879740738895925

theorem tailTrace_8217497 : CollatzResearch.WordTrace tailWord_8217497 prefixEnd_8217497 4219525737879740738895925 := by
  unfold tailWord_8217497
  simp only [CollatzResearch.WordTrace]
  refine ⟨299716738310419280599402745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199811158873612853732935163 299716738310419280599402745)
  ·
    refine ⟨224787553732814460449552059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299716738310419280599402745 224787553732814460449552059)
    ·
      refine ⟨337181330599221690674328089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224787553732814460449552059 337181330599221690674328089)
      ·
        refine ⟨252885997949416268005746067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337181330599221690674328089 252885997949416268005746067)
        ·
          refine ⟨379328996924124402008619101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252885997949416268005746067 379328996924124402008619101)
          ·
            refine ⟨142248373846546650753232163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379328996924124402008619101 142248373846546650753232163)
            ·
              refine ⟨213372560769819976129848245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142248373846546650753232163 213372560769819976129848245)
              ·
                refine ⟨20003677572170622762173273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213372560769819976129848245 20003677572170622762173273)
                ·
                  refine ⟨15002758179127967071629955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20003677572170622762173273 15002758179127967071629955)
                  ·
                    refine ⟨22504137268691950607444933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15002758179127967071629955 22504137268691950607444933)
                    ·
                      refine ⟨4219525737879740738895925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22504137268691950607444933 4219525737879740738895925)
                      ·
                        rfl

theorem cell23_8217497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_8217497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217497 prefixEnd_8217497 := by exact prefixLift 8217497
  have htrace : WordTrace (prefixWord ++ tailWord_8217497) baseStart_8217497 baseEnd_8217497 := by
    simpa [prefixWord, tailWord_8217497, baseEnd_8217497] using wordTrace_append hprefix tailTrace_8217497
  have hstable : (prefixWord ++ tailWord_8217497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217497).length < 2 ^ (prefixWord ++ tailWord_8217497).sum := by decide
  have hdescent : baseEnd_8217497 < baseStart_8217497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217498 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_8217498 : Nat := 118140960795 + 8217498 * 2 ^ 59
def prefixEnd_8217498 : Nat := 4983230072969 + 3 ^ 40 * 8217498 * 2
def baseEnd_8217498 : Nat := 468836250151155026109269

theorem tailTrace_8217498 : CollatzResearch.WordTrace tailWord_8217498 prefixEnd_8217498 468836250151155026109269 := by
  unfold tailWord_8217498
  simp only [CollatzResearch.WordTrace]
  refine ⟨74929193695853914442547287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199811183188943771846792765 74929193695853914442547287)
  ·
    refine ⟨112393790543780871663820931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74929193695853914442547287 112393790543780871663820931)
    ·
      refine ⟨168590685815671307495731397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112393790543780871663820931 168590685815671307495731397)
      ·
        refine ⟨31610753590438370155449637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168590685815671307495731397 31610753590438370155449637)
        ·
          refine ⟨5927016298207194404146807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31610753590438370155449637 5927016298207194404146807)
          ·
            refine ⟨8890524447310791606220211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927016298207194404146807 8890524447310791606220211)
            ·
              refine ⟨13335786670966187409330317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890524447310791606220211 13335786670966187409330317)
              ·
                refine ⟨5000920001612320278498869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13335786670966187409330317 5000920001612320278498869)
                ·
                  refine ⟨468836250151155026109269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5000920001612320278498869 468836250151155026109269)
                  ·
                    rfl

theorem cell23_8217498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_8217498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217498 prefixEnd_8217498 := by exact prefixLift 8217498
  have htrace : WordTrace (prefixWord ++ tailWord_8217498) baseStart_8217498 baseEnd_8217498 := by
    simpa [prefixWord, tailWord_8217498, baseEnd_8217498] using wordTrace_append hprefix tailTrace_8217498
  have hstable : (prefixWord ++ tailWord_8217498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217498).length < 2 ^ (prefixWord ++ tailWord_8217498).sum := by decide
  have hdescent : baseEnd_8217498 < baseStart_8217498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217507 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 5, 4]
def baseStart_8217507 : Nat := 118140960795 + 8217507 * 2 ^ 59
def prefixEnd_8217507 : Nat := 4983230072969 + 3 ^ 40 * 8217507 * 2
def baseEnd_8217507 : Nat := 1406510290895428566590293

theorem tailTrace_8217507 : CollatzResearch.WordTrace tailWord_8217507 prefixEnd_8217507 1406510290895428566590293 := by
  unfold tailWord_8217507
  simp only [CollatzResearch.WordTrace]
  refine ⟨299717103040383052307266775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199811402026922034871511183 299717103040383052307266775)
  ·
    refine ⟨449575654560574578460900163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299717103040383052307266775 449575654560574578460900163)
    ·
      refine ⟨674363481840861867691350245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449575654560574578460900163 674363481840861867691350245)
      ·
        refine ⟨126443152845161600192128171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 674363481840861867691350245 126443152845161600192128171)
        ·
          refine ⟨189664729267742400288192257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126443152845161600192128171 189664729267742400288192257)
          ·
            refine ⟨142248546950806800216144193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189664729267742400288192257 142248546950806800216144193)
            ·
              refine ⟨106686410213105100162108145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142248546950806800216144193 106686410213105100162108145)
              ·
                refine ⟨80014807659828825121581109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106686410213105100162108145 80014807659828825121581109)
                ·
                  refine ⟨7501388218108952355148229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80014807659828825121581109 7501388218108952355148229)
                  ·
                    refine ⟨1406510290895428566590293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7501388218108952355148229 1406510290895428566590293)
                    ·
                      rfl

theorem cell23_8217507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 4].length) (baseStart_8217507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217507 prefixEnd_8217507 := by exact prefixLift 8217507
  have htrace : WordTrace (prefixWord ++ tailWord_8217507) baseStart_8217507 baseEnd_8217507 := by
    simpa [prefixWord, tailWord_8217507, baseEnd_8217507] using wordTrace_append hprefix tailTrace_8217507
  have hstable : (prefixWord ++ tailWord_8217507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217507).length < 2 ^ (prefixWord ++ tailWord_8217507).sum := by decide
  have hdescent : baseEnd_8217507 < baseStart_8217507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217526 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_8217526 : Nat := 118140960795 + 8217526 * 2 ^ 59
def prefixEnd_8217526 : Nat := 4983230072969 + 3 ^ 40 * 8217526 * 2
def baseEnd_8217526 : Nat := 4219540628818721125433293

theorem tailTrace_8217526 : CollatzResearch.WordTrace tailWord_8217526 prefixEnd_8217526 4219540628818721125433293 := by
  unfold tailWord_8217526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732362251707138659513027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199811864018209479034805621 18732362251707138659513027)
  ·
    refine ⟨28098543377560707989269541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18732362251707138659513027 28098543377560707989269541)
    ·
      refine ⟨5268476883292632747988039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28098543377560707989269541 5268476883292632747988039)
      ·
        refine ⟨7902715324938949121982059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268476883292632747988039 7902715324938949121982059)
        ·
          refine ⟨11854072987408423682973089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902715324938949121982059 11854072987408423682973089)
          ·
            refine ⟨8890554740556317762229817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11854072987408423682973089 8890554740556317762229817)
            ·
              refine ⟨6667916055417238321672363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890554740556317762229817 6667916055417238321672363)
              ·
                refine ⟨10001874083125857482508545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667916055417238321672363 10001874083125857482508545)
                ·
                  refine ⟨7501405562344393111881409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10001874083125857482508545 7501405562344393111881409)
                  ·
                    refine ⟨5626054171758294833911057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7501405562344393111881409 5626054171758294833911057)
                    ·
                      refine ⟨4219540628818721125433293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626054171758294833911057 4219540628818721125433293)
                      ·
                        rfl

theorem cell23_8217526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_8217526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217526 prefixEnd_8217526 := by exact prefixLift 8217526
  have htrace : WordTrace (prefixWord ++ tailWord_8217526) baseStart_8217526 baseEnd_8217526 := by
    simpa [prefixWord, tailWord_8217526, baseEnd_8217526] using wordTrace_append hprefix tailTrace_8217526
  have hstable : (prefixWord ++ tailWord_8217526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217526).length < 2 ^ (prefixWord ++ tailWord_8217526).sum := by decide
  have hdescent : baseEnd_8217526 < baseStart_8217526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217534 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_8217534 : Nat := 118140960795 + 8217534 * 2 ^ 59
def prefixEnd_8217534 : Nat := 4983230072969 + 3 ^ 40 * 8217534 * 2
def baseEnd_8217534 : Nat := 4219544736663957094133255

theorem tailTrace_8217534 : CollatzResearch.WordTrace tailWord_8217534 prefixEnd_8217534 4219544736663957094133255 := by
  unfold tailWord_8217534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37464760976410654489812457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199812058540856823945666437 37464760976410654489812457)
  ·
    refine ⟨28098570732307990867359343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37464760976410654489812457 28098570732307990867359343)
    ·
      refine ⟨42147856098461986301039015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28098570732307990867359343 42147856098461986301039015)
      ·
        refine ⟨63221784147692979451558523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42147856098461986301039015 63221784147692979451558523)
        ·
          refine ⟨94832676221539469177337785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63221784147692979451558523 94832676221539469177337785)
          ·
            refine ⟨71124507166154601883003339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94832676221539469177337785 71124507166154601883003339)
            ·
              refine ⟨106686760749231902824505009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71124507166154601883003339 106686760749231902824505009)
              ·
                refine ⟨80015070561923927118378757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106686760749231902824505009 80015070561923927118378757)
                ·
                  refine ⟨15002825730360736334696017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80015070561923927118378757 15002825730360736334696017)
                  ·
                    refine ⟨11252119297770552251022013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15002825730360736334696017 11252119297770552251022013)
                    ·
                      refine ⟨4219544736663957094133255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252119297770552251022013 4219544736663957094133255)
                      ·
                        rfl

theorem cell23_8217534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_8217534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217534 prefixEnd_8217534 := by exact prefixLift 8217534
  have htrace : WordTrace (prefixWord ++ tailWord_8217534) baseStart_8217534 baseEnd_8217534 := by
    simpa [prefixWord, tailWord_8217534, baseEnd_8217534] using wordTrace_append hprefix tailTrace_8217534
  have hstable : (prefixWord ++ tailWord_8217534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217534).length < 2 ^ (prefixWord ++ tailWord_8217534).sum := by decide
  have hdescent : baseEnd_8217534 < baseStart_8217534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217575 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 1, 4]
def baseStart_8217575 : Nat := 118140960795 + 8217575 * 2 ^ 59
def prefixEnd_8217575 : Nat := 4983230072969 + 3 ^ 40 * 8217575 * 2
def baseEnd_8217575 : Nat := 1406521929790263811240189

theorem tailTrace_8217575 : CollatzResearch.WordTrace tailWord_8217575 prefixEnd_8217575 1406521929790263811240189 := by
  unfold tailWord_8217575
  simp only [CollatzResearch.WordTrace]
  refine ⟨299719583204136699920742179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199813055469424466613828119 299719583204136699920742179)
  ·
    refine ⟨449579374806205049881113269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299719583204136699920742179 449579374806205049881113269)
    ·
      refine ⟨42148066388081723426354369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449579374806205049881113269 42148066388081723426354369)
      ·
        refine ⟨31611049791061292569765777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42148066388081723426354369 31611049791061292569765777)
        ·
          refine ⟨23708287343295969427324333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31611049791061292569765777 23708287343295969427324333)
          ·
            refine ⟨8890607753735988535246625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23708287343295969427324333 8890607753735988535246625)
            ·
              refine ⟨6667955815301991401434969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890607753735988535246625 6667955815301991401434969)
              ·
                refine ⟨5000966861476493551076227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6667955815301991401434969 5000966861476493551076227)
                ·
                  refine ⟨7501450292214740326614341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000966861476493551076227 7501450292214740326614341)
                  ·
                    refine ⟨1406521929790263811240189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7501450292214740326614341 1406521929790263811240189)
                    ·
                      rfl

theorem cell23_8217575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_8217575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217575 prefixEnd_8217575 := by exact prefixLift 8217575
  have htrace : WordTrace (prefixWord ++ tailWord_8217575) baseStart_8217575 baseEnd_8217575 := by
    simpa [prefixWord, tailWord_8217575, baseEnd_8217575] using wordTrace_append hprefix tailTrace_8217575
  have hstable : (prefixWord ++ tailWord_8217575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217575).length < 2 ^ (prefixWord ++ tailWord_8217575).sum := by decide
  have hdescent : baseEnd_8217575 < baseStart_8217575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217602 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_8217602 : Nat := 118140960795 + 8217602 * 2 ^ 59
def prefixEnd_8217602 : Nat := 4983230072969 + 3 ^ 40 * 8217602 * 2
def baseEnd_8217602 : Nat := 4219579653348462828082943

theorem tailTrace_8217602 : CollatzResearch.WordTrace tailWord_8217602 prefixEnd_8217602 4219579653348462828082943 := by
  unfold tailWord_8217602
  simp only [CollatzResearch.WordTrace]
  refine ⟨74930141993759720882993765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199813711983359255687983373 74930141993759720882993765)
  ·
    refine ⟨14049401623829947665561331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74930141993759720882993765 14049401623829947665561331)
    ·
      refine ⟨21074102435744921498341997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049401623829947665561331 21074102435744921498341997)
      ·
        refine ⟨7902788413404345561878249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21074102435744921498341997 7902788413404345561878249)
        ·
          refine ⟨5927091310053259171408687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7902788413404345561878249 5927091310053259171408687)
          ·
            refine ⟨8890636965079888757113031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927091310053259171408687 8890636965079888757113031)
            ·
              refine ⟨13335955447619833135669547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890636965079888757113031 13335955447619833135669547)
              ·
                refine ⟨20003933171429749703504321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13335955447619833135669547 20003933171429749703504321)
                ·
                  refine ⟨15002949878572312277628241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20003933171429749703504321 15002949878572312277628241)
                  ·
                    refine ⟨11252212408929234208221181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15002949878572312277628241 11252212408929234208221181)
                    ·
                      refine ⟨4219579653348462828082943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252212408929234208221181 4219579653348462828082943)
                      ·
                        rfl

theorem cell23_8217602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_8217602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217602 prefixEnd_8217602 := by exact prefixLift 8217602
  have htrace : WordTrace (prefixWord ++ tailWord_8217602) baseStart_8217602 baseEnd_8217602 := by
    simpa [prefixWord, tailWord_8217602, baseEnd_8217602] using wordTrace_append hprefix tailTrace_8217602
  have hstable : (prefixWord ++ tailWord_8217602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217602).length < 2 ^ (prefixWord ++ tailWord_8217602).sum := by decide
  have hdescent : baseEnd_8217602 < baseStart_8217602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217608 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_8217608 : Nat := 118140960795 + 8217608 * 2 ^ 59
def prefixEnd_8217608 : Nat := 4983230072969 + 3 ^ 40 * 8217608 * 2
def baseEnd_8217608 : Nat := 4219582734232389804607915

theorem tailTrace_8217608 : CollatzResearch.WordTrace tailWord_8217608 prefixEnd_8217608 4219582734232389804607915 := by
  unfold tailWord_8217608
  simp only [CollatzResearch.WordTrace]
  refine ⟨149860393406508573278346739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199813857875344764371128985 149860393406508573278346739)
  ·
    refine ⟨224790590109762859917520109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149860393406508573278346739 224790590109762859917520109)
    ·
      refine ⟨84296471291161072469070041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224790590109762859917520109 84296471291161072469070041)
      ·
        refine ⟨63222353468370804351802531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84296471291161072469070041 63222353468370804351802531)
        ·
          refine ⟨94833530202556206527703797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63222353468370804351802531 94833530202556206527703797)
          ·
            refine ⟨8890643456489644361972231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94833530202556206527703797 8890643456489644361972231)
            ·
              refine ⟨13335965184734466542958347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890643456489644361972231 13335965184734466542958347)
              ·
                refine ⟨20003947777101699814437521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13335965184734466542958347 20003947777101699814437521)
                ·
                  refine ⟨15002960832826274860828141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20003947777101699814437521 15002960832826274860828141)
                  ·
                    refine ⟨5626110312309853072810553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15002960832826274860828141 5626110312309853072810553)
                    ·
                      refine ⟨4219582734232389804607915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626110312309853072810553 4219582734232389804607915)
                      ·
                        rfl

theorem cell23_8217608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_8217608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217608 prefixEnd_8217608 := by exact prefixLift 8217608
  have htrace : WordTrace (prefixWord ++ tailWord_8217608) baseStart_8217608 baseEnd_8217608 := by
    simpa [prefixWord, tailWord_8217608, baseEnd_8217608] using wordTrace_append hprefix tailTrace_8217608
  have hstable : (prefixWord ++ tailWord_8217608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217608).length < 2 ^ (prefixWord ++ tailWord_8217608).sum := by decide
  have hdescent : baseEnd_8217608 < baseStart_8217608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217614 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_8217614 : Nat := 118140960795 + 8217614 * 2 ^ 59
def prefixEnd_8217614 : Nat := 4983230072969 + 3 ^ 40 * 8217614 * 2
def baseEnd_8217614 : Nat := 1406528605038772260377629

theorem tailTrace_8217614 : CollatzResearch.WordTrace tailWord_8217614 prefixEnd_8217614 1406528605038772260377629 := by
  unfold tailWord_8217614
  simp only [CollatzResearch.WordTrace]
  refine ⟨37465125706374426197676487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199814003767330273054274597 37465125706374426197676487)
  ·
    refine ⟨56197688559561639296514731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37465125706374426197676487 56197688559561639296514731)
    ·
      refine ⟨84296532839342458944772097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56197688559561639296514731 84296532839342458944772097)
      ·
        refine ⟨63222399629506844208579073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84296532839342458944772097 63222399629506844208579073)
        ·
          refine ⟨47416799722130133156434305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63222399629506844208579073 47416799722130133156434305)
          ·
            refine ⟨35562599791597599867325729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47416799722130133156434305 35562599791597599867325729)
            ·
              refine ⟨26671949843698199900494297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35562599791597599867325729 26671949843698199900494297)
              ·
                refine ⟨20003962382773649925370723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26671949843698199900494297 20003962382773649925370723)
                ·
                  refine ⟨30005943574160474888056085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20003962382773649925370723 30005943574160474888056085)
                  ·
                    refine ⟨1406528605038772260377629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30005943574160474888056085 1406528605038772260377629)
                    ·
                      rfl

theorem cell23_8217614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_8217614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217614 prefixEnd_8217614 := by exact prefixLift 8217614
  have htrace : WordTrace (prefixWord ++ tailWord_8217614) baseStart_8217614 baseEnd_8217614 := by
    simpa [prefixWord, tailWord_8217614, baseEnd_8217614] using wordTrace_append hprefix tailTrace_8217614
  have hstable : (prefixWord ++ tailWord_8217614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217614).length < 2 ^ (prefixWord ++ tailWord_8217614).sum := by decide
  have hdescent : baseEnd_8217614 < baseStart_8217614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217621 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_8217621 : Nat := 118140960795 + 8217621 * 2 ^ 59
def prefixEnd_8217621 : Nat := 4983230072969 + 3 ^ 40 * 8217621 * 2
def baseEnd_8217621 : Nat := 4219589409480898253745355

theorem tailTrace_8217621 : CollatzResearch.WordTrace tailWord_8217621 prefixEnd_8217621 4219589409480898253745355 := by
  unfold tailWord_8217621
  simp only [CollatzResearch.WordTrace]
  refine ⟨299721260961970049776916717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199814173974646699851277811 299721260961970049776916717)
  ·
    refine ⟨112395472860738768666343769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299721260961970049776916717 112395472860738768666343769)
    ·
      refine ⟨84296604645554076499757827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112395472860738768666343769 84296604645554076499757827)
      ·
        refine ⟨126444906968331114749636741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84296604645554076499757827 126444906968331114749636741)
        ·
          refine ⟨23708420056562084015556889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126444906968331114749636741 23708420056562084015556889)
          ·
            refine ⟨17781315042421563011667667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23708420056562084015556889 17781315042421563011667667)
            ·
              refine ⟨26671972563632344517501501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17781315042421563011667667 26671972563632344517501501)
              ·
                refine ⟨10001989711362129194063063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26671972563632344517501501 10001989711362129194063063)
                ·
                  refine ⟨15002984567043193791094595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10001989711362129194063063 15002984567043193791094595)
                  ·
                    refine ⟨22504476850564790686641893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15002984567043193791094595 22504476850564790686641893)
                    ·
                      refine ⟨4219589409480898253745355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22504476850564790686641893 4219589409480898253745355)
                      ·
                        rfl

theorem cell23_8217621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_8217621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217621 prefixEnd_8217621 := by exact prefixLift 8217621
  have htrace : WordTrace (prefixWord ++ tailWord_8217621) baseStart_8217621 baseEnd_8217621 := by
    simpa [prefixWord, tailWord_8217621, baseEnd_8217621] using wordTrace_append hprefix tailTrace_8217621
  have hstable : (prefixWord ++ tailWord_8217621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217621).length < 2 ^ (prefixWord ++ tailWord_8217621).sum := by decide
  have hdescent : baseEnd_8217621 < baseStart_8217621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217631 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 2, 4]
def baseStart_8217631 : Nat := 118140960795 + 8217631 * 2 ^ 59
def prefixEnd_8217631 : Nat := 4983230072969 + 3 ^ 40 * 8217631 * 2
def baseEnd_8217631 : Nat := 1406531514762481071540103

theorem tailTrace_8217631 : CollatzResearch.WordTrace tailWord_8217631 prefixEnd_8217631 1406531514762481071540103 := by
  unfold tailWord_8217631
  simp only [CollatzResearch.WordTrace]
  refine ⟨299721625691933821484780747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199814417127955880989853831 299721625691933821484780747)
  ·
    refine ⟨449582438537900732227171121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299721625691933821484780747 449582438537900732227171121)
    ·
      refine ⟨337186828903425549170378341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449582438537900732227171121 337186828903425549170378341)
      ·
        refine ⟨63222530419392290469445939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337186828903425549170378341 63222530419392290469445939)
        ·
          refine ⟨94833795629088435704168909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63222530419392290469445939 94833795629088435704168909)
          ·
            refine ⟨35562673360908163389063341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94833795629088435704168909 35562673360908163389063341)
            ·
              refine ⟨13336002510340561270898753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35562673360908163389063341 13336002510340561270898753)
              ·
                refine ⟨10002001882755420953174065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13336002510340561270898753 10002001882755420953174065)
                ·
                  refine ⟨7501501412066565714880549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10002001882755420953174065 7501501412066565714880549)
                  ·
                    refine ⟨1406531514762481071540103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7501501412066565714880549 1406531514762481071540103)
                    ·
                      rfl

theorem cell23_8217631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_8217631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217631 prefixEnd_8217631 := by exact prefixLift 8217631
  have htrace : WordTrace (prefixWord ++ tailWord_8217631) baseStart_8217631 baseEnd_8217631 := by
    simpa [prefixWord, tailWord_8217631, baseEnd_8217631] using wordTrace_append hprefix tailTrace_8217631
  have hstable : (prefixWord ++ tailWord_8217631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217631).length < 2 ^ (prefixWord ++ tailWord_8217631).sum := by decide
  have hdescent : baseEnd_8217631 < baseStart_8217631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217661 : List Nat := [1, 4, 1, 3, 1, 4, 2, 7]
def baseStart_8217661 : Nat := 118140960795 + 8217661 * 2 ^ 59
def prefixEnd_8217661 : Nat := 4983230072969 + 3 ^ 40 * 8217661 * 2
def baseEnd_8217661 : Nat := 156281849952114003601673

theorem tailTrace_8217661 : CollatzResearch.WordTrace tailWord_8217661 prefixEnd_8217661 156281849952114003601673 := by
  unfold tailWord_8217661
  simp only [CollatzResearch.WordTrace]
  refine ⟨299722719881825136608372837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199815146587883424405581891 299722719881825136608372837)
  ·
    refine ⟨56198009977842213114069907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299722719881825136608372837 56198009977842213114069907)
    ·
      refine ⟨84297014966763319671104861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56198009977842213114069907 84297014966763319671104861)
      ·
        refine ⟨31611380612536244876664323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84297014966763319671104861 31611380612536244876664323)
        ·
          refine ⟨47417070918804367314996485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31611380612536244876664323 47417070918804367314996485)
          ·
            refine ⟨8890700797275818871561841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47417070918804367314996485 8890700797275818871561841)
            ·
              refine ⟨6668025597956864153671381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890700797275818871561841 6668025597956864153671381)
              ·
                refine ⟨156281849952114003601673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6668025597956864153671381 156281849952114003601673)
                ·
                  rfl

theorem cell23_8217661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 7].length) (baseStart_8217661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217661 prefixEnd_8217661 := by exact prefixLift 8217661
  have htrace : WordTrace (prefixWord ++ tailWord_8217661) baseStart_8217661 baseEnd_8217661 := by
    simpa [prefixWord, tailWord_8217661, baseEnd_8217661] using wordTrace_append hprefix tailTrace_8217661
  have hstable : (prefixWord ++ tailWord_8217661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217661).length < 2 ^ (prefixWord ++ tailWord_8217661).sum := by decide
  have hdescent : baseEnd_8217661 < baseStart_8217661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217667 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_8217667 : Nat := 118140960795 + 8217667 * 2 ^ 59
def prefixEnd_8217667 : Nat := 4983230072969 + 3 ^ 40 * 8217667 * 2
def baseEnd_8217667 : Nat := 4219613029591005073770143

theorem tailTrace_8217667 : CollatzResearch.WordTrace tailWord_8217667 prefixEnd_8217667 4219613029591005073770143 := by
  unfold tailWord_8217667
  simp only [CollatzResearch.WordTrace]
  refine ⟨299722938719803399633091255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199815292479868933088727503 299722938719803399633091255)
  ·
    refine ⟨449584408079705099449636883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299722938719803399633091255 449584408079705099449636883)
    ·
      refine ⟨674376612119557649174455325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449584408079705099449636883 674376612119557649174455325)
      ·
        refine ⟨252891229544834118440420747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674376612119557649174455325 252891229544834118440420747)
        ·
          refine ⟨379336844317251177660631121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252891229544834118440420747 379336844317251177660631121)
          ·
            refine ⟨284502633237938383245473341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379336844317251177660631121 284502633237938383245473341)
            ·
              refine ⟨106688487464226893717052503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284502633237938383245473341 106688487464226893717052503)
              ·
                refine ⟨160032731196340340575578755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106688487464226893717052503 160032731196340340575578755)
                ·
                  refine ⟨240049096794510510863368133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160032731196340340575578755 240049096794510510863368133)
                  ·
                    refine ⟨45009205648970720786881525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240049096794510510863368133 45009205648970720786881525)
                    ·
                      refine ⟨4219613029591005073770143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45009205648970720786881525 4219613029591005073770143)
                      ·
                        rfl

theorem cell23_8217667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_8217667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217667 prefixEnd_8217667 := by exact prefixLift 8217667
  have htrace : WordTrace (prefixWord ++ tailWord_8217667) baseStart_8217667 baseEnd_8217667 := by
    simpa [prefixWord, tailWord_8217667, baseEnd_8217667] using wordTrace_append hprefix tailTrace_8217667
  have hstable : (prefixWord ++ tailWord_8217667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217667).length < 2 ^ (prefixWord ++ tailWord_8217667).sum := by decide
  have hdescent : baseEnd_8217667 < baseStart_8217667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217671 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_8217671 : Nat := 118140960795 + 8217671 * 2 ^ 59
def prefixEnd_8217671 : Nat := 4983230072969 + 3 ^ 40 * 8217671 * 2
def baseEnd_8217671 : Nat := 4219615083513623058120125

theorem tailTrace_8217671 : CollatzResearch.WordTrace tailWord_8217671 prefixEnd_8217671 4219615083513623058120125 := by
  unfold tailWord_8217671
  simp only [CollatzResearch.WordTrace]
  refine ⟨299723084611788908316236867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199815389741192605544157911 299723084611788908316236867)
  ·
    refine ⟨449584626917683362474355301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299723084611788908316236867 449584626917683362474355301)
    ·
      refine ⟨84297117547065630463941619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449584626917683362474355301 84297117547065630463941619)
      ·
        refine ⟨126445676320598445695912429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84297117547065630463941619 126445676320598445695912429)
        ·
          refine ⟨47417128620224417135967161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126445676320598445695912429 47417128620224417135967161)
          ·
            refine ⟨35562846465168312851975371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47417128620224417135967161 35562846465168312851975371)
            ·
              refine ⟨53344269697752469277963057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35562846465168312851975371 53344269697752469277963057)
              ·
                refine ⟨40008202273314351958472293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53344269697752469277963057 40008202273314351958472293)
                ·
                  refine ⟨7501537926246440992213555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40008202273314351958472293 7501537926246440992213555)
                  ·
                    refine ⟨11252306889369661488320333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501537926246440992213555 11252306889369661488320333)
                    ·
                      refine ⟨4219615083513623058120125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252306889369661488320333 4219615083513623058120125)
                      ·
                        rfl

theorem cell23_8217671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_8217671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217671 prefixEnd_8217671 := by exact prefixLift 8217671
  have htrace : WordTrace (prefixWord ++ tailWord_8217671) baseStart_8217671 baseEnd_8217671 := by
    simpa [prefixWord, tailWord_8217671, baseEnd_8217671] using wordTrace_append hprefix tailTrace_8217671
  have hstable : (prefixWord ++ tailWord_8217671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217671).length < 2 ^ (prefixWord ++ tailWord_8217671).sum := by decide
  have hdescent : baseEnd_8217671 < baseStart_8217671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217705 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 2, 1, 3]
def baseStart_8217705 : Nat := 118140960795 + 8217705 * 2 ^ 59
def prefixEnd_8217705 : Nat := 4983230072969 + 3 ^ 40 * 8217705 * 2
def baseEnd_8217705 : Nat := 4219632541855875925094969

theorem tailTrace_8217705 : CollatzResearch.WordTrace tailWord_8217705 prefixEnd_8217705 4219632541855875925094969 := by
  unfold tailWord_8217705
  simp only [CollatzResearch.WordTrace]
  refine ⟨299724324693665732122974569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199816216462443821415316379 299724324693665732122974569)
  ·
    refine ⟨224793243520249299092230927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299724324693665732122974569 224793243520249299092230927)
    ·
      refine ⟨337189865280373948638346391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224793243520249299092230927 337189865280373948638346391)
      ·
        refine ⟨505784797920560922957519587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337189865280373948638346391 505784797920560922957519587)
        ·
          refine ⟨758677196880841384436279381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505784797920560922957519587 758677196880841384436279381)
          ·
            refine ⟨8890748400947359973862649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 758677196880841384436279381 8890748400947359973862649)
            ·
              refine ⟨6668061300710519980396987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890748400947359973862649 6668061300710519980396987)
              ·
                refine ⟨10002091951065779970595481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6668061300710519980396987 10002091951065779970595481)
                ·
                  refine ⟨7501568963299334977946611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10002091951065779970595481 7501568963299334977946611)
                  ·
                    refine ⟨11252353444949002466919917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501568963299334977946611 11252353444949002466919917)
                    ·
                      refine ⟨4219632541855875925094969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252353444949002466919917 4219632541855875925094969)
                      ·
                        rfl

theorem cell23_8217705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 1, 3].length) (baseStart_8217705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217705 prefixEnd_8217705 := by exact prefixLift 8217705
  have htrace : WordTrace (prefixWord ++ tailWord_8217705) baseStart_8217705 baseEnd_8217705 := by
    simpa [prefixWord, tailWord_8217705, baseEnd_8217705] using wordTrace_append hprefix tailTrace_8217705
  have hstable : (prefixWord ++ tailWord_8217705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217705).length < 2 ^ (prefixWord ++ tailWord_8217705).sum := by decide
  have hdescent : baseEnd_8217705 < baseStart_8217705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217707 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_8217707 : Nat := 118140960795 + 8217707 * 2 ^ 59
def prefixEnd_8217707 : Nat := 4983230072969 + 3 ^ 40 * 8217707 * 2
def baseEnd_8217707 : Nat := 4219633568817184917269959

theorem tailTrace_8217707 : CollatzResearch.WordTrace tailWord_8217707 prefixEnd_8217707 4219633568817184917269959 := by
  unfold tailWord_8217707
  simp only [CollatzResearch.WordTrace]
  refine ⟨299724397639658486464547375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199816265093105657643031583 299724397639658486464547375)
  ·
    refine ⟨449586596459487729696821063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299724397639658486464547375 449586596459487729696821063)
    ·
      refine ⟨674379894689231594545231595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449586596459487729696821063 674379894689231594545231595)
      ·
        refine ⟨1011569842033847391817847393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674379894689231594545231595 1011569842033847391817847393)
        ·
          refine ⟨758677381525385543863385545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011569842033847391817847393 758677381525385543863385545)
          ·
            refine ⟨569008036144039157897539159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758677381525385543863385545 569008036144039157897539159)
            ·
              refine ⟨853512054216058736846308739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569008036144039157897539159 853512054216058736846308739)
              ·
                refine ⟨1280268081324088105269463109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853512054216058736846308739 1280268081324088105269463109)
                ·
                  refine ⟨240050265248266519738024333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1280268081324088105269463109 240050265248266519738024333)
                  ·
                    refine ⟨90018849468099944901759125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240050265248266519738024333 90018849468099944901759125)
                    ·
                      refine ⟨4219633568817184917269959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90018849468099944901759125 4219633568817184917269959)
                      ·
                        rfl

theorem cell23_8217707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_8217707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217707 prefixEnd_8217707 := by exact prefixLift 8217707
  have htrace : WordTrace (prefixWord ++ tailWord_8217707) baseStart_8217707 baseEnd_8217707 := by
    simpa [prefixWord, tailWord_8217707, baseEnd_8217707] using wordTrace_append hprefix tailTrace_8217707
  have hstable : (prefixWord ++ tailWord_8217707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217707).length < 2 ^ (prefixWord ++ tailWord_8217707).sum := by decide
  have hdescent : baseEnd_8217707 < baseStart_8217707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217711 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 1, 4, 2]
def baseStart_8217711 : Nat := 118140960795 + 8217711 * 2 ^ 59
def prefixEnd_8217711 : Nat := 4983230072969 + 3 ^ 40 * 8217711 * 2
def baseEnd_8217711 : Nat := 4219635622739802901619941

theorem tailTrace_8217711 : CollatzResearch.WordTrace tailWord_8217711 prefixEnd_8217711 4219635622739802901619941 := by
  unfold tailWord_8217711
  simp only [CollatzResearch.WordTrace]
  refine ⟨299724543531643995147692987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199816362354429330098461991 299724543531643995147692987)
  ·
    refine ⟨449586815297465992721539481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299724543531643995147692987 449586815297465992721539481)
    ·
      refine ⟨337190111473099494541154611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449586815297465992721539481 337190111473099494541154611)
      ·
        refine ⟨505785167209649241811731917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337190111473099494541154611 505785167209649241811731917)
        ·
          refine ⟨189669437703618465679399469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505785167209649241811731917 189669437703618465679399469)
          ·
            refine ⟨71126039138856924629774801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189669437703618465679399469 71126039138856924629774801)
            ·
              refine ⟨53344529354142693472331101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71126039138856924629774801 53344529354142693472331101)
              ·
                refine ⟨20004198507803510052124163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53344529354142693472331101 20004198507803510052124163)
                ·
                  refine ⟨30006297761705265078186245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20004198507803510052124163 30006297761705265078186245)
                  ·
                    refine ⟨5626180830319737202159921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30006297761705265078186245 5626180830319737202159921)
                    ·
                      refine ⟨4219635622739802901619941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626180830319737202159921 4219635622739802901619941)
                      ·
                        rfl

theorem cell23_8217711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4, 2].length) (baseStart_8217711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217711 prefixEnd_8217711 := by exact prefixLift 8217711
  have htrace : WordTrace (prefixWord ++ tailWord_8217711) baseStart_8217711 baseEnd_8217711 := by
    simpa [prefixWord, tailWord_8217711, baseEnd_8217711] using wordTrace_append hprefix tailTrace_8217711
  have hstable : (prefixWord ++ tailWord_8217711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217711).length < 2 ^ (prefixWord ++ tailWord_8217711).sum := by decide
  have hdescent : baseEnd_8217711 < baseStart_8217711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217714 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_8217714 : Nat := 118140960795 + 8217714 * 2 ^ 59
def prefixEnd_8217714 : Nat := 4983230072969 + 3 ^ 40 * 8217714 * 2
def baseEnd_8217714 : Nat := 4219637163181766389882427

theorem tailTrace_8217714 : CollatzResearch.WordTrace tailWord_8217714 prefixEnd_8217714 4219637163181766389882427 := by
  unfold tailWord_8217714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74931163237658281665013049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199816435300422084440034797 74931163237658281665013049)
  ·
    refine ⟨56198372428243711248759787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74931163237658281665013049 56198372428243711248759787)
    ·
      refine ⟨84297558642365566873139681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56198372428243711248759787 84297558642365566873139681)
      ·
        refine ⟨63223168981774175154854761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84297558642365566873139681 63223168981774175154854761)
        ·
          refine ⟨47417376736330631366141071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63223168981774175154854761 47417376736330631366141071)
          ·
            refine ⟨71126065104495947049211607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47417376736330631366141071 71126065104495947049211607)
            ·
              refine ⟨106689097656743920573817411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71126065104495947049211607 106689097656743920573817411)
              ·
                refine ⟨160033646485115880860726117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106689097656743920573817411 160033646485115880860726117)
                ·
                  refine ⟨30006308715959227661386147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160033646485115880860726117 30006308715959227661386147)
                  ·
                    refine ⟨45009463073938841492079221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30006308715959227661386147 45009463073938841492079221)
                    ·
                      refine ⟨4219637163181766389882427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45009463073938841492079221 4219637163181766389882427)
                      ·
                        rfl

theorem cell23_8217714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_8217714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217714 prefixEnd_8217714 := by exact prefixLift 8217714
  have htrace : WordTrace (prefixWord ++ tailWord_8217714) baseStart_8217714 baseEnd_8217714 := by
    simpa [prefixWord, tailWord_8217714, baseEnd_8217714] using wordTrace_append hprefix tailTrace_8217714
  have hstable : (prefixWord ++ tailWord_8217714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217714).length < 2 ^ (prefixWord ++ tailWord_8217714).sum := by decide
  have hdescent : baseEnd_8217714 < baseStart_8217714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217758 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_8217758 : Nat := 118140960795 + 8217758 * 2 ^ 59
def prefixEnd_8217758 : Nat := 4983230072969 + 3 ^ 40 * 8217758 * 2
def baseEnd_8217758 : Nat := 4219659756330564217732225

theorem tailTrace_8217758 : CollatzResearch.WordTrace tailWord_8217758 prefixEnd_8217758 4219659756330564217732225 := by
  unfold tailWord_8217758
  simp only [CollatzResearch.WordTrace]
  refine ⟨37465782220309215271831741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199817505174982481449769285 37465782220309215271831741)
  ·
    refine ⟨14049668332615955726936903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37465782220309215271831741 14049668332615955726936903)
    ·
      refine ⟨21074502498923933590405355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049668332615955726936903 21074502498923933590405355)
      ·
        refine ⟨31611753748385900385608033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21074502498923933590405355 31611753748385900385608033)
        ·
          refine ⟨23708815311289425289206025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31611753748385900385608033 23708815311289425289206025)
          ·
            refine ⟨17781611483467068966904519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23708815311289425289206025 17781611483467068966904519)
            ·
              refine ⟨26672417225200603450356779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17781611483467068966904519 26672417225200603450356779)
              ·
                refine ⟨40008625837800905175535169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26672417225200603450356779 40008625837800905175535169)
                ·
                  refine ⟨30006469378350678881651377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40008625837800905175535169 30006469378350678881651377)
                  ·
                    refine ⟨22504852033763009161238533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30006469378350678881651377 22504852033763009161238533)
                    ·
                      refine ⟨4219659756330564217732225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22504852033763009161238533 4219659756330564217732225)
                      ·
                        rfl

theorem cell23_8217758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_8217758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217758 prefixEnd_8217758 := by exact prefixLift 8217758
  have htrace : WordTrace (prefixWord ++ tailWord_8217758) baseStart_8217758 baseEnd_8217758 := by
    simpa [prefixWord, tailWord_8217758, baseEnd_8217758] using wordTrace_append hprefix tailTrace_8217758
  have hstable : (prefixWord ++ tailWord_8217758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217758).length < 2 ^ (prefixWord ++ tailWord_8217758).sum := by decide
  have hdescent : baseEnd_8217758 < baseStart_8217758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217761 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_8217761 : Nat := 118140960795 + 8217761 * 2 ^ 59
def prefixEnd_8217761 : Nat := 4983230072969 + 3 ^ 40 * 8217761 * 2
def baseEnd_8217761 : Nat := 4219661296772527705994711

theorem tailTrace_8217761 : CollatzResearch.WordTrace tailWord_8217761 prefixEnd_8217761 4219661296772527705994711 := by
  unfold tailWord_8217761
  simp only [CollatzResearch.WordTrace]
  refine ⟨299726367181462853687013137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199817578120975235791342091 299726367181462853687013137)
  ·
    refine ⟨224794775386097140265259853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299726367181462853687013137 224794775386097140265259853)
    ·
      refine ⟨84298040769786427599472445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224794775386097140265259853 84298040769786427599472445)
      ·
        refine ⟨31611765288669910349802167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84298040769786427599472445 31611765288669910349802167)
        ·
          refine ⟨47417647933004865524703251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31611765288669910349802167 47417647933004865524703251)
          ·
            refine ⟨71126471899507298287054877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47417647933004865524703251 71126471899507298287054877)
            ·
              refine ⟨26672426962315236857645579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71126471899507298287054877 26672426962315236857645579)
              ·
                refine ⟨40008640443472855286468369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26672426962315236857645579 40008640443472855286468369)
                ·
                  refine ⟨30006480332604641464851277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40008640443472855286468369 30006480332604641464851277)
                  ·
                    refine ⟨11252430124726740549319229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30006480332604641464851277 11252430124726740549319229)
                    ·
                      refine ⟨4219661296772527705994711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252430124726740549319229 4219661296772527705994711)
                      ·
                        rfl

theorem cell23_8217761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_8217761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217761 prefixEnd_8217761 := by exact prefixLift 8217761
  have htrace : WordTrace (prefixWord ++ tailWord_8217761) baseStart_8217761 baseEnd_8217761 := by
    simpa [prefixWord, tailWord_8217761, baseEnd_8217761] using wordTrace_append hprefix tailTrace_8217761
  have hstable : (prefixWord ++ tailWord_8217761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217761).length < 2 ^ (prefixWord ++ tailWord_8217761).sum := by decide
  have hdescent : baseEnd_8217761 < baseStart_8217761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217888 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 3, 5]
def baseStart_8217888 : Nat := 118140960795 + 8217888 * 2 ^ 59
def prefixEnd_8217888 : Nat := 4983230072969 + 3 ^ 40 * 8217888 * 2
def baseEnd_8217888 : Nat := 1406575502938549569702209

theorem tailTrace_8217888 : CollatzResearch.WordTrace tailWord_8217888 prefixEnd_8217888 1406575502938549569702209 := by
  unfold tailWord_8217888
  simp only [CollatzResearch.WordTrace]
  refine ⟨149865499626001377188443159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199820666168001836251257545 149865499626001377188443159)
  ·
    refine ⟨224798249439002065782664739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149865499626001377188443159 224798249439002065782664739)
    ·
      refine ⟨337197374158503098673997109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224798249439002065782664739 337197374158503098673997109)
      ·
        refine ⟨31612253827359665500687229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337197374158503098673997109 31612253827359665500687229)
        ·
          refine ⟨11854595185259874562757711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31612253827359665500687229 11854595185259874562757711)
          ·
            refine ⟨17781892777889811844136567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854595185259874562757711 17781892777889811844136567)
            ·
              refine ⟨26672839166834717766204851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17781892777889811844136567 26672839166834717766204851)
              ·
                refine ⟨40009258750252076649307277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26672839166834717766204851 40009258750252076649307277)
                ·
                  refine ⟨15003472031344528743490229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40009258750252076649307277 15003472031344528743490229)
                  ·
                    refine ⟨1406575502938549569702209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15003472031344528743490229 1406575502938549569702209)
                    ·
                      rfl

theorem cell23_8217888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_8217888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217888 prefixEnd_8217888 := by exact prefixLift 8217888
  have htrace : WordTrace (prefixWord ++ tailWord_8217888) baseStart_8217888 baseEnd_8217888 := by
    simpa [prefixWord, tailWord_8217888, baseEnd_8217888] using wordTrace_append hprefix tailTrace_8217888
  have hstable : (prefixWord ++ tailWord_8217888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217888).length < 2 ^ (prefixWord ++ tailWord_8217888).sum := by decide
  have hdescent : baseEnd_8217888 < baseStart_8217888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217905 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 1, 5]
def baseStart_8217905 : Nat := 118140960795 + 8217905 * 2 ^ 59
def prefixEnd_8217905 : Nat := 4983230072969 + 3 ^ 40 * 8217905 * 2
def baseEnd_8217905 : Nat := 1406578412662258380864683

theorem tailTrace_8217905 : CollatzResearch.WordTrace tailWord_8217905 prefixEnd_8217905 1406578412662258380864683 := by
  unfold tailWord_8217905
  simp only [CollatzResearch.WordTrace]
  refine ⟨299731619292941166280255169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199821079528627444186836779 299731619292941166280255169)
  ·
    refine ⟨224798714469705874710191377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299731619292941166280255169 224798714469705874710191377)
    ·
      refine ⟨168599035852279406032643533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224798714469705874710191377 168599035852279406032643533)
      ·
        refine ⟨63224638444604777262241325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168599035852279406032643533 63224638444604777262241325)
        ·
          refine ⟨23709239416726791473340497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63224638444604777262241325 23709239416726791473340497)
          ·
            refine ⟨17781929562545093605005373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23709239416726791473340497 17781929562545093605005373)
            ·
              refine ⟨6668223585954410101877015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17781929562545093605005373 6668223585954410101877015)
              ·
                refine ⟨10002335378931615152815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6668223585954410101877015 10002335378931615152815523)
                ·
                  refine ⟨15003503068397422729223285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10002335378931615152815523 15003503068397422729223285)
                  ·
                    refine ⟨1406578412662258380864683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15003503068397422729223285 1406578412662258380864683)
                    ·
                      rfl

theorem cell23_8217905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_8217905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217905 prefixEnd_8217905 := by exact prefixLift 8217905
  have htrace : WordTrace (prefixWord ++ tailWord_8217905) baseStart_8217905 baseEnd_8217905 := by
    simpa [prefixWord, tailWord_8217905, baseEnd_8217905] using wordTrace_append hprefix tailTrace_8217905
  have hstable : (prefixWord ++ tailWord_8217905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217905).length < 2 ^ (prefixWord ++ tailWord_8217905).sum := by decide
  have hdescent : baseEnd_8217905 < baseStart_8217905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217919 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 1, 1, 3]
def baseStart_8217919 : Nat := 118140960795 + 8217919 * 2 ^ 59
def prefixEnd_8217919 : Nat := 4983230072969 + 3 ^ 40 * 8217919 * 2
def baseEnd_8217919 : Nat := 4219742426715938087818985

theorem tailTrace_8217919 : CollatzResearch.WordTrace tailWord_8217919 prefixEnd_8217919 4219742426715938087818985 := by
  unfold tailWord_8217919
  simp only [CollatzResearch.WordTrace]
  refine ⟨299732129914890446671264811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199821419943260297780843207 299732129914890446671264811)
  ·
    refine ⟨449598194872335670006897217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299732129914890446671264811 449598194872335670006897217)
    ·
      refine ⟨337198646154251752505172913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449598194872335670006897217 337198646154251752505172913)
      ·
        refine ⟨252898984615688814378879685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337198646154251752505172913 252898984615688814378879685)
        ·
          refine ⟨47418559615441652696039941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252898984615688814378879685 47418559615441652696039941)
          ·
            refine ⟨8890979927895309880507489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47418559615441652696039941 8890979927895309880507489)
            ·
              refine ⟨6668234945921482410380617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8890979927895309880507489 6668234945921482410380617)
              ·
                refine ⟨5001176209441111807785463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6668234945921482410380617 5001176209441111807785463)
                ·
                  refine ⟨7501764314161667711678195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001176209441111807785463 7501764314161667711678195)
                  ·
                    refine ⟨11252646471242501567517293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501764314161667711678195 11252646471242501567517293)
                    ·
                      refine ⟨4219742426715938087818985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252646471242501567517293 4219742426715938087818985)
                      ·
                        rfl

theorem cell23_8217919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_8217919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217919 prefixEnd_8217919 := by exact prefixLift 8217919
  have htrace : WordTrace (prefixWord ++ tailWord_8217919) baseStart_8217919 baseEnd_8217919 := by
    simpa [prefixWord, tailWord_8217919, baseEnd_8217919] using wordTrace_append hprefix tailTrace_8217919
  have hstable : (prefixWord ++ tailWord_8217919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217919).length < 2 ^ (prefixWord ++ tailWord_8217919).sum := by decide
  have hdescent : baseEnd_8217919 < baseStart_8217919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217959 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_8217959 : Nat := 118140960795 + 8217959 * 2 ^ 59
def prefixEnd_8217959 : Nat := 4983230072969 + 3 ^ 40 * 8217959 * 2
def baseEnd_8217959 : Nat := 4219762965942117931318801

theorem tailTrace_8217959 : CollatzResearch.WordTrace tailWord_8217959 prefixEnd_8217959 4219762965942117931318801 := by
  unfold tailWord_8217959
  simp only [CollatzResearch.WordTrace]
  refine ⟨299733588834745533502720931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199822392556497022335147287 299733588834745533502720931)
  ·
    refine ⟨449600383252118300254081397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299733588834745533502720931 449600383252118300254081397)
    ·
      refine ⟨42150035929886090648820131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449600383252118300254081397 42150035929886090648820131)
      ·
        refine ⟨63225053894829135973230197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42150035929886090648820131 63225053894829135973230197)
        ·
          refine ⟨5927348802640231497490331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63225053894829135973230197 5927348802640231497490331)
          ·
            refine ⟨8891023203960347246235497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927348802640231497490331 8891023203960347246235497)
            ·
              refine ⟨6668267402970260434676623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8891023203960347246235497 6668267402970260434676623)
              ·
                refine ⟨10002401104455390652014935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6668267402970260434676623 10002401104455390652014935)
                ·
                  refine ⟨15003601656683085978022403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10002401104455390652014935 15003601656683085978022403)
                  ·
                    refine ⟨22505402485024628967033605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15003601656683085978022403 22505402485024628967033605)
                    ·
                      refine ⟨4219762965942117931318801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22505402485024628967033605 4219762965942117931318801)
                      ·
                        rfl

theorem cell23_8217959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_8217959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217959 prefixEnd_8217959 := by exact prefixLift 8217959
  have htrace : WordTrace (prefixWord ++ tailWord_8217959) baseStart_8217959 baseEnd_8217959 := by
    simpa [prefixWord, tailWord_8217959, baseEnd_8217959] using wordTrace_append hprefix tailTrace_8217959
  have hstable : (prefixWord ++ tailWord_8217959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217959).length < 2 ^ (prefixWord ++ tailWord_8217959).sum := by decide
  have hdescent : baseEnd_8217959 < baseStart_8217959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8217962 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_8217962 : Nat := 118140960795 + 8217962 * 2 ^ 59
def prefixEnd_8217962 : Nat := 4983230072969 + 3 ^ 40 * 8217962 * 2
def baseEnd_8217962 : Nat := 4219764506384081419581287

theorem tailTrace_8217962 : CollatzResearch.WordTrace tailWord_8217962 prefixEnd_8217962 4219764506384081419581287 := by
  unfold tailWord_8217962
  simp only [CollatzResearch.WordTrace]
  refine ⟨74933424563433666253770035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199822465502489776676720093 74933424563433666253770035)
  ·
    refine ⟨112400136845150499380655053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74933424563433666253770035 112400136845150499380655053)
    ·
      refine ⟨42150051316931437267745645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112400136845150499380655053 42150051316931437267745645)
      ·
        refine ⟨15806269243849288975404617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42150051316931437267745645 15806269243849288975404617)
        ·
          refine ⟨11854701932886966731553463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15806269243849288975404617 11854701932886966731553463)
          ·
            refine ⟨17782052899330450097330195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854701932886966731553463 17782052899330450097330195)
            ·
              refine ⟨26673079348995675145995293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17782052899330450097330195 26673079348995675145995293)
              ·
                refine ⟨10002404755873378179748235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26673079348995675145995293 10002404755873378179748235)
                ·
                  refine ⟨15003607133810067269622353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10002404755873378179748235 15003607133810067269622353)
                  ·
                    refine ⟨11252705350357550452216765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15003607133810067269622353 11252705350357550452216765)
                    ·
                      refine ⟨4219764506384081419581287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252705350357550452216765 4219764506384081419581287)
                      ·
                        rfl

theorem cell23_8217962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_8217962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8217962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8217962 prefixEnd_8217962 := by exact prefixLift 8217962
  have htrace : WordTrace (prefixWord ++ tailWord_8217962) baseStart_8217962 baseEnd_8217962 := by
    simpa [prefixWord, tailWord_8217962, baseEnd_8217962] using wordTrace_append hprefix tailTrace_8217962
  have hstable : (prefixWord ++ tailWord_8217962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8217962).length < 2 ^ (prefixWord ++ tailWord_8217962).sum := by decide
  have hdescent : baseEnd_8217962 < baseStart_8217962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8217962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218001 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_8218001 : Nat := 118140960795 + 8218001 * 2 ^ 59
def prefixEnd_8218001 : Nat := 4983230072969 + 3 ^ 40 * 8218001 * 2
def baseEnd_8218001 : Nat := 4219784532129606766993607

theorem tailTrace_8218001 : CollatzResearch.WordTrace tailWord_8218001 prefixEnd_8218001 4219784532129606766993607 := by
  unfold tailWord_8218001
  simp only [CollatzResearch.WordTrace]
  refine ⟨299735120700593374675749857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199823413800395583117166571 299735120700593374675749857)
  ·
    refine ⟨224801340525445031006812393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299735120700593374675749857 224801340525445031006812393)
    ·
      refine ⟨168601005394083773255109295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224801340525445031006812393 168601005394083773255109295)
      ·
        refine ⟨252901508091125659882663943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168601005394083773255109295 252901508091125659882663943)
        ·
          refine ⟨379352262136688489823995915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252901508091125659882663943 379352262136688489823995915)
          ·
            refine ⟨569028393205032734735993873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379352262136688489823995915 569028393205032734735993873)
            ·
              refine ⟨426771294903774551051995405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569028393205032734735993873 426771294903774551051995405)
              ·
                refine ⟨160039235588915456644498277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426771294903774551051995405 160039235588915456644498277)
                ·
                  refine ⟨30007356672921648120843427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160039235588915456644498277 30007356672921648120843427)
                  ·
                    refine ⟨45011035009382472181265141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30007356672921648120843427 45011035009382472181265141)
                    ·
                      refine ⟨4219784532129606766993607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45011035009382472181265141 4219784532129606766993607)
                      ·
                        rfl

theorem cell23_8218001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_8218001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218001 prefixEnd_8218001 := by exact prefixLift 8218001
  have htrace : WordTrace (prefixWord ++ tailWord_8218001) baseStart_8218001 baseEnd_8218001 := by
    simpa [prefixWord, tailWord_8218001, baseEnd_8218001] using wordTrace_append hprefix tailTrace_8218001
  have hstable : (prefixWord ++ tailWord_8218001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218001).length < 2 ^ (prefixWord ++ tailWord_8218001).sum := by decide
  have hdescent : baseEnd_8218001 < baseStart_8218001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218018 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_8218018 : Nat := 118140960795 + 8218018 * 2 ^ 59
def prefixEnd_8218018 : Nat := 4983230072969 + 3 ^ 40 * 8218018 * 2
def baseEnd_8218018 : Nat := 4219793261300733200481029

theorem tailTrace_8218018 : CollatzResearch.WordTrace tailWord_8218018 prefixEnd_8218018 4219793261300733200481029 := by
  unfold tailWord_8218018
  simp only [CollatzResearch.WordTrace]
  refine ⟨74933935185382946644779677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199823827161021191052745805 74933935185382946644779677)
  ·
    refine ⟨28100225694518604991792379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74933935185382946644779677 28100225694518604991792379)
    ·
      refine ⟨42150338541777907487688569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28100225694518604991792379 42150338541777907487688569)
      ·
        refine ⟨31612753906333430615766427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42150338541777907487688569 31612753906333430615766427)
        ·
          refine ⟨47419130859500145923649641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31612753906333430615766427 47419130859500145923649641)
          ·
            refine ⟨35564348144625109442737231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47419130859500145923649641 35564348144625109442737231)
            ·
              refine ⟨53346522216937664164105847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35564348144625109442737231 53346522216937664164105847)
              ·
                refine ⟨80019783325406496246158771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53346522216937664164105847 80019783325406496246158771)
                ·
                  refine ⟨120029674988109744369238157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80019783325406496246158771 120029674988109744369238157)
                  ·
                    refine ⟨45011128120541154138464309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120029674988109744369238157 45011128120541154138464309)
                    ·
                      refine ⟨4219793261300733200481029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45011128120541154138464309 4219793261300733200481029)
                      ·
                        rfl

theorem cell23_8218018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_8218018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218018 prefixEnd_8218018 := by exact prefixLift 8218018
  have htrace : WordTrace (prefixWord ++ tailWord_8218018) baseStart_8218018 baseEnd_8218018 := by
    simpa [prefixWord, tailWord_8218018, baseEnd_8218018] using wordTrace_append hprefix tailTrace_8218018
  have hstable : (prefixWord ++ tailWord_8218018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218018).length < 2 ^ (prefixWord ++ tailWord_8218018).sum := by decide
  have hdescent : baseEnd_8218018 < baseStart_8218018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218048 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_8218048 : Nat := 118140960795 + 8218048 * 2 ^ 59
def prefixEnd_8218048 : Nat := 4983230072969 + 3 ^ 40 * 8218048 * 2
def baseEnd_8218048 : Nat := 4219808665720368083105891

theorem tailTrace_8218048 : CollatzResearch.WordTrace tailWord_8218048 prefixEnd_8218048 4219808665720368083105891 := by
  unfold tailWord_8218048
  simp only [CollatzResearch.WordTrace]
  refine ⟨149868417465711550851355399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199824556620948734468473865 149868417465711550851355399)
  ·
    refine ⟨224802626198567326277033099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149868417465711550851355399 224802626198567326277033099)
    ·
      refine ⟨337203939297850989415549649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224802626198567326277033099 337203939297850989415549649)
      ·
        refine ⟨252902954473388242061662237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337203939297850989415549649 252902954473388242061662237)
        ·
          refine ⟨94838607927520590773123339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252902954473388242061662237 94838607927520590773123339)
          ·
            refine ⟨142257911891280886159685009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94838607927520590773123339 142257911891280886159685009)
            ·
              refine ⟨106693433918460664619763757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142257911891280886159685009 106693433918460664619763757)
              ·
                refine ⟨40010037719422749232411409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106693433918460664619763757 40010037719422749232411409)
                ·
                  refine ⟨30007528289567061924308557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40010037719422749232411409 30007528289567061924308557)
                  ·
                    refine ⟨11252823108587648221615709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30007528289567061924308557 11252823108587648221615709)
                    ·
                      refine ⟨4219808665720368083105891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11252823108587648221615709 4219808665720368083105891)
                      ·
                        rfl

theorem cell23_8218048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_8218048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218048 prefixEnd_8218048 := by exact prefixLift 8218048
  have htrace : WordTrace (prefixWord ++ tailWord_8218048) baseStart_8218048 baseEnd_8218048 := by
    simpa [prefixWord, tailWord_8218048, baseEnd_8218048] using wordTrace_append hprefix tailTrace_8218048
  have hstable : (prefixWord ++ tailWord_8218048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218048).length < 2 ^ (prefixWord ++ tailWord_8218048).sum := by decide
  have hdescent : baseEnd_8218048 < baseStart_8218048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218051 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 3, 7]
def baseStart_8218051 : Nat := 118140960795 + 8218051 * 2 ^ 59
def prefixEnd_8218051 : Nat := 4983230072969 + 3 ^ 40 * 8218051 * 2
def baseEnd_8218051 : Nat := 1406603402054110523789459

theorem tailTrace_8218051 : CollatzResearch.WordTrace tailWord_8218051 prefixEnd_8218051 1406603402054110523789459 := by
  unfold tailWord_8218051
  simp only [CollatzResearch.WordTrace]
  refine ⟨299736944350412233215070007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199824629566941488810046671 299736944350412233215070007)
  ·
    refine ⟨449605416525618349822605011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299736944350412233215070007 449605416525618349822605011)
    ·
      refine ⟨674408124788427524733907517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449605416525618349822605011 674408124788427524733907517)
      ·
        refine ⟨252903046795660321775215319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674408124788427524733907517 252903046795660321775215319)
        ·
          refine ⟨379354570193490482662822979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252903046795660321775215319 379354570193490482662822979)
          ·
            refine ⟨569031855290235723994234469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379354570193490482662822979 569031855290235723994234469)
            ·
              refine ⟨106693472866919198248918963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 569031855290235723994234469 106693472866919198248918963)
              ·
                refine ⟨160040209300378797373378445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106693472866919198248918963 160040209300378797373378445)
                ·
                  refine ⟨60015078487642049015016917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160040209300378797373378445 60015078487642049015016917)
                  ·
                    refine ⟨1406603402054110523789459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60015078487642049015016917 1406603402054110523789459)
                    ·
                      rfl

theorem cell23_8218051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_8218051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218051 prefixEnd_8218051 := by exact prefixLift 8218051
  have htrace : WordTrace (prefixWord ++ tailWord_8218051) baseStart_8218051 baseEnd_8218051 := by
    simpa [prefixWord, tailWord_8218051, baseEnd_8218051] using wordTrace_append hprefix tailTrace_8218051
  have hstable : (prefixWord ++ tailWord_8218051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218051).length < 2 ^ (prefixWord ++ tailWord_8218051).sum := by decide
  have hdescent : baseEnd_8218051 < baseStart_8218051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218085 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_8218085 : Nat := 118140960795 + 8218085 * 2 ^ 59
def prefixEnd_8218085 : Nat := 4983230072969 + 3 ^ 40 * 8218085 * 2
def baseEnd_8218085 : Nat := 1406609221501528146114407

theorem tailTrace_8218085 : CollatzResearch.WordTrace tailWord_8218085 prefixEnd_8218085 1406609221501528146114407 := by
  unfold tailWord_8218085
  simp only [CollatzResearch.WordTrace]
  refine ⟨299738184432289057021807709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199825456288192704681205139 299738184432289057021807709)
  ·
    refine ⟨112401819162108396383177891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299738184432289057021807709 112401819162108396383177891)
    ·
      refine ⟨168602728743162594574766837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112401819162108396383177891 168602728743162594574766837)
      ·
        refine ⟨15806505819671493241384391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168602728743162594574766837 15806505819671493241384391)
        ·
          refine ⟨23709758729507239862076587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15806505819671493241384391 23709758729507239862076587)
          ·
            refine ⟨35564638094260859793114881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23709758729507239862076587 35564638094260859793114881)
            ·
              refine ⟨26673478570695644844836161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35564638094260859793114881 26673478570695644844836161)
              ·
                refine ⟨20005108928021733633627121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26673478570695644844836161 20005108928021733633627121)
                ·
                  refine ⟨15003831696016300225220341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20005108928021733633627121 15003831696016300225220341)
                  ·
                    refine ⟨1406609221501528146114407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15003831696016300225220341 1406609221501528146114407)
                    ·
                      rfl

theorem cell23_8218085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_8218085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218085 prefixEnd_8218085 := by exact prefixLift 8218085
  have htrace : WordTrace (prefixWord ++ tailWord_8218085) baseStart_8218085 baseEnd_8218085 := by
    simpa [prefixWord, tailWord_8218085, baseEnd_8218085] using wordTrace_append hprefix tailTrace_8218085
  have hstable : (prefixWord ++ tailWord_8218085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218085).length < 2 ^ (prefixWord ++ tailWord_8218085).sum := by decide
  have hdescent : baseEnd_8218085 < baseStart_8218085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218122 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_8218122 : Nat := 118140960795 + 8218122 * 2 ^ 59
def prefixEnd_8218122 : Nat := 4983230072969 + 3 ^ 40 * 8218122 * 2
def baseEnd_8218122 : Nat := 4219846663288800793580551

theorem tailTrace_8218122 : CollatzResearch.WordTrace tailWord_8218122 prefixEnd_8218122 4219846663288800793580551 := by
  unfold tailWord_8218122
  simp only [CollatzResearch.WordTrace]
  refine ⟨74934883483288753085226155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199826355955436674893936413 74934883483288753085226155)
  ·
    refine ⟨112402325224933129627839233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74934883483288753085226155 112402325224933129627839233)
    ·
      refine ⟨84301743918699847220879425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112402325224933129627839233 84301743918699847220879425)
      ·
        refine ⟨63226307939024885415659569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84301743918699847220879425 63226307939024885415659569)
        ·
          refine ⟨47419730954268664061744677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63226307939024885415659569 47419730954268664061744677)
          ·
            refine ⟨8891199553925374511577127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47419730954268664061744677 8891199553925374511577127)
            ·
              refine ⟨13336799330888061767365691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891199553925374511577127 13336799330888061767365691)
              ·
                refine ⟨20005198996332092651048537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13336799330888061767365691 20005198996332092651048537)
                ·
                  refine ⟨15003899247249069488286403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20005198996332092651048537 15003899247249069488286403)
                  ·
                    refine ⟨22505848870873604232429605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15003899247249069488286403 22505848870873604232429605)
                    ·
                      refine ⟨4219846663288800793580551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22505848870873604232429605 4219846663288800793580551)
                      ·
                        rfl

theorem cell23_8218122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_8218122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218122 prefixEnd_8218122 := by exact prefixLift 8218122
  have htrace : WordTrace (prefixWord ++ tailWord_8218122) baseStart_8218122 baseEnd_8218122 := by
    simpa [prefixWord, tailWord_8218122, baseEnd_8218122] using wordTrace_append hprefix tailTrace_8218122
  have hstable : (prefixWord ++ tailWord_8218122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218122).length < 2 ^ (prefixWord ++ tailWord_8218122).sum := by decide
  have hdescent : baseEnd_8218122 < baseStart_8218122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218145 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 6]
def baseStart_8218145 : Nat := 118140960795 + 8218145 * 2 ^ 59
def prefixEnd_8218145 : Nat := 4983230072969 + 3 ^ 40 * 8218145 * 2
def baseEnd_8218145 : Nat := 468873163704872689288105

theorem tailTrace_8218145 : CollatzResearch.WordTrace tailWord_8218145 prefixEnd_8218145 468873163704872689288105 := by
  unfold tailWord_8218145
  simp only [CollatzResearch.WordTrace]
  refine ⟨299740372812071687268991889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199826915208047791512661259 299740372812071687268991889)
  ·
    refine ⟨224805279609053765451743917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299740372812071687268991889 224805279609053765451743917)
    ·
      refine ⟨84301979853395162044403969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224805279609053765451743917 84301979853395162044403969)
      ·
        refine ⟨63226484890046371533302977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84301979853395162044403969 63226484890046371533302977)
        ·
          refine ⟨47419863667534778649977233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63226484890046371533302977 47419863667534778649977233)
          ·
            refine ⟨35564897750651083987482925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47419863667534778649977233 35564897750651083987482925)
            ·
              refine ⟨13336836656494156495306097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35564897750651083987482925 13336836656494156495306097)
              ·
                refine ⟨10002627492370617371479573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13336836656494156495306097 10002627492370617371479573)
                ·
                  refine ⟨468873163704872689288105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10002627492370617371479573 468873163704872689288105)
                  ·
                    rfl

theorem cell23_8218145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 6].length) (baseStart_8218145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218145 prefixEnd_8218145 := by exact prefixLift 8218145
  have htrace : WordTrace (prefixWord ++ tailWord_8218145) baseStart_8218145 baseEnd_8218145 := by
    simpa [prefixWord, tailWord_8218145, baseEnd_8218145] using wordTrace_append hprefix tailTrace_8218145
  have hstable : (prefixWord ++ tailWord_8218145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218145).length < 2 ^ (prefixWord ++ tailWord_8218145).sum := by decide
  have hdescent : baseEnd_8218145 < baseStart_8218145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218175 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 1, 5]
def baseStart_8218175 : Nat := 118140960795 + 8218175 * 2 ^ 59
def prefixEnd_8218175 : Nat := 4983230072969 + 3 ^ 40 * 8218175 * 2
def baseEnd_8218175 : Nat := 1406624625921163028739269

theorem tailTrace_8218175 : CollatzResearch.WordTrace tailWord_8218175 prefixEnd_8218175 1406624625921163028739269 := by
  unfold tailWord_8218175
  simp only [CollatzResearch.WordTrace]
  refine ⟨299741467001963002392583979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199827644667975334928389319 299741467001963002392583979)
  ·
    refine ⟨449612200502944503588875969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299741467001963002392583979 449612200502944503588875969)
    ·
      refine ⟨337209150377208377691656977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449612200502944503588875969 337209150377208377691656977)
      ·
        refine ⟨252906862782906283268742733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337209150377208377691656977 252906862782906283268742733)
        ·
          refine ⟨94840073543589856225778525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252906862782906283268742733 94840073543589856225778525)
          ·
            refine ⟨35565027578846196084666947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94840073543589856225778525 35565027578846196084666947)
            ·
              refine ⟨53347541368269294127000421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35565027578846196084666947 53347541368269294127000421)
              ·
                refine ⟨10002664006550492648812579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53347541368269294127000421 10002664006550492648812579)
                ·
                  refine ⟨15003996009825738973218869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10002664006550492648812579 15003996009825738973218869)
                  ·
                    refine ⟨1406624625921163028739269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15003996009825738973218869 1406624625921163028739269)
                    ·
                      rfl

theorem cell23_8218175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_8218175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218175 prefixEnd_8218175 := by exact prefixLift 8218175
  have htrace : WordTrace (prefixWord ++ tailWord_8218175) baseStart_8218175 baseEnd_8218175 := by
    simpa [prefixWord, tailWord_8218175, baseEnd_8218175] using wordTrace_append hprefix tailTrace_8218175
  have hstable : (prefixWord ++ tailWord_8218175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218175).length < 2 ^ (prefixWord ++ tailWord_8218175).sum := by decide
  have hdescent : baseEnd_8218175 < baseStart_8218175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218215 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_8218215 : Nat := 118140960795 + 8218215 * 2 ^ 59
def prefixEnd_8218215 : Nat := 4983230072969 + 3 ^ 40 * 8218215 * 2
def baseEnd_8218215 : Nat := 4219894416989668929717623

theorem tailTrace_8218215 : CollatzResearch.WordTrace tailWord_8218215 prefixEnd_8218215 4219894416989668929717623 := by
  unfold tailWord_8218215
  simp only [CollatzResearch.WordTrace]
  refine ⟨299742925921818089224040099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199828617281212059482693399 299742925921818089224040099)
  ·
    refine ⟨449614388882727133836060149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299742925921818089224040099 449614388882727133836060149)
    ·
      refine ⟨42151348957755668797130639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449614388882727133836060149 42151348957755668797130639)
      ·
        refine ⟨63227023436633503195695959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42151348957755668797130639 63227023436633503195695959)
        ·
          refine ⟨94840535154950254793543939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63227023436633503195695959 94840535154950254793543939)
          ·
            refine ⟨142260802732425382190315909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94840535154950254793543939 142260802732425382190315909)
            ·
              refine ⟨26673900512329759160684233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142260802732425382190315909 26673900512329759160684233)
              ·
                refine ⟨20005425384247319370513175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26673900512329759160684233 20005425384247319370513175)
                ·
                  refine ⟨30008138076370979055769763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20005425384247319370513175 30008138076370979055769763)
                  ·
                    refine ⟨45012207114556468583654645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30008138076370979055769763 45012207114556468583654645)
                    ·
                      refine ⟨4219894416989668929717623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45012207114556468583654645 4219894416989668929717623)
                      ·
                        rfl

theorem cell23_8218215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_8218215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218215 prefixEnd_8218215 := by exact prefixLift 8218215
  have htrace : WordTrace (prefixWord ++ tailWord_8218215) baseStart_8218215 baseEnd_8218215 := by
    simpa [prefixWord, tailWord_8218215, baseEnd_8218215] using wordTrace_append hprefix tailTrace_8218215
  have hstable : (prefixWord ++ tailWord_8218215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218215).length < 2 ^ (prefixWord ++ tailWord_8218215).sum := by decide
  have hdescent : baseEnd_8218215 < baseStart_8218215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218229 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_8218229 : Nat := 118140960795 + 8218229 * 2 ^ 59
def prefixEnd_8218229 : Nat := 4983230072969 + 3 ^ 40 * 8218229 * 2
def baseEnd_8218229 : Nat := 4219901605718831874942559

theorem tailTrace_8218229 : CollatzResearch.WordTrace tailWord_8218229 prefixEnd_8218229 4219901605718831874942559 := by
  unfold tailWord_8218229
  simp only [CollatzResearch.WordTrace]
  refine ⟨299743436543767369615049741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199828957695844913076699827 299743436543767369615049741)
  ·
    refine ⟨112403788703912763605643653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299743436543767369615049741 112403788703912763605643653)
    ·
      refine ⟨21075710381983643176058185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112403788703912763605643653 21075710381983643176058185)
      ·
        refine ⟨15806782786487732382043639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21075710381983643176058185 15806782786487732382043639)
        ·
          refine ⟨23710174179731598573065459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15806782786487732382043639 23710174179731598573065459)
          ·
            refine ⟨35565261269597397859598189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23710174179731598573065459 35565261269597397859598189)
            ·
              refine ⟨13336972976099024197349321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35565261269597397859598189 13336972976099024197349321)
              ·
                refine ⟨10002729732074268148011991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13336972976099024197349321 10002729732074268148011991)
                ·
                  refine ⟨15004094598111402222017987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10002729732074268148011991 15004094598111402222017987)
                  ·
                    refine ⟨22506141897167103333026981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15004094598111402222017987 22506141897167103333026981)
                    ·
                      refine ⟨4219901605718831874942559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22506141897167103333026981 4219901605718831874942559)
                      ·
                        rfl

theorem cell23_8218229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_8218229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218229 prefixEnd_8218229 := by exact prefixLift 8218229
  have htrace : WordTrace (prefixWord ++ tailWord_8218229) baseStart_8218229 baseEnd_8218229 := by
    simpa [prefixWord, tailWord_8218229, baseEnd_8218229] using wordTrace_append hprefix tailTrace_8218229
  have hstable : (prefixWord ++ tailWord_8218229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218229).length < 2 ^ (prefixWord ++ tailWord_8218229).sum := by decide
  have hdescent : baseEnd_8218229 < baseStart_8218229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218263 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 1, 2, 2]
def baseStart_8218263 : Nat := 118140960795 + 8218263 * 2 ^ 59
def prefixEnd_8218263 : Nat := 4983230072969 + 3 ^ 40 * 8218263 * 2
def baseEnd_8218263 : Nat := 4219919064061084741917403

theorem tailTrace_8218263 : CollatzResearch.WordTrace tailWord_8218263 prefixEnd_8218263 4219919064061084741917403 := by
  unfold tailWord_8218263
  simp only [CollatzResearch.WordTrace]
  refine ⟨299744676625644193421787443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199829784417096128947858295 299744676625644193421787443)
  ·
    refine ⟨449617014938466290132681165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299744676625644193421787443 449617014938466290132681165)
    ·
      refine ⟨168606380601924858799755437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449617014938466290132681165 168606380601924858799755437)
      ·
        refine ⟨63227392725721822049908289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168606380601924858799755437 63227392725721822049908289)
        ·
          refine ⟨47420544544291366537431217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63227392725721822049908289 47420544544291366537431217)
          ·
            refine ⟨35565408408218524903073413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47420544544291366537431217 35565408408218524903073413)
            ·
              refine ⟨6668514076540973419326265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35565408408218524903073413 6668514076540973419326265)
              ·
                refine ⟨5001385557405730064494699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6668514076540973419326265 5001385557405730064494699)
                ·
                  refine ⟨7502078336108595096742049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001385557405730064494699 7502078336108595096742049)
                  ·
                    refine ⟨5626558752081446322556537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502078336108595096742049 5626558752081446322556537)
                    ·
                      refine ⟨4219919064061084741917403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626558752081446322556537 4219919064061084741917403)
                      ·
                        rfl

theorem cell23_8218263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_8218263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218263 prefixEnd_8218263 := by exact prefixLift 8218263
  have htrace : WordTrace (prefixWord ++ tailWord_8218263) baseStart_8218263 baseEnd_8218263 := by
    simpa [prefixWord, tailWord_8218263, baseEnd_8218263] using wordTrace_append hprefix tailTrace_8218263
  have hstable : (prefixWord ++ tailWord_8218263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218263).length < 2 ^ (prefixWord ++ tailWord_8218263).sum := by decide
  have hdescent : baseEnd_8218263 < baseStart_8218263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218280 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_8218280 : Nat := 118140960795 + 8218280 * 2 ^ 59
def prefixEnd_8218280 : Nat := 4983230072969 + 3 ^ 40 * 8218280 * 2
def baseEnd_8218280 : Nat := 4219927793232211175404825

theorem tailTrace_8218280 : CollatzResearch.WordTrace tailWord_8218280 prefixEnd_8218280 4219927793232211175404825 := by
  unfold tailWord_8218280
  simp only [CollatzResearch.WordTrace]
  refine ⟨149872648333291302662578147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199830197777721736883437529 149872648333291302662578147)
  ·
    refine ⟨224808972499936953993867221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149872648333291302662578147 224808972499936953993867221)
    ·
      refine ⟨5268960292967272359231263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 224808972499936953993867221 5268960292967272359231263)
      ·
        refine ⟨7903440439450908538846895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268960292967272359231263 7903440439450908538846895)
        ·
          refine ⟨11855160659176362808270343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903440439450908538846895 11855160659176362808270343)
          ·
            refine ⟨17782740988764544212405515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855160659176362808270343 17782740988764544212405515)
            ·
              refine ⟨26674111483146816318608273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17782740988764544212405515 26674111483146816318608273)
              ·
                refine ⟨20005583612360112238956205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26674111483146816318608273 20005583612360112238956205)
                ·
                  refine ⟨7502093854635042089608577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20005583612360112238956205 7502093854635042089608577)
                  ·
                    refine ⟨5626570390976281567206433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502093854635042089608577 5626570390976281567206433)
                    ·
                      refine ⟨4219927793232211175404825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626570390976281567206433 4219927793232211175404825)
                      ·
                        rfl

theorem cell23_8218280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_8218280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218280 prefixEnd_8218280 := by exact prefixLift 8218280
  have htrace : WordTrace (prefixWord ++ tailWord_8218280) baseStart_8218280 baseEnd_8218280 := by
    simpa [prefixWord, tailWord_8218280, baseEnd_8218280] using wordTrace_append hprefix tailTrace_8218280
  have hstable : (prefixWord ++ tailWord_8218280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218280).length < 2 ^ (prefixWord ++ tailWord_8218280).sum := by decide
  have hdescent : baseEnd_8218280 < baseStart_8218280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218355 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 1, 7]
def baseStart_8218355 : Nat := 118140960795 + 8218355 * 2 ^ 59
def prefixEnd_8218355 : Nat := 4983230072969 + 3 ^ 40 * 8218355 * 2
def baseEnd_8218355 : Nat := 1406655434760432793988993

theorem tailTrace_8218355 : CollatzResearch.WordTrace tailWord_8218355 prefixEnd_8218355 1406655434760432793988993 := by
  unfold tailWord_8218355
  simp only [CollatzResearch.WordTrace]
  refine ⟨299748032141310893134136519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199832021427540595422757679 299748032141310893134136519)
  ·
    refine ⟨449622048211966339701204779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299748032141310893134136519 449622048211966339701204779)
    ·
      refine ⟨674433072317949509551807169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449622048211966339701204779 674433072317949509551807169)
      ·
        refine ⟨505824804238462132163855377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674433072317949509551807169 505824804238462132163855377)
        ·
          refine ⟨379368603178846599122891533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505824804238462132163855377 379368603178846599122891533)
          ·
            refine ⟨142263226192067474671084325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379368603178846599122891533 142263226192067474671084325)
            ·
              refine ⟨26674354911012651500828311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142263226192067474671084325 26674354911012651500828311)
              ·
                refine ⟨40011532366518977251242467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26674354911012651500828311 40011532366518977251242467)
                ·
                  refine ⟨60017298549778465876863701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40011532366518977251242467 60017298549778465876863701)
                  ·
                    refine ⟨1406655434760432793988993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60017298549778465876863701 1406655434760432793988993)
                    ·
                      rfl

theorem cell23_8218355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 7].length) (baseStart_8218355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218355 prefixEnd_8218355 := by exact prefixLift 8218355
  have htrace : WordTrace (prefixWord ++ tailWord_8218355) baseStart_8218355 baseEnd_8218355 := by
    simpa [prefixWord, tailWord_8218355, baseEnd_8218355] using wordTrace_append hprefix tailTrace_8218355
  have hstable : (prefixWord ++ tailWord_8218355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218355).length < 2 ^ (prefixWord ++ tailWord_8218355).sum := by decide
  have hdescent : baseEnd_8218355 < baseStart_8218355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218356 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8218356 : Nat := 118140960795 + 8218356 * 2 ^ 59
def prefixEnd_8218356 : Nat := 4983230072969 + 3 ^ 40 * 8218356 * 2
def baseEnd_8218356 : Nat := 4219966817761952878054475

theorem tailTrace_8218356 : CollatzResearch.WordTrace tailWord_8218356 prefixEnd_8218356 4219966817761952878054475 := by
  unfold tailWord_8218356
  simp only [CollatzResearch.WordTrace]
  refine ⟨149874034307153635152461461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199832045742871513536615281 149874034307153635152461461)
  ·
    refine ⟨7025345358147826647771631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149874034307153635152461461 7025345358147826647771631)
    ·
      refine ⟨10538018037221739971657447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7025345358147826647771631 10538018037221739971657447)
      ·
        refine ⟨15807027055832609957486171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538018037221739971657447 15807027055832609957486171)
        ·
          refine ⟨23710540583748914936229257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15807027055832609957486171 23710540583748914936229257)
          ·
            refine ⟨17782905437811686202171943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23710540583748914936229257 17782905437811686202171943)
            ·
              refine ⟨26674358156717529303257915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17782905437811686202171943 26674358156717529303257915)
              ·
                refine ⟨40011537235076293954886873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26674358156717529303257915 40011537235076293954886873)
                ·
                  refine ⟨30008652926307220466165155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40011537235076293954886873 30008652926307220466165155)
                  ·
                    refine ⟨45012979389460830699247733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30008652926307220466165155 45012979389460830699247733)
                    ·
                      refine ⟨4219966817761952878054475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45012979389460830699247733 4219966817761952878054475)
                      ·
                        rfl

theorem cell23_8218356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8218356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218356 prefixEnd_8218356 := by exact prefixLift 8218356
  have htrace : WordTrace (prefixWord ++ tailWord_8218356) baseStart_8218356 baseEnd_8218356 := by
    simpa [prefixWord, tailWord_8218356, baseEnd_8218356] using wordTrace_append hprefix tailTrace_8218356
  have hstable : (prefixWord ++ tailWord_8218356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218356).length < 2 ^ (prefixWord ++ tailWord_8218356).sum := by decide
  have hdescent : baseEnd_8218356 < baseStart_8218356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218362 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2]
def baseStart_8218362 : Nat := 118140960795 + 8218362 * 2 ^ 59
def prefixEnd_8218362 : Nat := 4983230072969 + 3 ^ 40 * 8218362 * 2
def baseEnd_8218362 : Nat := 4219969898645879854579447

theorem tailTrace_8218362 : CollatzResearch.WordTrace tailWord_8218362 prefixEnd_8218362 4219969898645879854579447 := by
  unfold tailWord_8218362
  simp only [CollatzResearch.WordTrace]
  refine ⟨74937071863071383332410335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199832191634857022219760893 74937071863071383332410335)
  ·
    refine ⟨112405607794607074998615503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74937071863071383332410335 112405607794607074998615503)
    ·
      refine ⟨168608411691910612497923255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112405607794607074998615503 168608411691910612497923255)
      ·
        refine ⟨252912617537865918746884883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168608411691910612497923255 252912617537865918746884883)
        ·
          refine ⟨379368926306798878120327325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252912617537865918746884883 379368926306798878120327325)
          ·
            refine ⟨142263347365049579295122747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379368926306798878120327325 142263347365049579295122747)
            ·
              refine ⟨213395021047574368942684121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142263347365049579295122747 213395021047574368942684121)
              ·
                refine ⟨160046265785680776707013091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213395021047574368942684121 160046265785680776707013091)
                ·
                  refine ⟨240069398678521165060519637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160046265785680776707013091 240069398678521165060519637)
                  ·
                    refine ⟨5626626531527839806105929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240069398678521165060519637 5626626531527839806105929)
                    ·
                      refine ⟨4219969898645879854579447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626626531527839806105929 4219969898645879854579447)
                      ·
                        rfl

theorem cell23_8218362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_8218362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218362 prefixEnd_8218362 := by exact prefixLift 8218362
  have htrace : WordTrace (prefixWord ++ tailWord_8218362) baseStart_8218362 baseEnd_8218362 := by
    simpa [prefixWord, tailWord_8218362, baseEnd_8218362] using wordTrace_append hprefix tailTrace_8218362
  have hstable : (prefixWord ++ tailWord_8218362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218362).length < 2 ^ (prefixWord ++ tailWord_8218362).sum := by decide
  have hdescent : baseEnd_8218362 < baseStart_8218362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218372 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_8218372 : Nat := 118140960795 + 8218372 * 2 ^ 59
def prefixEnd_8218372 : Nat := 4983230072969 + 3 ^ 40 * 8218372 * 2
def baseEnd_8218372 : Nat := 1406658344484141605151467

theorem tailTrace_8218372 : CollatzResearch.WordTrace tailWord_8218372 prefixEnd_8218372 1406658344484141605151467 := by
  unfold tailWord_8218372
  simp only [CollatzResearch.WordTrace]
  refine ⟨149874326091124652518752685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199832434788166203358336913 149874326091124652518752685)
  ·
    refine ⟨56202872284171744694532257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149874326091124652518752685 56202872284171744694532257)
    ·
      refine ⟨42152154213128808520899193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56202872284171744694532257 42152154213128808520899193)
      ·
        refine ⟨31614115659846606390674395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42152154213128808520899193 31614115659846606390674395)
        ·
          refine ⟨47421173489769909586011593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31614115659846606390674395 47421173489769909586011593)
          ·
            refine ⟨35565880117327432189508695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47421173489769909586011593 35565880117327432189508695)
            ·
              refine ⟨53348820175991148284263043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35565880117327432189508695 53348820175991148284263043)
              ·
                refine ⟨80023230263986722426394565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53348820175991148284263043 80023230263986722426394565)
                ·
                  refine ⟨15004355674497510454948981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80023230263986722426394565 15004355674497510454948981)
                  ·
                    refine ⟨1406658344484141605151467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15004355674497510454948981 1406658344484141605151467)
                    ·
                      rfl

theorem cell23_8218372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_8218372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218372 prefixEnd_8218372 := by exact prefixLift 8218372
  have htrace : WordTrace (prefixWord ++ tailWord_8218372) baseStart_8218372 baseEnd_8218372 := by
    simpa [prefixWord, tailWord_8218372, baseEnd_8218372] using wordTrace_append hprefix tailTrace_8218372
  have hstable : (prefixWord ++ tailWord_8218372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218372).length < 2 ^ (prefixWord ++ tailWord_8218372).sum := by decide
  have hdescent : baseEnd_8218372 < baseStart_8218372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218381 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_8218381 : Nat := 118140960795 + 8218381 * 2 ^ 59
def prefixEnd_8218381 : Nat := 4983230072969 + 3 ^ 40 * 8218381 * 2
def baseEnd_8218381 : Nat := 4219979654778315280241861

theorem tailTrace_8218381 : CollatzResearch.WordTrace tailWord_8218381 prefixEnd_8218381 4219979654778315280241861 := by
  unfold tailWord_8218381
  simp only [CollatzResearch.WordTrace]
  refine ⟨299748980439216699574582997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199832653626144466383055331 299748980439216699574582997)
  ·
    refine ⟨7025366729044141396279289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 299748980439216699574582997 7025366729044141396279289)
    ·
      refine ⟨5269025046783106047209467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7025366729044141396279289 5269025046783106047209467)
      ·
        refine ⟨7903537570174659070814201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269025046783106047209467 7903537570174659070814201)
        ·
          refine ⟨5927653177630994303110651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7903537570174659070814201 5927653177630994303110651)
          ·
            refine ⟨8891479766446491454665977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927653177630994303110651 8891479766446491454665977)
            ·
              refine ⟨6668609824834868590999483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8891479766446491454665977 6668609824834868590999483)
              ·
                refine ⟨10002914737252302886499225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6668609824834868590999483 10002914737252302886499225)
                ·
                  refine ⟨7502186052939227164874419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10002914737252302886499225 7502186052939227164874419)
                  ·
                    refine ⟨11253279079408840747311629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502186052939227164874419 11253279079408840747311629)
                    ·
                      refine ⟨4219979654778315280241861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11253279079408840747311629 4219979654778315280241861)
                      ·
                        rfl

theorem cell23_8218381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_8218381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218381 prefixEnd_8218381 := by exact prefixLift 8218381
  have htrace : WordTrace (prefixWord ++ tailWord_8218381) baseStart_8218381 baseEnd_8218381 := by
    simpa [prefixWord, tailWord_8218381, baseEnd_8218381] using wordTrace_append hprefix tailTrace_8218381
  have hstable : (prefixWord ++ tailWord_8218381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218381).length < 2 ^ (prefixWord ++ tailWord_8218381).sum := by decide
  have hdescent : baseEnd_8218381 < baseStart_8218381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218516 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_8218516 : Nat := 118140960795 + 8218516 * 2 ^ 59
def prefixEnd_8218516 : Nat := 4983230072969 + 3 ^ 40 * 8218516 * 2
def baseEnd_8218516 : Nat := 4220048974666672252053739

theorem tailTrace_8218516 : CollatzResearch.WordTrace tailWord_8218516 prefixEnd_8218516 4220048974666672252053739 := by
  unfold tailWord_8218516
  simp only [CollatzResearch.WordTrace]
  refine ⟨149876952146863808815373701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199835936195818411753831601 149876952146863808815373701)
  ·
    refine ⟨28101928527536964152882569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149876952146863808815373701 28101928527536964152882569)
    ·
      refine ⟨21076446395652723114661927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28101928527536964152882569 21076446395652723114661927)
      ·
        refine ⟨31614669593479084671992891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21076446395652723114661927 31614669593479084671992891)
        ·
          refine ⟨47422004390218627007989337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31614669593479084671992891 47422004390218627007989337)
          ·
            refine ⟨35566503292663970255992003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47422004390218627007989337 35566503292663970255992003)
            ·
              refine ⟨53349754938995955383988005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35566503292663970255992003 53349754938995955383988005)
              ·
                refine ⟨10003079051061741634497751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53349754938995955383988005 10003079051061741634497751)
                ·
                  refine ⟨15004618576592612451746627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003079051061741634497751 15004618576592612451746627)
                  ·
                    refine ⟨22506927864888918677619941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15004618576592612451746627 22506927864888918677619941)
                    ·
                      refine ⟨4220048974666672252053739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22506927864888918677619941 4220048974666672252053739)
                      ·
                        rfl

theorem cell23_8218516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_8218516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218516 prefixEnd_8218516 := by exact prefixLift 8218516
  have htrace : WordTrace (prefixWord ++ tailWord_8218516) baseStart_8218516 baseEnd_8218516 := by
    simpa [prefixWord, tailWord_8218516, baseEnd_8218516] using wordTrace_append hprefix tailTrace_8218516
  have hstable : (prefixWord ++ tailWord_8218516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218516).length < 2 ^ (prefixWord ++ tailWord_8218516).sum := by decide
  have hdescent : baseEnd_8218516 < baseStart_8218516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218527 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 1, 1, 3]
def baseStart_8218527 : Nat := 118140960795 + 8218527 * 2 ^ 59
def prefixEnd_8218527 : Nat := 4983230072969 + 3 ^ 40 * 8218527 * 2
def baseEnd_8218527 : Nat := 4220054622953871709016189

theorem tailTrace_8218527 : CollatzResearch.WordTrace tailWord_8218527 prefixEnd_8218527 4220054622953871709016189 := by
  unfold tailWord_8218527
  simp only [CollatzResearch.WordTrace]
  refine ⟨299754305496687766509397835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199836203664458511006265223 299754305496687766509397835)
  ·
    refine ⟨449631458245031649764096753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299754305496687766509397835 449631458245031649764096753)
    ·
      refine ⟨337223593683773737323072565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449631458245031649764096753 337223593683773737323072565)
      ·
        refine ⟨31614711907853787874038053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337223593683773737323072565 31614711907853787874038053)
        ·
          refine ⟨5927758482722585226382135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31614711907853787874038053 5927758482722585226382135)
          ·
            refine ⟨8891637724083877839573203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927758482722585226382135 8891637724083877839573203)
            ·
              refine ⟨13337456586125816759359805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891637724083877839573203 13337456586125816759359805)
              ·
                refine ⟨5001546219797181284759927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13337456586125816759359805 5001546219797181284759927)
                ·
                  refine ⟨7502319329695771927139891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001546219797181284759927 7502319329695771927139891)
                  ·
                    refine ⟨11253478994543657890709837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502319329695771927139891 11253478994543657890709837)
                    ·
                      refine ⟨4220054622953871709016189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11253478994543657890709837 4220054622953871709016189)
                      ·
                        rfl

theorem cell23_8218527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_8218527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218527 prefixEnd_8218527 := by exact prefixLift 8218527
  have htrace : WordTrace (prefixWord ++ tailWord_8218527) baseStart_8218527 baseEnd_8218527 := by
    simpa [prefixWord, tailWord_8218527, baseEnd_8218527] using wordTrace_append hprefix tailTrace_8218527
  have hstable : (prefixWord ++ tailWord_8218527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218527).length < 2 ^ (prefixWord ++ tailWord_8218527).sum := by decide
  have hdescent : baseEnd_8218527 < baseStart_8218527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218552 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_8218552 : Nat := 118140960795 + 8218552 * 2 ^ 59
def prefixEnd_8218552 : Nat := 4983230072969 + 3 ^ 40 * 8218552 * 2
def baseEnd_8218552 : Nat := 1406689153323411370401191

theorem tailTrace_8218552 : CollatzResearch.WordTrace tailWord_8218552 prefixEnd_8218552 1406689153323411370401191 := by
  unfold tailWord_8218552
  simp only [CollatzResearch.WordTrace]
  refine ⟨149877608660798597889528955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199836811547731463852705273 149877608660798597889528955)
  ·
    refine ⟨224816412991197896834293433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149877608660798597889528955 224816412991197896834293433)
    ·
      refine ⟨168612309743398422625720075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224816412991197896834293433 168612309743398422625720075)
      ·
        refine ⟨252918464615097633938580113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168612309743398422625720075 252918464615097633938580113)
        ·
          refine ⟨189688848461323225453935085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252918464615097633938580113 189688848461323225453935085)
          ·
            refine ⟨71133318172996209545225657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189688848461323225453935085 71133318172996209545225657)
            ·
              refine ⟨53349988629747157158919243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71133318172996209545225657 53349988629747157158919243)
              ·
                refine ⟨80024982944620735738378865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53349988629747157158919243 80024982944620735738378865)
                ·
                  refine ⟨60018737208465551803784149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80024982944620735738378865 60018737208465551803784149)
                  ·
                    refine ⟨1406689153323411370401191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60018737208465551803784149 1406689153323411370401191)
                    ·
                      rfl

theorem cell23_8218552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_8218552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218552 prefixEnd_8218552 := by exact prefixLift 8218552
  have htrace : WordTrace (prefixWord ++ tailWord_8218552) baseStart_8218552 baseEnd_8218552 := by
    simpa [prefixWord, tailWord_8218552, baseEnd_8218552] using wordTrace_append hprefix tailTrace_8218552
  have hstable : (prefixWord ++ tailWord_8218552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218552).length < 2 ^ (prefixWord ++ tailWord_8218552).sum := by decide
  have hdescent : baseEnd_8218552 < baseStart_8218552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218556 : List Nat := [2, 2, 2, 5, 1, 1, 2, 8]
def baseStart_8218556 : Nat := 118140960795 + 8218556 * 2 ^ 59
def prefixEnd_8218556 : Nat := 4983230072969 + 3 ^ 40 * 8218556 * 2
def baseEnd_8218556 : Nat := 156298870884920447983465

theorem tailTrace_8218556 : CollatzResearch.WordTrace tailWord_8218556 prefixEnd_8218556 156298870884920447983465 := by
  unfold tailWord_8218556
  simp only [CollatzResearch.WordTrace]
  refine ⟨149877681606791352231101761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199836908809055136308135681 149877681606791352231101761)
  ·
    refine ⟨112408261205093514173326321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149877681606791352231101761 112408261205093514173326321)
    ·
      refine ⟨84306195903820135629994741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112408261205093514173326321 84306195903820135629994741)
      ·
        refine ⟨7903705865983137715312007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84306195903820135629994741 7903705865983137715312007)
        ·
          refine ⟨11855558798974706572968011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903705865983137715312007 11855558798974706572968011)
          ·
            refine ⟨17783338198462059859452017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855558798974706572968011 17783338198462059859452017)
            ·
              refine ⟨13337503648846544894589013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17783338198462059859452017 13337503648846544894589013)
              ·
                refine ⟨156298870884920447983465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13337503648846544894589013 156298870884920447983465)
                ·
                  rfl

theorem cell23_8218556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 8].length) (baseStart_8218556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218556 prefixEnd_8218556 := by exact prefixLift 8218556
  have htrace : WordTrace (prefixWord ++ tailWord_8218556) baseStart_8218556 baseEnd_8218556 := by
    simpa [prefixWord, tailWord_8218556, baseEnd_8218556] using wordTrace_append hprefix tailTrace_8218556
  have hstable : (prefixWord ++ tailWord_8218556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218556).length < 2 ^ (prefixWord ++ tailWord_8218556).sum := by decide
  have hdescent : baseEnd_8218556 < baseStart_8218556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218629 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 7]
def baseStart_8218629 : Nat := 118140960795 + 8218629 * 2 ^ 59
def prefixEnd_8218629 : Nat := 4983230072969 + 3 ^ 40 * 8218629 * 2
def baseEnd_8218629 : Nat := 468900777553403367771191

theorem tailTrace_8218629 : CollatzResearch.WordTrace tailWord_8218629 prefixEnd_8218629 468900777553403367771191 := by
  unfold tailWord_8218629
  simp only [CollatzResearch.WordTrace]
  refine ⟨299758025742318237929610941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199838683828212158619740627 299758025742318237929610941)
  ·
    refine ⟨112409259653369339223604103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299758025742318237929610941 112409259653369339223604103)
    ·
      refine ⟨168613889480054008835406155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112409259653369339223604103 168613889480054008835406155)
      ·
        refine ⟨252920834220081013253109233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168613889480054008835406155 252920834220081013253109233)
        ·
          refine ⟨189690625665060759939831925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252920834220081013253109233 189690625665060759939831925)
          ·
            refine ⟨17783496156099446244359243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189690625665060759939831925 17783496156099446244359243)
            ·
              refine ⟨26675244234149169366538865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17783496156099446244359243 26675244234149169366538865)
              ·
                refine ⟨20006433175611877024904149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26675244234149169366538865 20006433175611877024904149)
                ·
                  refine ⟨468900777553403367771191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20006433175611877024904149 468900777553403367771191)
                  ·
                    rfl

theorem cell23_8218629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_8218629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218629 prefixEnd_8218629 := by exact prefixLift 8218629
  have htrace : WordTrace (prefixWord ++ tailWord_8218629) baseStart_8218629 baseEnd_8218629 := by
    simpa [prefixWord, tailWord_8218629, baseEnd_8218629] using wordTrace_append hprefix tailTrace_8218629
  have hstable : (prefixWord ++ tailWord_8218629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218629).length < 2 ^ (prefixWord ++ tailWord_8218629).sum := by decide
  have hdescent : baseEnd_8218629 < baseStart_8218629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218657 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_8218657 : Nat := 118140960795 + 8218657 * 2 ^ 59
def prefixEnd_8218657 : Nat := 4983230072969 + 3 ^ 40 * 8218657 * 2
def baseEnd_8218657 : Nat := 4220121375438956200390591

theorem tailTrace_8218657 : CollatzResearch.WordTrace tailWord_8218657 prefixEnd_8218657 4220121375438956200390591 := by
  unfold tailWord_8218657
  simp only [CollatzResearch.WordTrace]
  refine ⟨299759046986216798711630225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199839364657477865807753483 299759046986216798711630225)
  ·
    refine ⟨224819285239662599033722669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299759046986216798711630225 224819285239662599033722669)
    ·
      refine ⟨84307231964873474637646001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224819285239662599033722669 84307231964873474637646001)
      ·
        refine ⟨63230423973655105978234501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84307231964873474637646001 63230423973655105978234501)
        ·
          refine ⟨11855704495060332370918969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63230423973655105978234501 11855704495060332370918969)
          ·
            refine ⟨8891778371295249278189227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11855704495060332370918969 8891778371295249278189227)
            ·
              refine ⟨13337667556942873917283841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891778371295249278189227 13337667556942873917283841)
              ·
                refine ⟨10003250667707155437962881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13337667556942873917283841 10003250667707155437962881)
                ·
                  refine ⟨7502438000780366578472161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10003250667707155437962881 7502438000780366578472161)
                  ·
                    refine ⟨5626828500585274933854121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502438000780366578472161 5626828500585274933854121)
                    ·
                      refine ⟨4220121375438956200390591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626828500585274933854121 4220121375438956200390591)
                      ·
                        rfl

theorem cell23_8218657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_8218657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218657 prefixEnd_8218657 := by exact prefixLift 8218657
  have htrace : WordTrace (prefixWord ++ tailWord_8218657) baseStart_8218657 baseEnd_8218657 := by
    simpa [prefixWord, tailWord_8218657, baseEnd_8218657] using wordTrace_append hprefix tailTrace_8218657
  have hstable : (prefixWord ++ tailWord_8218657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218657).length < 2 ^ (prefixWord ++ tailWord_8218657).sum := by decide
  have hdescent : baseEnd_8218657 < baseStart_8218657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218659 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 4, 5]
def baseStart_8218659 : Nat := 118140960795 + 8218659 * 2 ^ 59
def prefixEnd_8218659 : Nat := 4983230072969 + 3 ^ 40 * 8218659 * 2
def baseEnd_8218659 : Nat := 1406707467466755064188527

theorem tailTrace_8218659 : CollatzResearch.WordTrace tailWord_8218659 prefixEnd_8218659 1406707467466755064188527 := by
  unfold tailWord_8218659
  simp only [CollatzResearch.WordTrace]
  refine ⟨299759119932209553053203031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199839413288139702035468687 299759119932209553053203031)
  ·
    refine ⟨449638679898314329579804547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299759119932209553053203031 449638679898314329579804547)
    ·
      refine ⟨674458019847471494369706821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449638679898314329579804547 674458019847471494369706821)
      ·
        refine ⟨126460878721400905194320029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 674458019847471494369706821 126460878721400905194320029)
        ·
          refine ⟨47422829520525339447870011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126460878721400905194320029 47422829520525339447870011)
          ·
            refine ⟨71134244280788009171805017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47422829520525339447870011 71134244280788009171805017)
            ·
              refine ⟨53350683210591006878853763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71134244280788009171805017 53350683210591006878853763)
              ·
                refine ⟨80026024815886510318280645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53350683210591006878853763 80026024815886510318280645)
                ·
                  refine ⟨15004879652978720684677621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80026024815886510318280645 15004879652978720684677621)
                  ·
                    refine ⟨1406707467466755064188527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15004879652978720684677621 1406707467466755064188527)
                    ·
                      rfl

theorem cell23_8218659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 5].length) (baseStart_8218659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218659 prefixEnd_8218659 := by exact prefixLift 8218659
  have htrace : WordTrace (prefixWord ++ tailWord_8218659) baseStart_8218659 baseEnd_8218659 := by
    simpa [prefixWord, tailWord_8218659, baseEnd_8218659] using wordTrace_append hprefix tailTrace_8218659
  have hstable : (prefixWord ++ tailWord_8218659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218659).length < 2 ^ (prefixWord ++ tailWord_8218659).sum := by decide
  have hdescent : baseEnd_8218659 < baseStart_8218659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218663 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 7]
def baseStart_8218663 : Nat := 118140960795 + 8218663 * 2 ^ 59
def prefixEnd_8218663 : Nat := 4983230072969 + 3 ^ 40 * 8218663 * 2
def baseEnd_8218663 : Nat := 468902717369209241879507

theorem tailTrace_8218663 : CollatzResearch.WordTrace tailWord_8218663 prefixEnd_8218663 468902717369209241879507 := by
  unfold tailWord_8218663
  simp only [CollatzResearch.WordTrace]
  refine ⟨299759265824195061736348643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199839510549463374490899095 299759265824195061736348643)
  ·
    refine ⟨449638898736292592604522965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299759265824195061736348643 449638898736292592604522965)
    ·
      refine ⟨10538411689131857639168507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 449638898736292592604522965 10538411689131857639168507)
      ·
        refine ⟨15807617533697786458752761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538411689131857639168507 15807617533697786458752761)
        ·
          refine ⟨11855713150273339844064571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15807617533697786458752761 11855713150273339844064571)
          ·
            refine ⟨17783569725410009766096857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855713150273339844064571 17783569725410009766096857)
            ·
              refine ⟨13337677294057507324572643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17783569725410009766096857 13337677294057507324572643)
              ·
                refine ⟨20006515941086260986858965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13337677294057507324572643 20006515941086260986858965)
                ·
                  refine ⟨468902717369209241879507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20006515941086260986858965 468902717369209241879507)
                  ·
                    rfl

theorem cell23_8218663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 7].length) (baseStart_8218663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218663 prefixEnd_8218663 := by exact prefixLift 8218663
  have htrace : WordTrace (prefixWord ++ tailWord_8218663) baseStart_8218663 baseEnd_8218663 := by
    simpa [prefixWord, tailWord_8218663, baseEnd_8218663] using wordTrace_append hprefix tailTrace_8218663
  have hstable : (prefixWord ++ tailWord_8218663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218663).length < 2 ^ (prefixWord ++ tailWord_8218663).sum := by decide
  have hdescent : baseEnd_8218663 < baseStart_8218663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218679 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_8218679 : Nat := 118140960795 + 8218679 * 2 ^ 59
def prefixEnd_8218679 : Nat := 4983230072969 + 3 ^ 40 * 8218679 * 2
def baseEnd_8218679 : Nat := 4220132672013355114315489

theorem tailTrace_8218679 : CollatzResearch.WordTrace tailWord_8218679 prefixEnd_8218679 4220132672013355114315489 := by
  unfold tailWord_8218679
  simp only [CollatzResearch.WordTrace]
  refine ⟨299759849392137096468931091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199839899594758064312620727 299759849392137096468931091)
  ·
    refine ⟨449639774088205644703396637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299759849392137096468931091 449639774088205644703396637)
    ·
      refine ⟨168614915283077116763773739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449639774088205644703396637 168614915283077116763773739)
      ·
        refine ⟨252922372924615675145660609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168614915283077116763773739 252922372924615675145660609)
        ·
          refine ⟨189691779693461756359245457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252922372924615675145660609 189691779693461756359245457)
          ·
            refine ⟨142268834770096317269434093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189691779693461756359245457 142268834770096317269434093)
            ·
              refine ⟨53350813038786118976037785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142268834770096317269434093 53350813038786118976037785)
              ·
                refine ⟨40013109779089589232028339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53350813038786118976037785 40013109779089589232028339)
                ·
                  refine ⟨60019664668634383848042509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40013109779089589232028339 60019664668634383848042509)
                  ·
                    refine ⟨22507374250737893943015941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60019664668634383848042509 22507374250737893943015941)
                    ·
                      refine ⟨4220132672013355114315489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22507374250737893943015941 4220132672013355114315489)
                      ·
                        rfl

theorem cell23_8218679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_8218679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218679 prefixEnd_8218679 := by exact prefixLift 8218679
  have htrace : WordTrace (prefixWord ++ tailWord_8218679) baseStart_8218679 baseEnd_8218679 := by
    simpa [prefixWord, tailWord_8218679, baseEnd_8218679] using wordTrace_append hprefix tailTrace_8218679
  have hstable : (prefixWord ++ tailWord_8218679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218679).length < 2 ^ (prefixWord ++ tailWord_8218679).sum := by decide
  have hdescent : baseEnd_8218679 < baseStart_8218679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218696 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_8218696 : Nat := 118140960795 + 8218696 * 2 ^ 59
def prefixEnd_8218696 : Nat := 4983230072969 + 3 ^ 40 * 8218696 * 2
def baseEnd_8218696 : Nat := 4220141401184481547802911

theorem tailTrace_8218696 : CollatzResearch.WordTrace tailWord_8218696 prefixEnd_8218696 4220141401184481547802911 := by
  unfold tailWord_8218696
  simp only [CollatzResearch.WordTrace]
  refine ⟨149880234716537754186149971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199840312955383672248199961 149880234716537754186149971)
  ·
    refine ⟨224820352074806631279224957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149880234716537754186149971 224820352074806631279224957)
    ·
      refine ⟨84307632028052486729709359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224820352074806631279224957 84307632028052486729709359)
      ·
        refine ⟨126461448042078730094564039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84307632028052486729709359 126461448042078730094564039)
        ·
          refine ⟨189692172063118095141846059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126461448042078730094564039 189692172063118095141846059)
          ·
            refine ⟨284538258094677142712769089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189692172063118095141846059 284538258094677142712769089)
            ·
              refine ⟨213403693571007857034576817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284538258094677142712769089 213403693571007857034576817)
              ·
                refine ⟨160052770178255892775932613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213403693571007857034576817 160052770178255892775932613)
                ·
                  refine ⟨30009894408422979895487365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160052770178255892775932613 30009894408422979895487365)
                  ·
                    refine ⟨5626855201579308730403881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30009894408422979895487365 5626855201579308730403881)
                    ·
                      refine ⟨4220141401184481547802911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626855201579308730403881 4220141401184481547802911)
                      ·
                        rfl

theorem cell23_8218696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_8218696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218696 prefixEnd_8218696 := by exact prefixLift 8218696
  have htrace : WordTrace (prefixWord ++ tailWord_8218696) baseStart_8218696 baseEnd_8218696 := by
    simpa [prefixWord, tailWord_8218696, baseEnd_8218696] using wordTrace_append hprefix tailTrace_8218696
  have hstable : (prefixWord ++ tailWord_8218696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218696).length < 2 ^ (prefixWord ++ tailWord_8218696).sum := by decide
  have hdescent : baseEnd_8218696 < baseStart_8218696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218710 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_8218710 : Nat := 118140960795 + 8218710 * 2 ^ 59
def prefixEnd_8218710 : Nat := 4983230072969 + 3 ^ 40 * 8218710 * 2
def baseEnd_8218710 : Nat := 1406716196637881497675949

theorem tailTrace_8218710 : CollatzResearch.WordTrace tailWord_8218710 prefixEnd_8218710 1406716196637881497675949 := by
  unfold tailWord_8218710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735061253439049297706849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199840653370016525842206389 18735061253439049297706849)
  ·
    refine ⟨14051295940079286973280137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18735061253439049297706849 14051295940079286973280137)
    ·
      refine ⟨10538471955059465229960103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14051295940079286973280137 10538471955059465229960103)
      ·
        refine ⟨15807707932589197844940155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538471955059465229960103 15807707932589197844940155)
        ·
          refine ⟨23711561898883796767410233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15807707932589197844940155 23711561898883796767410233)
          ·
            refine ⟨17783671424162847575557675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23711561898883796767410233 17783671424162847575557675)
            ·
              refine ⟨26675507136244271363336513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17783671424162847575557675 26675507136244271363336513)
              ·
                refine ⟨20006630352183203522502385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26675507136244271363336513 20006630352183203522502385)
                ·
                  refine ⟨15004972764137402641876789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20006630352183203522502385 15004972764137402641876789)
                  ·
                    refine ⟨1406716196637881497675949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15004972764137402641876789 1406716196637881497675949)
                    ·
                      rfl

theorem cell23_8218710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_8218710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218710 prefixEnd_8218710 := by exact prefixLift 8218710
  have htrace : WordTrace (prefixWord ++ tailWord_8218710) baseStart_8218710 baseEnd_8218710 := by
    simpa [prefixWord, tailWord_8218710, baseEnd_8218710] using wordTrace_append hprefix tailTrace_8218710
  have hstable : (prefixWord ++ tailWord_8218710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218710).length < 2 ^ (prefixWord ++ tailWord_8218710).sum := by decide
  have hdescent : baseEnd_8218710 < baseStart_8218710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218723 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 1, 4]
def baseStart_8218723 : Nat := 118140960795 + 8218723 * 2 ^ 59
def prefixEnd_8218723 : Nat := 4983230072969 + 3 ^ 40 * 8218723 * 2
def baseEnd_8218723 : Nat := 1406718421720717647388429

theorem tailTrace_8218723 : CollatzResearch.WordTrace tailWord_8218723 prefixEnd_8218723 1406718421720717647388429 := by
  unfold tailWord_8218723
  simp only [CollatzResearch.WordTrace]
  refine ⟨299761454203977691983532823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199840969469318461322355215 299761454203977691983532823)
  ·
    refine ⟨449642181305966537975299235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299761454203977691983532823 449642181305966537975299235)
    ·
      refine ⟨674463271958949806962948853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449642181305966537975299235 674463271958949806962948853)
      ·
        refine ⟨63230931746151544402776455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 674463271958949806962948853 63230931746151544402776455)
        ·
          refine ⟨94846397619227316604164683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63230931746151544402776455 94846397619227316604164683)
          ·
            refine ⟨142269596428840974906247025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94846397619227316604164683 142269596428840974906247025)
            ·
              refine ⟨106702197321630731179685269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142269596428840974906247025 106702197321630731179685269)
              ·
                refine ⟨5001665499451440524047747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106702197321630731179685269 5001665499451440524047747)
                ·
                  refine ⟨7502498249177160786071621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001665499451440524047747 7502498249177160786071621)
                  ·
                    refine ⟨1406718421720717647388429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7502498249177160786071621 1406718421720717647388429)
                    ·
                      rfl

theorem cell23_8218723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 4].length) (baseStart_8218723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218723 prefixEnd_8218723 := by exact prefixLift 8218723
  have htrace : WordTrace (prefixWord ++ tailWord_8218723) baseStart_8218723 baseEnd_8218723 := by
    simpa [prefixWord, tailWord_8218723, baseEnd_8218723] using wordTrace_append hprefix tailTrace_8218723
  have hstable : (prefixWord ++ tailWord_8218723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218723).length < 2 ^ (prefixWord ++ tailWord_8218723).sum := by decide
  have hdescent : baseEnd_8218723 < baseStart_8218723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218736 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 6]
def baseStart_8218736 : Nat := 118140960795 + 8218736 * 2 ^ 59
def prefixEnd_8218736 : Nat := 4983230072969 + 3 ^ 40 * 8218736 * 2
def baseEnd_8218736 : Nat := 468906882267851265700303

theorem tailTrace_8218736 : CollatzResearch.WordTrace tailWord_8218736 prefixEnd_8218736 468906882267851265700303 := by
  unfold tailWord_8218736
  simp only [CollatzResearch.WordTrace]
  refine ⟨149880964176465297601878031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199841285568620396802504041 149880964176465297601878031)
  ·
    refine ⟨224821446264697946402817047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149880964176465297601878031 224821446264697946402817047)
    ·
      refine ⟨337232169397046919604225571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224821446264697946402817047 337232169397046919604225571)
      ·
        refine ⟨505848254095570379406338357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337232169397046919604225571 505848254095570379406338357)
        ·
          refine ⟨47423273821459723069344221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 505848254095570379406338357 47423273821459723069344221)
          ·
            refine ⟨17783727683047396151004083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47423273821459723069344221 17783727683047396151004083)
            ·
              refine ⟨26675591524571094226506125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17783727683047396151004083 26675591524571094226506125)
              ·
                refine ⟨10003346821714160334939797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26675591524571094226506125 10003346821714160334939797)
                ·
                  refine ⟨468906882267851265700303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10003346821714160334939797 468906882267851265700303)
                  ·
                    rfl

theorem cell23_8218736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_8218736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218736 prefixEnd_8218736 := by exact prefixLift 8218736
  have htrace : WordTrace (prefixWord ++ tailWord_8218736) baseStart_8218736 baseEnd_8218736 := by
    simpa [prefixWord, tailWord_8218736, baseEnd_8218736] using wordTrace_append hprefix tailTrace_8218736
  have hstable : (prefixWord ++ tailWord_8218736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218736).length < 2 ^ (prefixWord ++ tailWord_8218736).sum := by decide
  have hdescent : baseEnd_8218736 < baseStart_8218736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218773 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_8218773 : Nat := 118140960795 + 8218773 * 2 ^ 59
def prefixEnd_8218773 : Nat := 4983230072969 + 3 ^ 40 * 8218773 * 2
def baseEnd_8218773 : Nat := 4220180939194877746540057

theorem tailTrace_8218773 : CollatzResearch.WordTrace tailWord_8218773 prefixEnd_8218773 4220180939194877746540057 := by
  unfold tailWord_8218773
  simp only [CollatzResearch.WordTrace]
  refine ⟨299763277853796550522852973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199842185235864367015235315 299763277853796550522852973)
  ·
    refine ⟨112411229195173706446069865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299763277853796550522852973 112411229195173706446069865)
    ·
      refine ⟨84308421896380279834552399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112411229195173706446069865 84308421896380279834552399)
      ·
        refine ⟨126462632844570419751828599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84308421896380279834552399 126462632844570419751828599)
        ·
          refine ⟨189693949266855629627742899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126462632844570419751828599 189693949266855629627742899)
          ·
            refine ⟨284540923900283444441614349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189693949266855629627742899 284540923900283444441614349)
            ·
              refine ⟨106702846462606291665605381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284540923900283444441614349 106702846462606291665605381)
              ·
                refine ⟨20006783711738679687301009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106702846462606291665605381 20006783711738679687301009)
                ·
                  refine ⟨15005087783804009765475757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20006783711738679687301009 15005087783804009765475757)
                  ·
                    refine ⟨5626907918926503662053409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15005087783804009765475757 5626907918926503662053409)
                    ·
                      refine ⟨4220180939194877746540057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626907918926503662053409 4220180939194877746540057)
                      ·
                        rfl

theorem cell23_8218773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_8218773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218773 prefixEnd_8218773 := by exact prefixLift 8218773
  have htrace : WordTrace (prefixWord ++ tailWord_8218773) baseStart_8218773 baseEnd_8218773 := by
    simpa [prefixWord, tailWord_8218773, baseEnd_8218773] using wordTrace_append hprefix tailTrace_8218773
  have hstable : (prefixWord ++ tailWord_8218773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218773).length < 2 ^ (prefixWord ++ tailWord_8218773).sum := by decide
  have hdescent : baseEnd_8218773 < baseStart_8218773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218779 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 3, 6]
def baseStart_8218779 : Nat := 118140960795 + 8218779 * 2 ^ 59
def prefixEnd_8218779 : Nat := 4983230072969 + 3 ^ 40 * 8218779 * 2
def baseEnd_8218779 : Nat := 1406728006692934907688343

theorem tailTrace_8218779 : CollatzResearch.WordTrace tailWord_8218779 prefixEnd_8218779 1406728006692934907688343 := by
  unfold tailWord_8218779
  simp only [CollatzResearch.WordTrace]
  refine ⟨299763496691774813547571391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199842331127849875698380927 299763496691774813547571391)
  ·
    refine ⟨449645245037662220321357087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299763496691774813547571391 449645245037662220321357087)
    ·
      refine ⟨674467867556493330482035631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449645245037662220321357087 674467867556493330482035631)
      ·
        refine ⟨1011701801334739995723053447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674467867556493330482035631 1011701801334739995723053447)
        ·
          refine ⟨1517552702002109993584580171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011701801334739995723053447 1517552702002109993584580171)
          ·
            refine ⟨2276329053003164990376870257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517552702002109993584580171 2276329053003164990376870257)
            ·
              refine ⟨1707246789752373742782652693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276329053003164990376870257 1707246789752373742782652693)
              ·
                refine ⟨80027193269642519192936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1707246789752373742782652693 80027193269642519192936845)
                ·
                  refine ⟨30010197476115944697351317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80027193269642519192936845 30010197476115944697351317)
                  ·
                    refine ⟨1406728006692934907688343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30010197476115944697351317 1406728006692934907688343)
                    ·
                      rfl

theorem cell23_8218779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_8218779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218779 prefixEnd_8218779 := by exact prefixLift 8218779
  have htrace : WordTrace (prefixWord ++ tailWord_8218779) baseStart_8218779 baseEnd_8218779 := by
    simpa [prefixWord, tailWord_8218779, baseEnd_8218779] using wordTrace_append hprefix tailTrace_8218779
  have hstable : (prefixWord ++ tailWord_8218779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218779).length < 2 ^ (prefixWord ++ tailWord_8218779).sum := by decide
  have hdescent : baseEnd_8218779 < baseStart_8218779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218814 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_8218814 : Nat := 118140960795 + 8218814 * 2 ^ 59
def prefixEnd_8218814 : Nat := 4983230072969 + 3 ^ 40 * 8218814 * 2
def baseEnd_8218814 : Nat := 4220201991901712086127369

theorem tailTrace_8218814 : CollatzResearch.WordTrace tailWord_8218814 prefixEnd_8218814 4220201991901712086127369 := by
  unfold tailWord_8218814
  simp only [CollatzResearch.WordTrace]
  refine ⟨37470596655831001815636937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199843182164432009683396997 37470596655831001815636937)
  ·
    refine ⟨28102947491873251361727703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37470596655831001815636937 28102947491873251361727703)
    ·
      refine ⟨42154421237809877042591555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28102947491873251361727703 42154421237809877042591555)
      ·
        refine ⟨63231631856714815563887333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42154421237809877042591555 63231631856714815563887333)
        ·
          refine ⟨11855930973134027918228875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63231631856714815563887333 11855930973134027918228875)
          ·
            refine ⟨17783896459701041877343313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855930973134027918228875 17783896459701041877343313)
            ·
              refine ⟨13337922344775781408007485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17783896459701041877343313 13337922344775781408007485)
              ·
                refine ⟨5001720879290918028002807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13337922344775781408007485 5001720879290918028002807)
                ·
                  refine ⟨7502581318936377042004211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001720879290918028002807 7502581318936377042004211)
                  ·
                    refine ⟨11253871978404565563006317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502581318936377042004211 11253871978404565563006317)
                    ·
                      refine ⟨4220201991901712086127369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11253871978404565563006317 4220201991901712086127369)
                      ·
                        rfl

theorem cell23_8218814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_8218814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218814 prefixEnd_8218814 := by exact prefixLift 8218814
  have htrace : WordTrace (prefixWord ++ tailWord_8218814) baseStart_8218814 baseEnd_8218814 := by
    simpa [prefixWord, tailWord_8218814, baseEnd_8218814] using wordTrace_append hprefix tailTrace_8218814
  have hstable : (prefixWord ++ tailWord_8218814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218814).length < 2 ^ (prefixWord ++ tailWord_8218814).sum := by decide
  have hdescent : baseEnd_8218814 < baseStart_8218814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218819 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_8218819 : Nat := 118140960795 + 8218819 * 2 ^ 59
def prefixEnd_8218819 : Nat := 4983230072969 + 3 ^ 40 * 8218819 * 2
def baseEnd_8218819 : Nat := 4220204559304984566564845

theorem tailTrace_8218819 : CollatzResearch.WordTrace tailWord_8218819 prefixEnd_8218819 4220204559304984566564845 := by
  unfold tailWord_8218819
  simp only [CollatzResearch.WordTrace]
  refine ⟨299764955611629900379027511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199843303741086600252685007 299764955611629900379027511)
  ·
    refine ⟨449647433417444850568541267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299764955611629900379027511 449647433417444850568541267)
    ·
      refine ⟨674471150126167275852811901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449647433417444850568541267 674471150126167275852811901)
      ·
        refine ⟨252926681297312728444804463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674471150126167275852811901 252926681297312728444804463)
        ·
          refine ⟨379390021945969092667206695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252926681297312728444804463 379390021945969092667206695)
          ·
            refine ⟨569085032918953639000810043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379390021945969092667206695 569085032918953639000810043)
            ·
              refine ⟨853627549378430458501215065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569085032918953639000810043 853627549378430458501215065)
              ·
                refine ⟨640220662033822843875911299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853627549378430458501215065 640220662033822843875911299)
                ·
                  refine ⟨960330993050734265813866949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640220662033822843875911299 960330993050734265813866949)
                  ·
                    refine ⟨180062061197012674840100053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 960330993050734265813866949 180062061197012674840100053)
                    ·
                      refine ⟨4220204559304984566564845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180062061197012674840100053 4220204559304984566564845)
                      ·
                        rfl

theorem cell23_8218819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_8218819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218819 prefixEnd_8218819 := by exact prefixLift 8218819
  have htrace : WordTrace (prefixWord ++ tailWord_8218819) baseStart_8218819 baseEnd_8218819 := by
    simpa [prefixWord, tailWord_8218819, baseEnd_8218819] using wordTrace_append hprefix tailTrace_8218819
  have hstable : (prefixWord ++ tailWord_8218819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218819).length < 2 ^ (prefixWord ++ tailWord_8218819).sum := by decide
  have hdescent : baseEnd_8218819 < baseStart_8218819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218820 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_8218820 : Nat := 118140960795 + 8218820 * 2 ^ 59
def prefixEnd_8218820 : Nat := 4983230072969 + 3 ^ 40 * 8218820 * 2
def baseEnd_8218820 : Nat := 4220205072785639062652341

theorem tailTrace_8218820 : CollatzResearch.WordTrace tailWord_8218820 prefixEnd_8218820 4220205072785639062652341 := by
  unfold tailWord_8218820
  simp only [CollatzResearch.WordTrace]
  refine ⟨149882496042313138774906957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199843328056417518366542609 149882496042313138774906957)
  ·
    refine ⟨56205936015867427040590109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149882496042313138774906957 56205936015867427040590109)
    ·
      refine ⟨21077226005950285140221291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56205936015867427040590109 21077226005950285140221291)
      ·
        refine ⟨31615839008925427710331937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21077226005950285140221291 31615839008925427710331937)
        ·
          refine ⟨23711879256694070782748953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31615839008925427710331937 23711879256694070782748953)
          ·
            refine ⟨17783909442520553087061715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23711879256694070782748953 17783909442520553087061715)
            ·
              refine ⟨26675864163780829630592573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17783909442520553087061715 26675864163780829630592573)
              ·
                refine ⟨10003449061417811111472215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26675864163780829630592573 10003449061417811111472215)
                ·
                  refine ⟨15005173592126716667208323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003449061417811111472215 15005173592126716667208323)
                  ·
                    refine ⟨22507760388190075000812485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15005173592126716667208323 22507760388190075000812485)
                    ·
                      refine ⟨4220205072785639062652341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22507760388190075000812485 4220205072785639062652341)
                      ·
                        rfl

theorem cell23_8218820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_8218820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218820 prefixEnd_8218820 := by exact prefixLift 8218820
  have htrace : WordTrace (prefixWord ++ tailWord_8218820) baseStart_8218820 baseEnd_8218820 := by
    simpa [prefixWord, tailWord_8218820, baseEnd_8218820] using wordTrace_append hprefix tailTrace_8218820
  have hstable : (prefixWord ++ tailWord_8218820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218820).length < 2 ^ (prefixWord ++ tailWord_8218820).sum := by decide
  have hdescent : baseEnd_8218820 < baseStart_8218820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218830 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_8218830 : Nat := 118140960795 + 8218830 * 2 ^ 59
def prefixEnd_8218830 : Nat := 4983230072969 + 3 ^ 40 * 8218830 * 2
def baseEnd_8218830 : Nat := 1406736735864061341175765

theorem tailTrace_8218830 : CollatzResearch.WordTrace tailWord_8218830 prefixEnd_8218830 1406736735864061341175765 := by
  unfold tailWord_8218830
  simp only [CollatzResearch.WordTrace]
  refine ⟨37470669601823756157209743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199843571209726699505118629 37470669601823756157209743)
  ·
    refine ⟨56206004402735634235814615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37470669601823756157209743 56206004402735634235814615)
    ·
      refine ⟨84309006604103451353721923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56206004402735634235814615 84309006604103451353721923)
      ·
        refine ⟨126463509906155177030582885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84309006604103451353721923 126463509906155177030582885)
        ·
          refine ⟨23711908107404095693234291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126463509906155177030582885 23711908107404095693234291)
          ·
            refine ⟨35567862161106143539851437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23711908107404095693234291 35567862161106143539851437)
            ·
              refine ⟨13337948310414803827444289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35567862161106143539851437 13337948310414803827444289)
              ·
                refine ⟨10003461232811102870583217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13337948310414803827444289 10003461232811102870583217)
                ·
                  refine ⟨7502595924608327152937413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10003461232811102870583217 7502595924608327152937413)
                  ·
                    refine ⟨1406736735864061341175765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7502595924608327152937413 1406736735864061341175765)
                    ·
                      rfl

theorem cell23_8218830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_8218830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218830 prefixEnd_8218830 := by exact prefixLift 8218830
  have htrace : WordTrace (prefixWord ++ tailWord_8218830) baseStart_8218830 baseEnd_8218830 := by
    simpa [prefixWord, tailWord_8218830, baseEnd_8218830] using wordTrace_append hprefix tailTrace_8218830
  have hstable : (prefixWord ++ tailWord_8218830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218830).length < 2 ^ (prefixWord ++ tailWord_8218830).sum := by decide
  have hdescent : baseEnd_8218830 < baseStart_8218830 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218870 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_8218870 : Nat := 118140960795 + 8218870 * 2 ^ 59
def prefixEnd_8218870 : Nat := 4983230072969 + 3 ^ 40 * 8218870 * 2
def baseEnd_8218870 : Nat := 4220230746818363867027111

theorem tailTrace_8218870 : CollatzResearch.WordTrace tailWord_8218870 prefixEnd_8218870 4220230746818363867027111 := by
  unfold tailWord_8218870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735425983402821005570879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199844543822963424059422709 18735425983402821005570879)
  ·
    refine ⟨28103138975104231508356319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18735425983402821005570879 28103138975104231508356319)
    ·
      refine ⟨42154708462656347262534479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28103138975104231508356319 42154708462656347262534479)
      ·
        refine ⟨63232062693984520893801719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42154708462656347262534479 63232062693984520893801719)
        ·
          refine ⟨94848094040976781340702579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63232062693984520893801719 94848094040976781340702579)
          ·
            refine ⟨142272141061465172011053869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94848094040976781340702579 142272141061465172011053869)
            ·
              refine ⟨53352052898049439504145201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142272141061465172011053869 53352052898049439504145201)
              ·
                refine ⟨40014039673537079628108901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53352052898049439504145201 40014039673537079628108901)
                ·
                  refine ⟨7502632438788202430270419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40014039673537079628108901 7502632438788202430270419)
                  ·
                    refine ⟨11253948658182303645405629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502632438788202430270419 11253948658182303645405629)
                    ·
                      refine ⟨4220230746818363867027111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11253948658182303645405629 4220230746818363867027111)
                      ·
                        rfl

theorem cell23_8218870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_8218870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218870 prefixEnd_8218870 := by exact prefixLift 8218870
  have htrace : WordTrace (prefixWord ++ tailWord_8218870) baseStart_8218870 baseEnd_8218870 := by
    simpa [prefixWord, tailWord_8218870, baseEnd_8218870] using wordTrace_append hprefix tailTrace_8218870
  have hstable : (prefixWord ++ tailWord_8218870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218870).length < 2 ^ (prefixWord ++ tailWord_8218870).sum := by decide
  have hdescent : baseEnd_8218870 < baseStart_8218870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218880 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 1, 3, 2]
def baseStart_8218880 : Nat := 118140960795 + 8218880 * 2 ^ 59
def prefixEnd_8218880 : Nat := 4983230072969 + 3 ^ 40 * 8218880 * 2
def baseEnd_8218880 : Nat := 4220235881624908827902065

theorem tailTrace_8218880 : CollatzResearch.WordTrace tailWord_8218880 prefixEnd_8218880 4220235881624908827902065 := by
  unfold tailWord_8218880
  simp only [CollatzResearch.WordTrace]
  refine ⟨149883590232204453898499047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199844786976272605197998729 149883590232204453898499047)
  ·
    refine ⟨224825385348306680847748571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149883590232204453898499047 224825385348306680847748571)
    ·
      refine ⟨337238078022460021271622857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224825385348306680847748571 337238078022460021271622857)
      ·
        refine ⟨252928558516845015953717143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337238078022460021271622857 252928558516845015953717143)
        ·
          refine ⟨379392837775267523930575715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252928558516845015953717143 379392837775267523930575715)
          ·
            refine ⟨569089256662901285895863573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379392837775267523930575715 569089256662901285895863573)
            ·
              refine ⟨26676058906073497776368605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 569089256662901285895863573 26676058906073497776368605)
              ·
                refine ⟨10003522089777561666138227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26676058906073497776368605 10003522089777561666138227)
                ·
                  refine ⟨15005283134666342499207341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003522089777561666138227 15005283134666342499207341)
                  ·
                    refine ⟨5626981175499878437202753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15005283134666342499207341 5626981175499878437202753)
                    ·
                      refine ⟨4220235881624908827902065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5626981175499878437202753 4220235881624908827902065)
                      ·
                        rfl

theorem cell23_8218880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_8218880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218880 prefixEnd_8218880 := by exact prefixLift 8218880
  have htrace : WordTrace (prefixWord ++ tailWord_8218880) baseStart_8218880 baseEnd_8218880 := by
    simpa [prefixWord, tailWord_8218880, baseEnd_8218880] using wordTrace_append hprefix tailTrace_8218880
  have hstable : (prefixWord ++ tailWord_8218880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218880).length < 2 ^ (prefixWord ++ tailWord_8218880).sum := by decide
  have hdescent : baseEnd_8218880 < baseStart_8218880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218914 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_8218914 : Nat := 118140960795 + 8218914 * 2 ^ 59
def prefixEnd_8218914 : Nat := 4983230072969 + 3 ^ 40 * 8218914 * 2
def baseEnd_8218914 : Nat := 4220253339967161694876909

theorem tailTrace_8218914 : CollatzResearch.WordTrace tailWord_8218914 prefixEnd_8218914 4220253339967161694876909 := by
  unfold tailWord_8218914
  simp only [CollatzResearch.WordTrace]
  refine ⟨74942105136571432900933949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199845613697523821069157197 74942105136571432900933949)
  ·
    refine ⟨28103289426214287337850231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74942105136571432900933949 28103289426214287337850231)
    ·
      refine ⟨42154934139321431006775347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28103289426214287337850231 42154934139321431006775347)
      ·
        refine ⟨63232401208982146510163021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42154934139321431006775347 63232401208982146510163021)
        ·
          refine ⟨23712150453368304941311133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63232401208982146510163021 23712150453368304941311133)
          ·
            refine ⟨8892056420013114352991675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23712150453368304941311133 8892056420013114352991675)
            ·
              refine ⟨13338084630019671529487513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892056420013114352991675 13338084630019671529487513)
              ·
                refine ⟨10003563472514753647115635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13338084630019671529487513 10003563472514753647115635)
                ·
                  refine ⟨15005345208772130470673453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003563472514753647115635 15005345208772130470673453)
                  ·
                    refine ⟨5627004453289548926502545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15005345208772130470673453 5627004453289548926502545)
                    ·
                      refine ⟨4220253339967161694876909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627004453289548926502545 4220253339967161694876909)
                      ·
                        rfl

theorem cell23_8218914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_8218914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218914 prefixEnd_8218914 := by exact prefixLift 8218914
  have htrace : WordTrace (prefixWord ++ tailWord_8218914) baseStart_8218914 baseEnd_8218914 := by
    simpa [prefixWord, tailWord_8218914, baseEnd_8218914] using wordTrace_append hprefix tailTrace_8218914
  have hstable : (prefixWord ++ tailWord_8218914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218914).length < 2 ^ (prefixWord ++ tailWord_8218914).sum := by decide
  have hdescent : baseEnd_8218914 < baseStart_8218914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218943 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_8218943 : Nat := 118140960795 + 8218943 * 2 ^ 59
def prefixEnd_8218943 : Nat := 4983230072969 + 3 ^ 40 * 8218943 * 2
def baseEnd_8218943 : Nat := 4220268230906142081414275

theorem tailTrace_8218943 : CollatzResearch.WordTrace tailWord_8218943 prefixEnd_8218943 4220268230906142081414275 := by
  unfold tailWord_8218943
  simp only [CollatzResearch.WordTrace]
  refine ⟨299769478263180669556541483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199846318842120446371027655 299769478263180669556541483)
  ·
    refine ⟨449654217394771004334812225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299769478263180669556541483 449654217394771004334812225)
    ·
      refine ⟨337240663046078253251109169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449654217394771004334812225 337240663046078253251109169)
      ·
        refine ⟨252930497284558689938331877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337240663046078253251109169 252930497284558689938331877)
        ·
          refine ⟨47424468240854754363437227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252930497284558689938331877 47424468240854754363437227)
          ·
            refine ⟨71136702361282131545155841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47424468240854754363437227 71136702361282131545155841)
            ·
              refine ⟨53352526770961598658866881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71136702361282131545155841 53352526770961598658866881)
              ·
                refine ⟨40014395078221198994150161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53352526770961598658866881 40014395078221198994150161)
                ·
                  refine ⟨30010796308665899245612621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40014395078221198994150161 30010796308665899245612621)
                  ·
                    refine ⟨11254048615749712217104733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30010796308665899245612621 11254048615749712217104733)
                    ·
                      refine ⟨4220268230906142081414275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11254048615749712217104733 4220268230906142081414275)
                      ·
                        rfl

theorem cell23_8218943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_8218943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218943 prefixEnd_8218943 := by exact prefixLift 8218943
  have htrace : WordTrace (prefixWord ++ tailWord_8218943) baseStart_8218943 baseEnd_8218943 := by
    simpa [prefixWord, tailWord_8218943, baseEnd_8218943] using wordTrace_append hprefix tailTrace_8218943
  have hstable : (prefixWord ++ tailWord_8218943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218943).length < 2 ^ (prefixWord ++ tailWord_8218943).sum := by decide
  have hdescent : baseEnd_8218943 < baseStart_8218943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8218993 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 7, 4]
def baseStart_8218993 : Nat := 118140960795 + 8218993 * 2 ^ 59
def prefixEnd_8218993 : Nat := 4983230072969 + 3 ^ 40 * 8218993 * 2
def baseEnd_8218993 : Nat := 1406764634979622295263015

theorem tailTrace_8218993 : CollatzResearch.WordTrace tailWord_8218993 prefixEnd_8218993 1406764634979622295263015 := by
  unfold tailWord_8218993
  simp only [CollatzResearch.WordTrace]
  refine ⟨299771301912999528095861633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199847534608666352063907755 299771301912999528095861633)
  ·
    refine ⟨224828476434749646071896225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299771301912999528095861633 224828476434749646071896225)
    ·
      refine ⟨168621357326062234553922169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224828476434749646071896225 168621357326062234553922169)
      ·
        refine ⟨126466017994546675915441627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168621357326062234553922169 126466017994546675915441627)
        ·
          refine ⟨189699026991820013873162441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126466017994546675915441627 189699026991820013873162441)
          ·
            refine ⟨142274270243865010404871831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189699026991820013873162441 142274270243865010404871831)
            ·
              refine ⟨213411405365797515607307747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142274270243865010404871831 213411405365797515607307747)
              ·
                refine ⟨320117108048696273410961621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213411405365797515607307747 320117108048696273410961621)
                ·
                  refine ⟨7502744719891318908069413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320117108048696273410961621 7502744719891318908069413)
                  ·
                    refine ⟨1406764634979622295263015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7502744719891318908069413 1406764634979622295263015)
                    ·
                      rfl

theorem cell23_8218993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_8218993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8218993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8218993 prefixEnd_8218993 := by exact prefixLift 8218993
  have htrace : WordTrace (prefixWord ++ tailWord_8218993) baseStart_8218993 baseEnd_8218993 := by
    simpa [prefixWord, tailWord_8218993, baseEnd_8218993] using wordTrace_append hprefix tailTrace_8218993
  have hstable : (prefixWord ++ tailWord_8218993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8218993).length < 2 ^ (prefixWord ++ tailWord_8218993).sum := by decide
  have hdescent : baseEnd_8218993 < baseStart_8218993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8218993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219033 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_8219033 : Nat := 118140960795 + 8219033 * 2 ^ 59
def prefixEnd_8219033 : Nat := 4983230072969 + 3 ^ 40 * 8219033 * 2
def baseEnd_8219033 : Nat := 4220314444165046729288861

theorem tailTrace_8219033 : CollatzResearch.WordTrace tailWord_8219033 prefixEnd_8219033 4220314444165046729288861 := by
  unfold tailWord_8219033
  simp only [CollatzResearch.WordTrace]
  refine ⟨299772760832854614927317753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199848507221903076618211835 299772760832854614927317753)
  ·
    refine ⟨224829570624640961195488315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299772760832854614927317753 224829570624640961195488315)
    ·
      refine ⟨337244355936961441793232473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224829570624640961195488315 337244355936961441793232473)
      ·
        refine ⟨252933266952721081344924355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337244355936961441793232473 252933266952721081344924355)
        ·
          refine ⟨379399900429081622017386533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252933266952721081344924355 379399900429081622017386533)
          ·
            refine ⟨71137481330452804128259975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379399900429081622017386533 71137481330452804128259975)
            ·
              refine ⟨106706221995679206192389963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71137481330452804128259975 106706221995679206192389963)
              ·
                refine ⟨160059332993518809288584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106706221995679206192389963 160059332993518809288584945)
                ·
                  refine ⟨120044499745139106966438709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160059332993518809288584945 120044499745139106966438709)
                  ·
                    refine ⟨11254171851106791278103629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120044499745139106966438709 11254171851106791278103629)
                    ·
                      refine ⟨4220314444165046729288861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11254171851106791278103629 4220314444165046729288861)
                      ·
                        rfl

theorem cell23_8219033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_8219033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219033 prefixEnd_8219033 := by exact prefixLift 8219033
  have htrace : WordTrace (prefixWord ++ tailWord_8219033) baseStart_8219033 baseEnd_8219033 := by
    simpa [prefixWord, tailWord_8219033, baseEnd_8219033] using wordTrace_append hprefix tailTrace_8219033
  have hstable : (prefixWord ++ tailWord_8219033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219033).length < 2 ^ (prefixWord ++ tailWord_8219033).sum := by decide
  have hdescent : baseEnd_8219033 < baseStart_8219033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219061 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_8219061 : Nat := 118140960795 + 8219061 * 2 ^ 59
def prefixEnd_8219061 : Nat := 4983230072969 + 3 ^ 40 * 8219061 * 2
def baseEnd_8219061 : Nat := 1406776273874457539912911

theorem tailTrace_8219061 : CollatzResearch.WordTrace tailWord_8219061 prefixEnd_8219061 1406776273874457539912911 := by
  unfold tailWord_8219061
  simp only [CollatzResearch.WordTrace]
  refine ⟨299773782076753175709337037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199849188051168783806224691 299773782076753175709337037)
  ·
    refine ⟨112415168278782440891001389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299773782076753175709337037 112415168278782440891001389)
    ·
      refine ⟨42155688104543415334125521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112415168278782440891001389 42155688104543415334125521)
      ·
        refine ⟨31616766078407561500594141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42155688104543415334125521 31616766078407561500594141)
        ·
          refine ⟨11856287279402835562722803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31616766078407561500594141 11856287279402835562722803)
          ·
            refine ⟨17784430919104253344084205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11856287279402835562722803 17784430919104253344084205)
            ·
              refine ⟨6669161594664095004031577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17784430919104253344084205 6669161594664095004031577)
              ·
                refine ⟨5001871195998071253023683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669161594664095004031577 5001871195998071253023683)
                ·
                  refine ⟨7502806793997106879535525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001871195998071253023683 7502806793997106879535525)
                  ·
                    refine ⟨1406776273874457539912911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7502806793997106879535525 1406776273874457539912911)
                    ·
                      rfl

theorem cell23_8219061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_8219061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219061 prefixEnd_8219061 := by exact prefixLift 8219061
  have htrace : WordTrace (prefixWord ++ tailWord_8219061) baseStart_8219061 baseEnd_8219061 := by
    simpa [prefixWord, tailWord_8219061, baseEnd_8219061] using wordTrace_append hprefix tailTrace_8219061
  have hstable : (prefixWord ++ tailWord_8219061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219061).length < 2 ^ (prefixWord ++ tailWord_8219061).sum := by decide
  have hdescent : baseEnd_8219061 < baseStart_8219061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219083 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 1, 6]
def baseStart_8219083 : Nat := 118140960795 + 8219083 * 2 ^ 59
def prefixEnd_8219083 : Nat := 4983230072969 + 3 ^ 40 * 8219083 * 2
def baseEnd_8219083 : Nat := 1406780039399257177887877

theorem tailTrace_8219083 : CollatzResearch.WordTrace tailWord_8219083 prefixEnd_8219083 1406780039399257177887877 := by
  unfold tailWord_8219083
  simp only [CollatzResearch.WordTrace]
  refine ⟨299774584482673473466637903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199849722988448982311091935 299774584482673473466637903)
  ·
    refine ⟨449661876724010210199956855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299774584482673473466637903 449661876724010210199956855)
    ·
      refine ⟨674492815086015315299935283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449661876724010210199956855 674492815086015315299935283)
      ·
        refine ⟨1011739222629022972949902925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674492815086015315299935283 1011739222629022972949902925)
        ·
          refine ⟨379402208485883614856213597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1011739222629022972949902925 379402208485883614856213597)
          ·
            refine ⟨142275828182206355571080099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379402208485883614856213597 142275828182206355571080099)
            ·
              refine ⟨213413742273309533356620149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142275828182206355571080099 213413742273309533356620149)
              ·
                refine ⟨20007538338122768752183139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213413742273309533356620149 20007538338122768752183139)
                ·
                  refine ⟨30011307507184153128274709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20007538338122768752183139 30011307507184153128274709)
                  ·
                    refine ⟨1406780039399257177887877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30011307507184153128274709 1406780039399257177887877)
                    ·
                      rfl

theorem cell23_8219083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 6].length) (baseStart_8219083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219083 prefixEnd_8219083 := by exact prefixLift 8219083
  have htrace : WordTrace (prefixWord ++ tailWord_8219083) baseStart_8219083 baseEnd_8219083 := by
    simpa [prefixWord, tailWord_8219083, baseEnd_8219083] using wordTrace_append hprefix tailTrace_8219083
  have hstable : (prefixWord ++ tailWord_8219083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219083).length < 2 ^ (prefixWord ++ tailWord_8219083).sum := by decide
  have hdescent : baseEnd_8219083 < baseStart_8219083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219118 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_8219118 : Nat := 118140960795 + 8219118 * 2 ^ 59
def prefixEnd_8219118 : Nat := 4983230072969 + 3 ^ 40 * 8219118 * 2
def baseEnd_8219118 : Nat := 4220358090020678896725971

theorem tailTrace_8219118 : CollatzResearch.WordTrace tailWord_8219118 prefixEnd_8219118 4220358090020678896725971 := by
  unfold tailWord_8219118
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471982629693334305520251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199850574025031116296108005 37471982629693334305520251)
  ·
    refine ⟨56207973944540001458280377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37471982629693334305520251 56207973944540001458280377)
    ·
      refine ⟨42155980458405001093710283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56207973944540001458280377 42155980458405001093710283)
      ·
        refine ⟨63233970687607501640565425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42155980458405001093710283 63233970687607501640565425)
        ·
          refine ⟨47425478015705626230424069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63233970687607501640565425 47425478015705626230424069)
          ·
            refine ⟨8892277127944804918204513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47425478015705626230424069 8892277127944804918204513)
            ·
              refine ⟨6669207845958603688653385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892277127944804918204513 6669207845958603688653385)
              ·
                refine ⟨5001905884468952766490039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669207845958603688653385 5001905884468952766490039)
                ·
                  refine ⟨7502858826703429149735059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001905884468952766490039 7502858826703429149735059)
                  ·
                    refine ⟨11254288240055143724602589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502858826703429149735059 11254288240055143724602589)
                    ·
                      refine ⟨4220358090020678896725971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11254288240055143724602589 4220358090020678896725971)
                      ·
                        rfl

theorem cell23_8219118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_8219118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219118 prefixEnd_8219118 := by exact prefixLift 8219118
  have htrace : WordTrace (prefixWord ++ tailWord_8219118) baseStart_8219118 baseEnd_8219118 := by
    simpa [prefixWord, tailWord_8219118, baseEnd_8219118] using wordTrace_append hprefix tailTrace_8219118
  have hstable : (prefixWord ++ tailWord_8219118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219118).length < 2 ^ (prefixWord ++ tailWord_8219118).sum := by decide
  have hdescent : baseEnd_8219118 < baseStart_8219118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219137 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_8219137 : Nat := 118140960795 + 8219137 * 2 ^ 59
def prefixEnd_8219137 : Nat := 4983230072969 + 3 ^ 40 * 8219137 * 2
def baseEnd_8219137 : Nat := 4220367846153114322388383

theorem tailTrace_8219137 : CollatzResearch.WordTrace tailWord_8219137 prefixEnd_8219137 4220367846153114322388383 := by
  unfold tailWord_8219137
  simp only [CollatzResearch.WordTrace]
  refine ⟨299776554024477840689103665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199851036016318560459402443 299776554024477840689103665)
  ·
    refine ⟨224832415518358380516827749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299776554024477840689103665 224832415518358380516827749)
    ·
      refine ⟨42156077909692196346905203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224832415518358380516827749 42156077909692196346905203)
      ·
        refine ⟨63234116864538294520357805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42156077909692196346905203 63234116864538294520357805)
        ·
          refine ⟨23712793824201860445134177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63234116864538294520357805 23712793824201860445134177)
          ·
            refine ⟨17784595368151395333850633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23712793824201860445134177 17784595368151395333850633)
            ·
              refine ⟨13338446526113546500387975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17784595368151395333850633 13338446526113546500387975)
              ·
                refine ⟨20007669789170319750581963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13338446526113546500387975 20007669789170319750581963)
                ·
                  refine ⟨30011504683755479625872945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20007669789170319750581963 30011504683755479625872945)
                  ·
                    refine ⟨22508628512816609719404709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30011504683755479625872945 22508628512816609719404709)
                    ·
                      refine ⟨4220367846153114322388383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22508628512816609719404709 4220367846153114322388383)
                      ·
                        rfl

theorem cell23_8219137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_8219137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219137 prefixEnd_8219137 := by exact prefixLift 8219137
  have htrace : WordTrace (prefixWord ++ tailWord_8219137) baseStart_8219137 baseEnd_8219137 := by
    simpa [prefixWord, tailWord_8219137, baseEnd_8219137] using wordTrace_append hprefix tailTrace_8219137
  have hstable : (prefixWord ++ tailWord_8219137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219137).length < 2 ^ (prefixWord ++ tailWord_8219137).sum := by decide
  have hdescent : baseEnd_8219137 < baseStart_8219137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219157 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_8219157 : Nat := 118140960795 + 8219157 * 2 ^ 59
def prefixEnd_8219157 : Nat := 4983230072969 + 3 ^ 40 * 8219157 * 2
def baseEnd_8219157 : Nat := 4220378115766204244138291

theorem tailTrace_8219157 : CollatzResearch.WordTrace tailWord_8219157 prefixEnd_8219157 4220378115766204244138291 := by
  unfold tailWord_8219157
  simp only [CollatzResearch.WordTrace]
  refine ⟨299777283484405384104831725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199851522322936922736554483 299777283484405384104831725)
  ·
    refine ⟨112416481306652019039311897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299777283484405384104831725 112416481306652019039311897)
    ·
      refine ⟨84312360979989014279483923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112416481306652019039311897 84312360979989014279483923)
      ·
        refine ⟨126468541469983521419225885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84312360979989014279483923 126468541469983521419225885)
        ·
          refine ⟨47425703051243820532209707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126468541469983521419225885 47425703051243820532209707)
          ·
            refine ⟨71138554576865730798314561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47425703051243820532209707 71138554576865730798314561)
            ·
              refine ⟨53353915932649298098735921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71138554576865730798314561 53353915932649298098735921)
              ·
                refine ⟨40015436949486973574051941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53353915932649298098735921 40015436949486973574051941)
                ·
                  refine ⟨7502894428028807545134739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40015436949486973574051941 7502894428028807545134739)
                  ·
                    refine ⟨11254341642043211317702109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502894428028807545134739 11254341642043211317702109)
                    ·
                      refine ⟨4220378115766204244138291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11254341642043211317702109 4220378115766204244138291)
                      ·
                        rfl

theorem cell23_8219157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_8219157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219157 prefixEnd_8219157 := by exact prefixLift 8219157
  have htrace : WordTrace (prefixWord ++ tailWord_8219157) baseStart_8219157 baseEnd_8219157 := by
    simpa [prefixWord, tailWord_8219157, baseEnd_8219157] using wordTrace_append hprefix tailTrace_8219157
  have hstable : (prefixWord ++ tailWord_8219157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219157).length < 2 ^ (prefixWord ++ tailWord_8219157).sum := by decide
  have hdescent : baseEnd_8219157 < baseStart_8219157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219188 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_8219188 : Nat := 118140960795 + 8219188 * 2 ^ 59
def prefixEnd_8219188 : Nat := 4983230072969 + 3 ^ 40 * 8219188 * 2
def baseEnd_8219188 : Nat := 4220394033666493622850649

theorem tailTrace_8219188 : CollatzResearch.WordTrace tailWord_8219188 prefixEnd_8219188 4220394033666493622850649 := by
  unfold tailWord_8219188
  simp only [CollatzResearch.WordTrace]
  refine ⟨149889207073646538199605109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199852276098195384266140145 149889207073646538199605109)
  ·
    refine ⟨14052113163154362956212979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149889207073646538199605109 14052113163154362956212979)
    ·
      refine ⟨21078169744731544434319469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14052113163154362956212979 21078169744731544434319469)
      ·
        refine ⟨7904313654274329162869801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21078169744731544434319469 7904313654274329162869801)
        ·
          refine ⟨5928235240705746872152351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7904313654274329162869801 5928235240705746872152351)
          ·
            refine ⟨8892352861058620308228527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5928235240705746872152351 8892352861058620308228527)
            ·
              refine ⟨13338529291587930462342791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892352861058620308228527 13338529291587930462342791)
              ·
                refine ⟨20007793937381895693514187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13338529291587930462342791 20007793937381895693514187)
                ·
                  refine ⟨30011690906072843540271281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20007793937381895693514187 30011690906072843540271281)
                  ·
                    refine ⟨22508768179554632655203461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30011690906072843540271281 22508768179554632655203461)
                    ·
                      refine ⟨4220394033666493622850649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22508768179554632655203461 4220394033666493622850649)
                      ·
                        rfl

theorem cell23_8219188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_8219188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219188 prefixEnd_8219188 := by exact prefixLift 8219188
  have htrace : WordTrace (prefixWord ++ tailWord_8219188) baseStart_8219188 baseEnd_8219188 := by
    simpa [prefixWord, tailWord_8219188, baseEnd_8219188] using wordTrace_append hprefix tailTrace_8219188
  have hstable : (prefixWord ++ tailWord_8219188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219188).length < 2 ^ (prefixWord ++ tailWord_8219188).sum := by decide
  have hdescent : baseEnd_8219188 < baseStart_8219188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219200 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_8219200 : Nat := 118140960795 + 8219200 * 2 ^ 59
def prefixEnd_8219200 : Nat := 4983230072969 + 3 ^ 40 * 8219200 * 2
def baseEnd_8219200 : Nat := 4220400195434347575900593

theorem tailTrace_8219200 : CollatzResearch.WordTrace tailWord_8219200 prefixEnd_8219200 4220400195434347575900593 := by
  unfold tailWord_8219200
  simp only [CollatzResearch.WordTrace]
  refine ⟨149889425911624801224323527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199852567882166401632431369 149889425911624801224323527)
  ·
    refine ⟨224834138867437201836485291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149889425911624801224323527 224834138867437201836485291)
    ·
      refine ⟨337251208301155802754727937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224834138867437201836485291 337251208301155802754727937)
      ·
        refine ⟨252938406225866852066045953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337251208301155802754727937 252938406225866852066045953)
        ·
          refine ⟨189703804669400139049534465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252938406225866852066045953 189703804669400139049534465)
          ·
            refine ⟨142277853502050104287150849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189703804669400139049534465 142277853502050104287150849)
            ·
              refine ⟨106708390126537578215363137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142277853502050104287150849 106708390126537578215363137)
              ·
                refine ⟨80031292594903183661522353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106708390126537578215363137 80031292594903183661522353)
                ·
                  refine ⟨60023469446177387746141765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80031292594903183661522353 60023469446177387746141765)
                  ·
                    refine ⟨11254400521158260202401581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60023469446177387746141765 11254400521158260202401581)
                    ·
                      refine ⟨4220400195434347575900593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11254400521158260202401581 4220400195434347575900593)
                      ·
                        rfl

theorem cell23_8219200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_8219200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219200 prefixEnd_8219200 := by exact prefixLift 8219200
  have htrace : WordTrace (prefixWord ++ tailWord_8219200) baseStart_8219200 baseEnd_8219200 := by
    simpa [prefixWord, tailWord_8219200, baseEnd_8219200] using wordTrace_append hprefix tailTrace_8219200
  have hstable : (prefixWord ++ tailWord_8219200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219200).length < 2 ^ (prefixWord ++ tailWord_8219200).sum := by decide
  have hdescent : baseEnd_8219200 < baseStart_8219200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219201 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_8219201 : Nat := 118140960795 + 8219201 * 2 ^ 59
def prefixEnd_8219201 : Nat := 4983230072969 + 3 ^ 40 * 8219201 * 2
def baseEnd_8219201 : Nat := 4220400708915002071988089

theorem tailTrace_8219201 : CollatzResearch.WordTrace tailWord_8219201 prefixEnd_8219201 4220400708915002071988089 := by
  unfold tailWord_8219201
  simp only [CollatzResearch.WordTrace]
  refine ⟨299778888296245979619433457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199852592197497319746288971 299778888296245979619433457)
  ·
    refine ⟨224834166222184484714575093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299778888296245979619433457 224834166222184484714575093)
    ·
      refine ⟨21078203083329795441991415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224834166222184484714575093 21078203083329795441991415)
      ·
        refine ⟨31617304624994693162987123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21078203083329795441991415 31617304624994693162987123)
        ·
          refine ⟨47425956937492039744480685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31617304624994693162987123 47425956937492039744480685)
          ·
            refine ⟨17784733851559514904180257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47425956937492039744480685 17784733851559514904180257)
            ·
              refine ⟨13338550388669636178135193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17784733851559514904180257 13338550388669636178135193)
              ·
                refine ⟨10003912791502227133601395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13338550388669636178135193 10003912791502227133601395)
                ·
                  refine ⟨15005869187253340700402093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003912791502227133601395 15005869187253340700402093)
                  ·
                    refine ⟨5627200945220002762650785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15005869187253340700402093 5627200945220002762650785)
                    ·
                      refine ⟨4220400708915002071988089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627200945220002762650785 4220400708915002071988089)
                      ·
                        rfl

theorem cell23_8219201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_8219201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219201 prefixEnd_8219201 := by exact prefixLift 8219201
  have htrace : WordTrace (prefixWord ++ tailWord_8219201) baseStart_8219201 baseEnd_8219201 := by
    simpa [prefixWord, tailWord_8219201, baseEnd_8219201] using wordTrace_append hprefix tailTrace_8219201
  have hstable : (prefixWord ++ tailWord_8219201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219201).length < 2 ^ (prefixWord ++ tailWord_8219201).sum := by decide
  have hdescent : baseEnd_8219201 < baseStart_8219201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219214 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_8219214 : Nat := 118140960795 + 8219214 * 2 ^ 59
def prefixEnd_8219214 : Nat := 4983230072969 + 3 ^ 40 * 8219214 * 2
def baseEnd_8219214 : Nat := 4220407384163510521125529

theorem tailTrace_8219214 : CollatzResearch.WordTrace tailWord_8219214 prefixEnd_8219214 4220407384163510521125529 := by
  unfold tailWord_8219214
  simp only [CollatzResearch.WordTrace]
  refine ⟨37472420305649860354957087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199852908296799255226437797 37472420305649860354957087)
  ·
    refine ⟨56208630458474790532435631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37472420305649860354957087 56208630458474790532435631)
    ·
      refine ⟨84312945687712185798653447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56208630458474790532435631 84312945687712185798653447)
      ·
        refine ⟨126469418531568278697980171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84312945687712185798653447 126469418531568278697980171)
        ·
          refine ⟨189704127797352418046970257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126469418531568278697980171 189704127797352418046970257)
          ·
            refine ⟨142278095848014313535227693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189704127797352418046970257 142278095848014313535227693)
            ·
              refine ⟨53354285943005367575710385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142278095848014313535227693 53354285943005367575710385)
              ·
                refine ⟨40015714457254025681782789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53354285943005367575710385 40015714457254025681782789)
                ·
                  refine ⟨7502946460735129815334273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40015714457254025681782789 7502946460735129815334273)
                  ·
                    refine ⟨5627209845551347361500705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502946460735129815334273 5627209845551347361500705)
                    ·
                      refine ⟨4220407384163510521125529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627209845551347361500705 4220407384163510521125529)
                      ·
                        rfl

theorem cell23_8219214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_8219214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219214 prefixEnd_8219214 := by exact prefixLift 8219214
  have htrace : WordTrace (prefixWord ++ tailWord_8219214) baseStart_8219214 baseEnd_8219214 := by
    simpa [prefixWord, tailWord_8219214, baseEnd_8219214] using wordTrace_append hprefix tailTrace_8219214
  have hstable : (prefixWord ++ tailWord_8219214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219214).length < 2 ^ (prefixWord ++ tailWord_8219214).sum := by decide
  have hdescent : baseEnd_8219214 < baseStart_8219214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219284 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_8219284 : Nat := 118140960795 + 8219284 * 2 ^ 59
def prefixEnd_8219284 : Nat := 4983230072969 + 3 ^ 40 * 8219284 * 2
def baseEnd_8219284 : Nat := 1406814442603108415750069

theorem tailTrace_8219284 : CollatzResearch.WordTrace tailWord_8219284 prefixEnd_8219284 1406814442603108415750069 := by
  unfold tailWord_8219284
  simp only [CollatzResearch.WordTrace]
  refine ⟨149890957777472642397352453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199854610369963523196469937 149890957777472642397352453)
  ·
    refine ⟨28104554583276120449503585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149890957777472642397352453 28104554583276120449503585)
    ·
      refine ⟨21078415937457090337127689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28104554583276120449503585 21078415937457090337127689)
      ·
        refine ⟨15808811953092817752845767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21078415937457090337127689 15808811953092817752845767)
        ·
          refine ⟨23713217929639226629268651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15808811953092817752845767 23713217929639226629268651)
          ·
            refine ⟨35569826894458839943902977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23713217929639226629268651 35569826894458839943902977)
            ·
              refine ⟨26677370170844129957927233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35569826894458839943902977 26677370170844129957927233)
              ·
                refine ⟨20008027628133097468445425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26677370170844129957927233 20008027628133097468445425)
                ·
                  refine ⟨15006020721099823101334069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20008027628133097468445425 15006020721099823101334069)
                  ·
                    refine ⟨1406814442603108415750069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15006020721099823101334069 1406814442603108415750069)
                    ·
                      rfl

theorem cell23_8219284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_8219284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219284 prefixEnd_8219284 := by exact prefixLift 8219284
  have htrace : WordTrace (prefixWord ++ tailWord_8219284) baseStart_8219284 baseEnd_8219284 := by
    simpa [prefixWord, tailWord_8219284, baseEnd_8219284] using wordTrace_append hprefix tailTrace_8219284
  have hstable : (prefixWord ++ tailWord_8219284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219284).length < 2 ^ (prefixWord ++ tailWord_8219284).sum := by decide
  have hdescent : baseEnd_8219284 < baseStart_8219284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219287 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_8219287 : Nat := 118140960795 + 8219287 * 2 ^ 59
def prefixEnd_8219287 : Nat := 4983230072969 + 3 ^ 40 * 8219287 * 2
def baseEnd_8219287 : Nat := 4220444868251288735512693

theorem tailTrace_8219287 : CollatzResearch.WordTrace tailWord_8219287 prefixEnd_8219287 4220444868251288735512693 := by
  unfold tailWord_8219287
  simp only [CollatzResearch.WordTrace]
  refine ⟨299782024973934416307064115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199854683315956277538042743 299782024973934416307064115)
  ·
    refine ⟨449673037460901624460596173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299782024973934416307064115 449673037460901624460596173)
    ·
      refine ⟨168627389047838109172723565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449673037460901624460596173 168627389047838109172723565)
      ·
        refine ⟨63235270892939290939771337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168627389047838109172723565 63235270892939290939771337)
        ·
          refine ⟨47426453169704468204828503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63235270892939290939771337 47426453169704468204828503)
          ·
            refine ⟨71139679754556702307242755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47426453169704468204828503 71139679754556702307242755)
            ·
              refine ⟨106709519631835053460864133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71139679754556702307242755 106709519631835053460864133)
              ·
                refine ⟨20008034930969072523912025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106709519631835053460864133 20008034930969072523912025)
                ·
                  refine ⟨15006026198226804392934019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20008034930969072523912025 15006026198226804392934019)
                  ·
                    refine ⟨22509039297340206589401029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15006026198226804392934019 22509039297340206589401029)
                    ·
                      refine ⟨4220444868251288735512693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22509039297340206589401029 4220444868251288735512693)
                      ·
                        rfl

theorem cell23_8219287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_8219287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219287 prefixEnd_8219287 := by exact prefixLift 8219287
  have htrace : WordTrace (prefixWord ++ tailWord_8219287) baseStart_8219287 baseEnd_8219287 := by
    simpa [prefixWord, tailWord_8219287, baseEnd_8219287] using wordTrace_append hprefix tailTrace_8219287
  have hstable : (prefixWord ++ tailWord_8219287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219287).length < 2 ^ (prefixWord ++ tailWord_8219287).sum := by decide
  have hdescent : baseEnd_8219287 < baseStart_8219287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219318 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_8219318 : Nat := 118140960795 + 8219318 * 2 ^ 59
def prefixEnd_8219318 : Nat := 4983230072969 + 3 ^ 40 * 8219318 * 2
def baseEnd_8219318 : Nat := 1406820262050526038075017

theorem tailTrace_8219318 : CollatzResearch.WordTrace tailWord_8219318 prefixEnd_8219318 1406820262050526038075017 := by
  unfold tailWord_8219318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736447227301381787590163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199855437091214739067628405 18736447227301381787590163)
  ·
    refine ⟨28104670840952072681385245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18736447227301381787590163 28104670840952072681385245)
    ·
      refine ⟨10539251565357027255519467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28104670840952072681385245 10539251565357027255519467)
      ·
        refine ⟨15808877348035540883279201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10539251565357027255519467 15808877348035540883279201)
        ·
          refine ⟨11856658011026655662459401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15808877348035540883279201 11856658011026655662459401)
          ·
            refine ⟨8892493508269991746844551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11856658011026655662459401 8892493508269991746844551)
            ·
              refine ⟨13338740262404987620266827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892493508269991746844551 13338740262404987620266827)
              ·
                refine ⟨20008110393607481430400241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13338740262404987620266827 20008110393607481430400241)
                ·
                  refine ⟨15006082795205611072800181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20008110393607481430400241 15006082795205611072800181)
                  ·
                    refine ⟨1406820262050526038075017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15006082795205611072800181 1406820262050526038075017)
                    ·
                      rfl

theorem cell23_8219318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_8219318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219318 prefixEnd_8219318 := by exact prefixLift 8219318
  have htrace : WordTrace (prefixWord ++ tailWord_8219318) baseStart_8219318 baseEnd_8219318 := by
    simpa [prefixWord, tailWord_8219318, baseEnd_8219318] using wordTrace_append hprefix tailTrace_8219318
  have hstable : (prefixWord ++ tailWord_8219318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219318).length < 2 ^ (prefixWord ++ tailWord_8219318).sum := by decide
  have hdescent : baseEnd_8219318 < baseStart_8219318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219364 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_8219364 : Nat := 118140960795 + 8219364 * 2 ^ 59
def prefixEnd_8219364 : Nat := 4983230072969 + 3 ^ 40 * 8219364 * 2
def baseEnd_8219364 : Nat := 4220484406261684934249839

theorem tailTrace_8219364 : CollatzResearch.WordTrace tailWord_8219364 prefixEnd_8219364 4220484406261684934249839 := by
  unfold tailWord_8219364
  simp only [CollatzResearch.WordTrace]
  refine ⟨149892416697327729228808573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199856555596436972305078097 149892416697327729228808573)
  ·
    refine ⟨56209656261497898460803215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149892416697327729228808573 56209656261497898460803215)
    ·
      refine ⟨84314484392246847691204823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56209656261497898460803215 84314484392246847691204823)
      ·
        refine ⟨126471726588370271536807235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84314484392246847691204823 126471726588370271536807235)
        ·
          refine ⟨189707589882555407305210853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126471726588370271536807235 189707589882555407305210853)
          ·
            refine ⟨35570173102979138869727035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189707589882555407305210853 35570173102979138869727035)
            ·
              refine ⟨53355259654468708304590553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35570173102979138869727035 53355259654468708304590553)
              ·
                refine ⟨40016444740851531228442915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53355259654468708304590553 40016444740851531228442915)
                ·
                  refine ⟨60024667111277296842664373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40016444740851531228442915 60024667111277296842664373)
                  ·
                    refine ⟨5627312541682246578999785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60024667111277296842664373 5627312541682246578999785)
                    ·
                      refine ⟨4220484406261684934249839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627312541682246578999785 4220484406261684934249839)
                      ·
                        rfl

theorem cell23_8219364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_8219364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219364 prefixEnd_8219364 := by exact prefixLift 8219364
  have htrace : WordTrace (prefixWord ++ tailWord_8219364) baseStart_8219364 baseEnd_8219364 := by
    simpa [prefixWord, tailWord_8219364, baseEnd_8219364] using wordTrace_append hprefix tailTrace_8219364
  have hstable : (prefixWord ++ tailWord_8219364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219364).length < 2 ^ (prefixWord ++ tailWord_8219364).sum := by decide
  have hdescent : baseEnd_8219364 < baseStart_8219364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219374 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_8219374 : Nat := 118140960795 + 8219374 * 2 ^ 59
def prefixEnd_8219374 : Nat := 4983230072969 + 3 ^ 40 * 8219374 * 2
def baseEnd_8219374 : Nat := 1406829847022743298374931

theorem tailTrace_8219374 : CollatzResearch.WordTrace tailWord_8219374 prefixEnd_8219374 1406829847022743298374931 := by
  unfold tailWord_8219374
  simp only [CollatzResearch.WordTrace]
  refine ⟨37473149765577403770685147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199856798749746153443654117 37473149765577403770685147)
  ·
    refine ⟨56209724648366105656027721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37473149765577403770685147 56209724648366105656027721)
    ·
      refine ⟨42157293486274579242020791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56209724648366105656027721 42157293486274579242020791)
      ·
        refine ⟨63235940229411868863031187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42157293486274579242020791 63235940229411868863031187)
        ·
          refine ⟨94853910344117803294546781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63235940229411868863031187 94853910344117803294546781)
          ·
            refine ⟨35570216379044176235455043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94853910344117803294546781 35570216379044176235455043)
            ·
              refine ⟨53355324568566264353182565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35570216379044176235455043 53355324568566264353182565)
              ·
                refine ⟨10004123356606174566221731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53355324568566264353182565 10004123356606174566221731)
                ·
                  refine ⟨15006185034909261849332597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004123356606174566221731 15006185034909261849332597)
                  ·
                    refine ⟨1406829847022743298374931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15006185034909261849332597 1406829847022743298374931)
                    ·
                      rfl

theorem cell23_8219374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_8219374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219374 prefixEnd_8219374 := by exact prefixLift 8219374
  have htrace : WordTrace (prefixWord ++ tailWord_8219374) baseStart_8219374 baseEnd_8219374 := by
    simpa [prefixWord, tailWord_8219374, baseEnd_8219374] using wordTrace_append hprefix tailTrace_8219374
  have hstable : (prefixWord ++ tailWord_8219374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219374).length < 2 ^ (prefixWord ++ tailWord_8219374).sum := by decide
  have hdescent : baseEnd_8219374 < baseStart_8219374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219388 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_8219388 : Nat := 118140960795 + 8219388 * 2 ^ 59
def prefixEnd_8219388 : Nat := 4983230072969 + 3 ^ 40 * 8219388 * 2
def baseEnd_8219388 : Nat := 4220496729797392840349729

theorem tailTrace_8219388 : CollatzResearch.WordTrace tailWord_8219388 prefixEnd_8219388 4220496729797392840349729 := by
  unfold tailWord_8219388
  simp only [CollatzResearch.WordTrace]
  refine ⟨149892854373284255278245409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199857139164379007037660545 149892854373284255278245409)
  ·
    refine ⟨112419640779963191458684057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149892854373284255278245409 112419640779963191458684057)
    ·
      refine ⟨84314730584972393594013043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112419640779963191458684057 84314730584972393594013043)
      ·
        refine ⟨126472095877458590391019565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84314730584972393594013043 126472095877458590391019565)
        ·
          refine ⟨47427035954046971396632337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126472095877458590391019565 47427035954046971396632337)
          ·
            refine ⟨35570276965535228547474253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47427035954046971396632337 35570276965535228547474253)
            ·
              refine ⟨13338853862075710705302845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35570276965535228547474253 13338853862075710705302845)
              ·
                refine ⟨5002070198278391514488567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13338853862075710705302845 5002070198278391514488567)
                ·
                  refine ⟨7503105297417587271732851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002070198278391514488567 7503105297417587271732851)
                  ·
                    refine ⟨11254657946126380907599277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7503105297417587271732851 11254657946126380907599277)
                    ·
                      refine ⟨4220496729797392840349729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11254657946126380907599277 4220496729797392840349729)
                      ·
                        rfl

theorem cell23_8219388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_8219388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219388 prefixEnd_8219388 := by exact prefixLift 8219388
  have htrace : WordTrace (prefixWord ++ tailWord_8219388) baseStart_8219388 baseEnd_8219388 := by
    simpa [prefixWord, tailWord_8219388, baseEnd_8219388] using wordTrace_append hprefix tailTrace_8219388
  have hstable : (prefixWord ++ tailWord_8219388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219388).length < 2 ^ (prefixWord ++ tailWord_8219388).sum := by decide
  have hdescent : baseEnd_8219388 < baseStart_8219388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219404 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_8219404 : Nat := 118140960795 + 8219404 * 2 ^ 59
def prefixEnd_8219404 : Nat := 4983230072969 + 3 ^ 40 * 8219404 * 2
def baseEnd_8219404 : Nat := 1406834981829288259249885

theorem tailTrace_8219404 : CollatzResearch.WordTrace tailWord_8219404 prefixEnd_8219404 1406834981829288259249885 := by
  unfold tailWord_8219404
  simp only [CollatzResearch.WordTrace]
  refine ⟨149893146157255272644536633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199857528209673696859382177 149893146157255272644536633)
  ·
    refine ⟨112419859617941454483402475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149893146157255272644536633 112419859617941454483402475)
    ·
      refine ⟨168629789426912181725103713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112419859617941454483402475 168629789426912181725103713)
      ·
        refine ⟨126472342070184136293827785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168629789426912181725103713 126472342070184136293827785)
        ·
          refine ⟨94854256552638102220370839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126472342070184136293827785 94854256552638102220370839)
          ·
            refine ⟨142281384828957153330556259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94854256552638102220370839 142281384828957153330556259)
            ·
              refine ⟨213422077243435729995834389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142281384828957153330556259 213422077243435729995834389)
              ·
                refine ⟨10004159870786049843554737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213422077243435729995834389 10004159870786049843554737)
                ·
                  refine ⟨7503119903089537382666053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10004159870786049843554737 7503119903089537382666053)
                  ·
                    refine ⟨1406834981829288259249885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503119903089537382666053 1406834981829288259249885)
                    ·
                      rfl

theorem cell23_8219404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_8219404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219404 prefixEnd_8219404 := by exact prefixLift 8219404
  have htrace : WordTrace (prefixWord ++ tailWord_8219404) baseStart_8219404 baseEnd_8219404 := by
    simpa [prefixWord, tailWord_8219404, baseEnd_8219404] using wordTrace_append hprefix tailTrace_8219404
  have hstable : (prefixWord ++ tailWord_8219404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219404).length < 2 ^ (prefixWord ++ tailWord_8219404).sum := by decide
  have hdescent : baseEnd_8219404 < baseStart_8219404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219428 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_8219428 : Nat := 118140960795 + 8219428 * 2 ^ 59
def prefixEnd_8219428 : Nat := 4983230072969 + 3 ^ 40 * 8219428 * 2
def baseEnd_8219428 : Nat := 4220517269023572683849545

theorem tailTrace_8219428 : CollatzResearch.WordTrace tailWord_8219428 prefixEnd_8219428 4220517269023572683849545 := by
  unfold tailWord_8219428
  simp only [CollatzResearch.WordTrace]
  refine ⟨149893583833211798693973469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199858111777615731591964625 149893583833211798693973469)
  ·
    refine ⟨56210093937454424510240051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149893583833211798693973469 56210093937454424510240051)
    ·
      refine ⟨84315140906181636765360077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56210093937454424510240051 84315140906181636765360077)
      ·
        refine ⟨31618177839818113787010029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84315140906181636765360077 31618177839818113787010029)
        ·
          refine ⟨11856816689931792670128761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31618177839818113787010029 11856816689931792670128761)
          ·
            refine ⟨8892612517448844502596571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11856816689931792670128761 8892612517448844502596571)
            ·
              refine ⟨13338918776173266753894857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892612517448844502596571 13338918776173266753894857)
              ·
                refine ⟨10004189082129950065421143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13338918776173266753894857 10004189082129950065421143)
                ·
                  refine ⟨15006283623194925098131715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004189082129950065421143 15006283623194925098131715)
                  ·
                    refine ⟨22509425434792387647197573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15006283623194925098131715 22509425434792387647197573)
                    ·
                      refine ⟨4220517269023572683849545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22509425434792387647197573 4220517269023572683849545)
                      ·
                        rfl

theorem cell23_8219428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_8219428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219428 prefixEnd_8219428 := by exact prefixLift 8219428
  have htrace : WordTrace (prefixWord ++ tailWord_8219428) baseStart_8219428 baseEnd_8219428 := by
    simpa [prefixWord, tailWord_8219428, baseEnd_8219428] using wordTrace_append hprefix tailTrace_8219428
  have hstable : (prefixWord ++ tailWord_8219428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219428).length < 2 ^ (prefixWord ++ tailWord_8219428).sum := by decide
  have hdescent : baseEnd_8219428 < baseStart_8219428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219505 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 1, 3, 2]
def baseStart_8219505 : Nat := 118140960795 + 8219505 * 2 ^ 59
def prefixEnd_8219505 : Nat := 4983230072969 + 3 ^ 40 * 8219505 * 2
def baseEnd_8219505 : Nat := 4220556807033968882586691

theorem tailTrace_8219505 : CollatzResearch.WordTrace tailWord_8219505 prefixEnd_8219505 4220556807033968882586691 := by
  unfold tailWord_8219505
  simp only [CollatzResearch.WordTrace]
  refine ⟨299789976087144639538499969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199859984058096426358999979 299789976087144639538499969)
  ·
    refine ⟨224842482065358479653874977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299789976087144639538499969 224842482065358479653874977)
    ·
      refine ⟨168631861549018859740406233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224842482065358479653874977 168631861549018859740406233)
      ·
        refine ⟨126473896161764144805304675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168631861549018859740406233 126473896161764144805304675)
        ·
          refine ⟨189710844242646217207957013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126473896161764144805304675 189710844242646217207957013)
          ·
            refine ⟨8892695823874041431622985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189710844242646217207957013 8892695823874041431622985)
            ·
              refine ⟨6669521867905531073717239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892695823874041431622985 6669521867905531073717239)
              ·
                refine ⟨10004282801858296610575859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669521867905531073717239 10004282801858296610575859)
                ·
                  refine ⟨15006424202787444915863789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004282801858296610575859 15006424202787444915863789)
                  ·
                    refine ⟨5627409076045291843448921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15006424202787444915863789 5627409076045291843448921)
                    ·
                      refine ⟨4220556807033968882586691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627409076045291843448921 4220556807033968882586691)
                      ·
                        rfl

theorem cell23_8219505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_8219505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219505 prefixEnd_8219505 := by exact prefixLift 8219505
  have htrace : WordTrace (prefixWord ++ tailWord_8219505) baseStart_8219505 baseEnd_8219505 := by
    simpa [prefixWord, tailWord_8219505, baseEnd_8219505] using wordTrace_append hprefix tailTrace_8219505
  have hstable : (prefixWord ++ tailWord_8219505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219505).length < 2 ^ (prefixWord ++ tailWord_8219505).sum := by decide
  have hdescent : baseEnd_8219505 < baseStart_8219505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219547 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_8219547 : Nat := 118140960795 + 8219547 * 2 ^ 59
def prefixEnd_8219547 : Nat := 4983230072969 + 3 ^ 40 * 8219547 * 2
def baseEnd_8219547 : Nat := 4220578373221457718261497

theorem tailTrace_8219547 : CollatzResearch.WordTrace tailWord_8219547 prefixEnd_8219547 4220578373221457718261497 := by
  unfold tailWord_8219547
  simp only [CollatzResearch.WordTrace]
  refine ⟨299791507952992480711528895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199861005301994987141019263 299791507952992480711528895)
  ·
    refine ⟨449687261929488721067293343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299791507952992480711528895 449687261929488721067293343)
    ·
      refine ⟨674530892894233081600940015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449687261929488721067293343 674530892894233081600940015)
      ·
        refine ⟨1011796339341349622401410023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674530892894233081600940015 1011796339341349622401410023)
        ·
          refine ⟨1517694509012024433602115035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011796339341349622401410023 1517694509012024433602115035)
          ·
            refine ⟨2276541763518036650403172553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517694509012024433602115035 2276541763518036650403172553)
            ·
              refine ⟨1707406322638527487802379415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276541763518036650403172553 1707406322638527487802379415)
              ·
                refine ⟨2561109483957791231703569123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707406322638527487802379415 2561109483957791231703569123)
                ·
                  refine ⟨3841664225936686847555353685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561109483957791231703569123 3841664225936686847555353685)
                  ·
                    refine ⟨45019502647695548994789301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3841664225936686847555353685 45019502647695548994789301)
                    ·
                      refine ⟨4220578373221457718261497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45019502647695548994789301 4220578373221457718261497)
                      ·
                        rfl

theorem cell23_8219547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_8219547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219547 prefixEnd_8219547 := by exact prefixLift 8219547
  have htrace : WordTrace (prefixWord ++ tailWord_8219547) baseStart_8219547 baseEnd_8219547 := by
    simpa [prefixWord, tailWord_8219547, baseEnd_8219547] using wordTrace_append hprefix tailTrace_8219547
  have hstable : (prefixWord ++ tailWord_8219547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219547).length < 2 ^ (prefixWord ++ tailWord_8219547).sum := by decide
  have hdescent : baseEnd_8219547 < baseStart_8219547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219581 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_8219581 : Nat := 118140960795 + 8219581 * 2 ^ 59
def prefixEnd_8219581 : Nat := 4983230072969 + 3 ^ 40 * 8219581 * 2
def baseEnd_8219581 : Nat := 4220595831563710585236341

theorem tailTrace_8219581 : CollatzResearch.WordTrace tailWord_8219581 prefixEnd_8219581 4220595831563710585236341 := by
  unfold tailWord_8219581
  simp only [CollatzResearch.WordTrace]
  refine ⟨299792748034869304518266597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199861832023246203012177731 299792748034869304518266597)
  ·
    refine ⟨56211140256537994597174987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299792748034869304518266597 56211140256537994597174987)
    ·
      refine ⟨84316710384806991895762481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56211140256537994597174987 84316710384806991895762481)
      ·
        refine ⟨63237532788605243921821861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84316710384806991895762481 63237532788605243921821861)
        ·
          refine ⟨11857037397863483235341599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63237532788605243921821861 11857037397863483235341599)
          ·
            refine ⟨17785556096795224853012399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857037397863483235341599 17785556096795224853012399)
            ·
              refine ⟨26678334145192837279518599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17785556096795224853012399 26678334145192837279518599)
              ·
                refine ⟨40017501217789255919277899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26678334145192837279518599 40017501217789255919277899)
                ·
                  refine ⟨60026251826683883878916849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40017501217789255919277899 60026251826683883878916849)
                  ·
                    refine ⟨45019688870012912909187637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60026251826683883878916849 45019688870012912909187637)
                    ·
                      refine ⟨4220595831563710585236341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45019688870012912909187637 4220595831563710585236341)
                      ·
                        rfl

theorem cell23_8219581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_8219581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219581 prefixEnd_8219581 := by exact prefixLift 8219581
  have htrace : WordTrace (prefixWord ++ tailWord_8219581) baseStart_8219581 baseEnd_8219581 := by
    simpa [prefixWord, tailWord_8219581, baseEnd_8219581] using wordTrace_append hprefix tailTrace_8219581
  have hstable : (prefixWord ++ tailWord_8219581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219581).length < 2 ^ (prefixWord ++ tailWord_8219581).sum := by decide
  have hdescent : baseEnd_8219581 < baseStart_8219581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219591 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_8219591 : Nat := 118140960795 + 8219591 * 2 ^ 59
def prefixEnd_8219591 : Nat := 4983230072969 + 3 ^ 40 * 8219591 * 2
def baseEnd_8219591 : Nat := 4220600966370255546111295

theorem tailTrace_8219591 : CollatzResearch.WordTrace tailWord_8219591 prefixEnd_8219591 4220600966370255546111295 := by
  unfold tailWord_8219591
  simp only [CollatzResearch.WordTrace]
  refine ⟨299793112764833076226130627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199862075176555384150753751 299793112764833076226130627)
  ·
    refine ⟨449689669147249614339195941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299793112764833076226130627 449689669147249614339195941)
    ·
      refine ⟨84316812965109302688599239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449689669147249614339195941 84316812965109302688599239)
      ·
        refine ⟨126475219447663954032898859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84316812965109302688599239 126475219447663954032898859)
        ·
          refine ⟨189712829171495931049348289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126475219447663954032898859 189712829171495931049348289)
          ·
            refine ⟨142284621878621948287011217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189712829171495931049348289 142284621878621948287011217)
            ·
              refine ⟨106713466408966461215258413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142284621878621948287011217 106713466408966461215258413)
              ·
                refine ⟨40017549903362422955721905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106713466408966461215258413 40017549903362422955721905)
                ·
                  refine ⟨30013162427521817216791429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40017549903362422955721905 30013162427521817216791429)
                  ·
                    refine ⟨5627467955160340728148393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30013162427521817216791429 5627467955160340728148393)
                    ·
                      refine ⟨4220600966370255546111295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627467955160340728148393 4220600966370255546111295)
                      ·
                        rfl

theorem cell23_8219591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_8219591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219591 prefixEnd_8219591 := by exact prefixLift 8219591
  have htrace : WordTrace (prefixWord ++ tailWord_8219591) baseStart_8219591 baseEnd_8219591 := by
    simpa [prefixWord, tailWord_8219591, baseEnd_8219591] using wordTrace_append hprefix tailTrace_8219591
  have hstable : (prefixWord ++ tailWord_8219591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219591).length < 2 ^ (prefixWord ++ tailWord_8219591).sum := by decide
  have hdescent : baseEnd_8219591 < baseStart_8219591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219631 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 6]
def baseStart_8219631 : Nat := 118140960795 + 8219631 * 2 ^ 59
def prefixEnd_8219631 : Nat := 4983230072969 + 3 ^ 40 * 8219631 * 2
def baseEnd_8219631 : Nat := 468957945066270598845679

theorem tailTrace_8219631 : CollatzResearch.WordTrace tailWord_8219631 prefixEnd_8219631 468957945066270598845679 := by
  unfold tailWord_8219631
  simp only [CollatzResearch.WordTrace]
  refine ⟨299794571684688163057586747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199863047789792108705057831 299794571684688163057586747)
  ·
    refine ⟨449691857527032244586380121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299794571684688163057586747 449691857527032244586380121)
    ·
      refine ⟨337268893145274183439785091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449691857527032244586380121 337268893145274183439785091)
      ·
        refine ⟨505903339717911275159677637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337268893145274183439785091 505903339717911275159677637)
        ·
          refine ⟨94856876197108364092439557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505903339717911275159677637 94856876197108364092439557)
          ·
            refine ⟨17785664286957818267332417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94856876197108364092439557 17785664286957818267332417)
            ·
              refine ⟨13339248215218363700499313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17785664286957818267332417 13339248215218363700499313)
              ·
                refine ⟨10004436161413772775374485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13339248215218363700499313 10004436161413772775374485)
                ·
                  refine ⟨468957945066270598845679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10004436161413772775374485 468957945066270598845679)
                  ·
                    rfl

theorem cell23_8219631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 6].length) (baseStart_8219631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219631 prefixEnd_8219631 := by exact prefixLift 8219631
  have htrace : WordTrace (prefixWord ++ tailWord_8219631) baseStart_8219631 baseEnd_8219631 := by
    simpa [prefixWord, tailWord_8219631, baseEnd_8219631] using wordTrace_append hprefix tailTrace_8219631
  have hstable : (prefixWord ++ tailWord_8219631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219631).length < 2 ^ (prefixWord ++ tailWord_8219631).sum := by decide
  have hdescent : baseEnd_8219631 < baseStart_8219631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219658 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_8219658 : Nat := 118140960795 + 8219658 * 2 ^ 59
def prefixEnd_8219658 : Nat := 4983230072969 + 3 ^ 40 * 8219658 * 2
def baseEnd_8219658 : Nat := 4220635369574106783973487

theorem tailTrace_8219658 : CollatzResearch.WordTrace tailWord_8219658 prefixEnd_8219658 4220635369574106783973487 := by
  unfold tailWord_8219658
  simp only [CollatzResearch.WordTrace]
  refine ⟨74948889113897586667204907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199863704303726897779213085 74948889113897586667204907)
  ·
    refine ⟨112423333670846380000807361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74948889113897586667204907 112423333670846380000807361)
    ·
      refine ⟨84317500253134785000605521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112423333670846380000807361 84317500253134785000605521)
      ·
        refine ⟨63238125189851088750454141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84317500253134785000605521 63238125189851088750454141)
        ·
          refine ⟨23714296946194158281420303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63238125189851088750454141 23714296946194158281420303)
          ·
            refine ⟨35571445419291237422130455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23714296946194158281420303 35571445419291237422130455)
            ·
              refine ⟨53357168128936856133195683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35571445419291237422130455 53357168128936856133195683)
              ·
                refine ⟨80035752193405284199793525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53357168128936856133195683 80035752193405284199793525)
                ·
                  refine ⟨7503351768131745393730643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80035752193405284199793525 7503351768131745393730643)
                  ·
                    refine ⟨11255027652197618090595965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7503351768131745393730643 11255027652197618090595965)
                    ·
                      refine ⟨4220635369574106783973487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255027652197618090595965 4220635369574106783973487)
                      ·
                        rfl

theorem cell23_8219658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_8219658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219658 prefixEnd_8219658 := by exact prefixLift 8219658
  have htrace : WordTrace (prefixWord ++ tailWord_8219658) baseStart_8219658 baseEnd_8219658 := by
    simpa [prefixWord, tailWord_8219658, baseEnd_8219658] using wordTrace_append hprefix tailTrace_8219658
  have hstable : (prefixWord ++ tailWord_8219658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219658).length < 2 ^ (prefixWord ++ tailWord_8219658).sum := by decide
  have hdescent : baseEnd_8219658 < baseStart_8219658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219691 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 4, 4]
def baseStart_8219691 : Nat := 118140960795 + 8219691 * 2 ^ 59
def prefixEnd_8219691 : Nat := 4983230072969 + 3 ^ 40 * 8219691 * 2
def baseEnd_8219691 : Nat := 1406884104811901718286945

theorem tailTrace_8219691 : CollatzResearch.WordTrace tailWord_8219691 prefixEnd_8219691 1406884104811901718286945 := by
  unfold tailWord_8219691
  simp only [CollatzResearch.WordTrace]
  refine ⟨299796760064470793304770927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199864506709647195536513951 299796760064470793304770927)
  ·
    refine ⟨449695140096706189957156391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299796760064470793304770927 449695140096706189957156391)
    ·
      refine ⟨674542710145059284935734587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449695140096706189957156391 674542710145059284935734587)
      ·
        refine ⟨1011814065217588927403601881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674542710145059284935734587 1011814065217588927403601881)
        ·
          refine ⟨758860548913191695552701411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011814065217588927403601881 758860548913191695552701411)
          ·
            refine ⟨1138290823369787543329052117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758860548913191695552701411 1138290823369787543329052117)
            ·
              refine ⟨26678691172729395546774659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1138290823369787543329052117 26678691172729395546774659)
              ·
                refine ⟨40018036759094093320161989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26678691172729395546774659 40018036759094093320161989)
                ·
                  refine ⟨7503381892330142497530373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40018036759094093320161989 7503381892330142497530373)
                  ·
                    refine ⟨1406884104811901718286945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503381892330142497530373 1406884104811901718286945)
                    ·
                      rfl

theorem cell23_8219691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 4].length) (baseStart_8219691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219691 prefixEnd_8219691 := by exact prefixLift 8219691
  have htrace : WordTrace (prefixWord ++ tailWord_8219691) baseStart_8219691 baseEnd_8219691 := by
    simpa [prefixWord, tailWord_8219691, baseEnd_8219691] using wordTrace_append hprefix tailTrace_8219691
  have hstable : (prefixWord ++ tailWord_8219691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219691).length < 2 ^ (prefixWord ++ tailWord_8219691).sum := by decide
  have hdescent : baseEnd_8219691 < baseStart_8219691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219708 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_8219708 : Nat := 118140960795 + 8219708 * 2 ^ 59
def prefixEnd_8219708 : Nat := 4983230072969 + 3 ^ 40 * 8219708 * 2
def baseEnd_8219708 : Nat := 1406887014535610529449419

theorem tailTrace_8219708 : CollatzResearch.WordTrace tailWord_8219708 prefixEnd_8219708 1406887014535610529449419 := by
  unfold tailWord_8219708
  simp only [CollatzResearch.WordTrace]
  refine ⟨149898690052704602604069889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199864920070272803472093185 149898690052704602604069889)
  ·
    refine ⟨112424017539528451953052417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149898690052704602604069889 112424017539528451953052417)
    ·
      refine ⟨84318013154646338964789313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112424017539528451953052417 84318013154646338964789313)
      ·
        refine ⟨63238509865984754223591985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84318013154646338964789313 63238509865984754223591985)
        ·
          refine ⟨47428882399488565667693989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63238509865984754223591985 47428882399488565667693989)
          ·
            refine ⟨8892915449904106062692623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47428882399488565667693989 8892915449904106062692623)
            ·
              refine ⟨13339373174856159094038935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892915449904106062692623 13339373174856159094038935)
              ·
                refine ⟨20009059762284238641058403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13339373174856159094038935 20009059762284238641058403)
                ·
                  refine ⟨30013589643426357961587605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20009059762284238641058403 30013589643426357961587605)
                  ·
                    refine ⟨1406887014535610529449419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30013589643426357961587605 1406887014535610529449419)
                    ·
                      rfl

theorem cell23_8219708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_8219708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219708 prefixEnd_8219708 := by exact prefixLift 8219708
  have htrace : WordTrace (prefixWord ++ tailWord_8219708) baseStart_8219708 baseEnd_8219708 := by
    simpa [prefixWord, tailWord_8219708, baseEnd_8219708] using wordTrace_append hprefix tailTrace_8219708
  have hstable : (prefixWord ++ tailWord_8219708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219708).length < 2 ^ (prefixWord ++ tailWord_8219708).sum := by decide
  have hdescent : baseEnd_8219708 < baseStart_8219708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219742 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_8219742 : Nat := 118140960795 + 8219742 * 2 ^ 59
def prefixEnd_8219742 : Nat := 4983230072969 + 3 ^ 40 * 8219742 * 2
def baseEnd_8219742 : Nat := 1406892833983028151774367

theorem tailTrace_8219742 : CollatzResearch.WordTrace tailWord_8219742 prefixEnd_8219742 1406892833983028151774367 := by
  unfold tailWord_8219742
  simp only [CollatzResearch.WordTrace]
  refine ⟨37474827523410753626859685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199865746791524019343251653 37474827523410753626859685)
  ·
    refine ⟨7026530160639516305036191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37474827523410753626859685 7026530160639516305036191)
    ·
      refine ⟨10539795240959274457554287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7026530160639516305036191 10539795240959274457554287)
      ·
        refine ⟨15809692861438911686331431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10539795240959274457554287 15809692861438911686331431)
        ·
          refine ⟨23714539292158367529497147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15809692861438911686331431 23714539292158367529497147)
          ·
            refine ⟨35571808938237551294245721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23714539292158367529497147 35571808938237551294245721)
            ·
              refine ⟨26678856703678163470684291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35571808938237551294245721 26678856703678163470684291)
              ·
                refine ⟨40018285055517245206026437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26678856703678163470684291 40018285055517245206026437)
                ·
                  refine ⟨7503428447909483476129957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40018285055517245206026437 7503428447909483476129957)
                  ·
                    refine ⟨1406892833983028151774367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503428447909483476129957 1406892833983028151774367)
                    ·
                      rfl

theorem cell23_8219742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_8219742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219742 prefixEnd_8219742 := by exact prefixLift 8219742
  have htrace : WordTrace (prefixWord ++ tailWord_8219742) baseStart_8219742 baseEnd_8219742 := by
    simpa [prefixWord, tailWord_8219742, baseEnd_8219742] using wordTrace_append hprefix tailTrace_8219742
  have hstable : (prefixWord ++ tailWord_8219742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219742).length < 2 ^ (prefixWord ++ tailWord_8219742).sum := by decide
  have hdescent : baseEnd_8219742 < baseStart_8219742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219749 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 1, 2, 2]
def baseStart_8219749 : Nat := 118140960795 + 8219749 * 2 ^ 59
def prefixEnd_8219749 : Nat := 4983230072969 + 3 ^ 40 * 8219749 * 2
def baseEnd_8219749 : Nat := 4220682096313665927935569

theorem tailTrace_8219749 : CollatzResearch.WordTrace tailWord_8219749 prefixEnd_8219749 4220682096313665927935569 := by
  unfold tailWord_8219749
  simp only [CollatzResearch.WordTrace]
  refine ⟨299798875498260669210382301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199865916998840446140254867 299798875498260669210382301)
  ·
    refine ⟨112424578311847750953893363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299798875498260669210382301 112424578311847750953893363)
    ·
      refine ⟨168636867467771626430840045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112424578311847750953893363 168636867467771626430840045)
      ·
        refine ⟨63238825300414359911565017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168636867467771626430840045 63238825300414359911565017)
        ·
          refine ⟨47429118975310769933673763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63238825300414359911565017 47429118975310769933673763)
          ·
            refine ⟨71143678462966154900510645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47429118975310769933673763 71143678462966154900510645)
            ·
              refine ⟨6669719855903077021922873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71143678462966154900510645 6669719855903077021922873)
              ·
                refine ⟨5002289891927307766442155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669719855903077021922873 5002289891927307766442155)
                ·
                  refine ⟨7503434837890961649663233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002289891927307766442155 7503434837890961649663233)
                  ·
                    refine ⟨5627576128418221237247425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7503434837890961649663233 5627576128418221237247425)
                    ·
                      refine ⟨4220682096313665927935569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627576128418221237247425 4220682096313665927935569)
                      ·
                        rfl

theorem cell23_8219749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_8219749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219749 prefixEnd_8219749 := by exact prefixLift 8219749
  have htrace : WordTrace (prefixWord ++ tailWord_8219749) baseStart_8219749 baseEnd_8219749 := by
    simpa [prefixWord, tailWord_8219749, baseEnd_8219749] using wordTrace_append hprefix tailTrace_8219749
  have hstable : (prefixWord ++ tailWord_8219749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219749).length < 2 ^ (prefixWord ++ tailWord_8219749).sum := by decide
  have hdescent : baseEnd_8219749 < baseStart_8219749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219851 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5]
def baseStart_8219851 : Nat := 118140960795 + 8219851 * 2 ^ 59
def prefixEnd_8219851 : Nat := 4983230072969 + 3 ^ 40 * 8219851 * 2
def baseEnd_8219851 : Nat := 4220734471340424528860099

theorem tailTrace_8219851 : CollatzResearch.WordTrace tailWord_8219851 prefixEnd_8219851 4220734471340424528860099 := by
  unfold tailWord_8219851
  simp only [CollatzResearch.WordTrace]
  refine ⟨299802595743891140630595407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199868397162594093753730271 299802595743891140630595407)
  ·
    refine ⟨449703893615836710945893111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299802595743891140630595407 449703893615836710945893111)
    ·
      refine ⟨674555840423755066418839667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449703893615836710945893111 674555840423755066418839667)
      ·
        refine ⟨1011833760635632599628259501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674555840423755066418839667 1011833760635632599628259501)
        ·
          refine ⟨379437660238362224860597313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1011833760635632599628259501 379437660238362224860597313)
          ·
            refine ⟨284578245178771668645447985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379437660238362224860597313 284578245178771668645447985)
            ·
              refine ⟨213433683884078751484085989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284578245178771668645447985 213433683884078751484085989)
              ·
                refine ⟨40018815728264765903266123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213433683884078751484085989 40018815728264765903266123)
                ·
                  refine ⟨60028223592397148854899185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40018815728264765903266123 60028223592397148854899185)
                  ·
                    refine ⟨45021167694297861641174389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60028223592397148854899185 45021167694297861641174389)
                    ·
                      refine ⟨4220734471340424528860099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45021167694297861641174389 4220734471340424528860099)
                      ·
                        rfl

theorem cell23_8219851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_8219851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219851 prefixEnd_8219851 := by exact prefixLift 8219851
  have htrace : WordTrace (prefixWord ++ tailWord_8219851) baseStart_8219851 baseEnd_8219851 := by
    simpa [prefixWord, tailWord_8219851, baseEnd_8219851] using wordTrace_append hprefix tailTrace_8219851
  have hstable : (prefixWord ++ tailWord_8219851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219851).length < 2 ^ (prefixWord ++ tailWord_8219851).sum := by decide
  have hdescent : baseEnd_8219851 < baseStart_8219851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219858 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_8219858 : Nat := 118140960795 + 8219858 * 2 ^ 59
def prefixEnd_8219858 : Nat := 4983230072969 + 3 ^ 40 * 8219858 * 2
def baseEnd_8219858 : Nat := 1406912688568335333824189

theorem tailTrace_8219858 : CollatzResearch.WordTrace tailWord_8219858 prefixEnd_8219858 1406912688568335333824189 := by
  unfold tailWord_8219858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74950712763716445206525057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199868567369910520550733485 74950712763716445206525057)
  ·
    refine ⟨56213034572787333904893793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74950712763716445206525057 56213034572787333904893793)
    ·
      refine ⟨42159775929590500428670345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56213034572787333904893793 42159775929590500428670345)
      ·
        refine ⟨31619831947192875321502759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42159775929590500428670345 31619831947192875321502759)
        ·
          refine ⟨47429747920789312982254139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31619831947192875321502759 47429747920789312982254139)
          ·
            refine ⟨71144621881183969473381209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47429747920789312982254139 71144621881183969473381209)
            ·
              refine ⟨53358466410887977105035907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71144621881183969473381209 53358466410887977105035907)
              ·
                refine ⟨80037699616331965657553861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53358466410887977105035907 80037699616331965657553861)
                ·
                  refine ⟨15007068678062243560791349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80037699616331965657553861 15007068678062243560791349)
                  ·
                    refine ⟨1406912688568335333824189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15007068678062243560791349 1406912688568335333824189)
                    ·
                      rfl

theorem cell23_8219858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_8219858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219858 prefixEnd_8219858 := by exact prefixLift 8219858
  have htrace : WordTrace (prefixWord ++ tailWord_8219858) baseStart_8219858 baseEnd_8219858 := by
    simpa [prefixWord, tailWord_8219858, baseEnd_8219858] using wordTrace_append hprefix tailTrace_8219858
  have hstable : (prefixWord ++ tailWord_8219858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219858).length < 2 ^ (prefixWord ++ tailWord_8219858).sum := by decide
  have hdescent : baseEnd_8219858 < baseStart_8219858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219862 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_8219862 : Nat := 118140960795 + 8219862 * 2 ^ 59
def prefixEnd_8219862 : Nat := 4983230072969 + 3 ^ 40 * 8219862 * 2
def baseEnd_8219862 : Nat := 468971124403069331758061

theorem tailTrace_8219862 : CollatzResearch.WordTrace tailWord_8219862 prefixEnd_8219862 468971124403069331758061 := by
  unfold tailWord_8219862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18737687309178205594327865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199868664631234193006163893 18737687309178205594327865)
  ·
    refine ⟨14053265481883654195745899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18737687309178205594327865 14053265481883654195745899)
    ·
      refine ⟨21079898222825481293618849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14053265481883654195745899 21079898222825481293618849)
      ·
        refine ⟨15809923667119110970214137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21079898222825481293618849 15809923667119110970214137)
        ·
          refine ⟨11857442750339333227660603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15809923667119110970214137 11857442750339333227660603)
          ·
            refine ⟨17786164125508999841490905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857442750339333227660603 17786164125508999841490905)
            ·
              refine ⟨13339623094131749881118179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17786164125508999841490905 13339623094131749881118179)
              ·
                refine ⟨20009434641197624821677269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13339623094131749881118179 20009434641197624821677269)
                ·
                  refine ⟨468971124403069331758061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20009434641197624821677269 468971124403069331758061)
                  ·
                    rfl

theorem cell23_8219862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_8219862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219862 prefixEnd_8219862 := by exact prefixLift 8219862
  have htrace : WordTrace (prefixWord ++ tailWord_8219862) baseStart_8219862 baseEnd_8219862 := by
    simpa [prefixWord, tailWord_8219862, baseEnd_8219862] using wordTrace_append hprefix tailTrace_8219862
  have hstable : (prefixWord ++ tailWord_8219862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219862).length < 2 ^ (prefixWord ++ tailWord_8219862).sum := by decide
  have hdescent : baseEnd_8219862 < baseStart_8219862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219898 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_8219898 : Nat := 118140960795 + 8219898 * 2 ^ 59
def prefixEnd_8219898 : Nat := 4983230072969 + 3 ^ 40 * 8219898 * 2
def baseEnd_8219898 : Nat := 4220758604931185844972383

theorem tailTrace_8219898 : CollatzResearch.WordTrace tailWord_8219898 prefixEnd_8219898 4220758604931185844972383 := by
  unfold tailWord_8219898
  simp only [CollatzResearch.WordTrace]
  refine ⟨74951077493680216914389087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199869539983147245105037565 74951077493680216914389087)
  ·
    refine ⟨112426616240520325371583631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74951077493680216914389087 112426616240520325371583631)
    ·
      refine ⟨168639924360780488057375447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112426616240520325371583631 168639924360780488057375447)
      ·
        refine ⟨252959886541170732086063171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168639924360780488057375447 252959886541170732086063171)
        ·
          refine ⟨379439829811756098129094757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252959886541170732086063171 379439829811756098129094757)
          ·
            refine ⟨71144968089704268399205267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379439829811756098129094757 71144968089704268399205267)
            ·
              refine ⟨106717452134556402598807901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71144968089704268399205267 106717452134556402598807901)
              ·
                refine ⟨40019044550458650974552963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106717452134556402598807901 40019044550458650974552963)
                ·
                  refine ⟨60028566825687976461829445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40019044550458650974552963 60028566825687976461829445)
                  ·
                    refine ⟨11255356279816495586593021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60028566825687976461829445 11255356279816495586593021)
                    ·
                      refine ⟨4220758604931185844972383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255356279816495586593021 4220758604931185844972383)
                      ·
                        rfl

theorem cell23_8219898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_8219898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219898 prefixEnd_8219898 := by exact prefixLift 8219898
  have htrace : WordTrace (prefixWord ++ tailWord_8219898) baseStart_8219898 baseEnd_8219898 := by
    simpa [prefixWord, tailWord_8219898, baseEnd_8219898] using wordTrace_append hprefix tailTrace_8219898
  have hstable : (prefixWord ++ tailWord_8219898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219898).length < 2 ^ (prefixWord ++ tailWord_8219898).sum := by decide
  have hdescent : baseEnd_8219898 < baseStart_8219898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219915 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 3]
def baseStart_8219915 : Nat := 118140960795 + 8219915 * 2 ^ 59
def prefixEnd_8219915 : Nat := 4983230072969 + 3 ^ 40 * 8219915 * 2
def baseEnd_8219915 : Nat := 4220767334102312278459805

theorem tailTrace_8219915 : CollatzResearch.WordTrace tailWord_8219915 prefixEnd_8219915 4220767334102312278459805 := by
  unfold tailWord_8219915
  simp only [CollatzResearch.WordTrace]
  refine ⟨299804930015659279560925199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199869953343772853040616799 299804930015659279560925199)
  ·
    refine ⟨449707395023488919341387799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299804930015659279560925199 449707395023488919341387799)
    ·
      refine ⟨674561092535233379012081699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449707395023488919341387799 674561092535233379012081699)
      ·
        refine ⟨1011841638802850068518122549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674561092535233379012081699 1011841638802850068518122549)
        ·
          refine ⟨94860153637767193923573989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1011841638802850068518122549 94860153637767193923573989)
          ·
            refine ⟨17786278807081348860670123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94860153637767193923573989 17786278807081348860670123)
            ·
              refine ⟨26679418210622023291005185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17786278807081348860670123 26679418210622023291005185)
              ·
                refine ⟨20009563657966517468253889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26679418210622023291005185 20009563657966517468253889)
                ·
                  refine ⟨15007172743474888101190417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20009563657966517468253889 15007172743474888101190417)
                  ·
                    refine ⟨11255379557606166075892813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15007172743474888101190417 11255379557606166075892813)
                    ·
                      refine ⟨4220767334102312278459805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255379557606166075892813 4220767334102312278459805)
                      ·
                        rfl

theorem cell23_8219915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 3].length) (baseStart_8219915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219915 prefixEnd_8219915 := by exact prefixLift 8219915
  have htrace : WordTrace (prefixWord ++ tailWord_8219915) baseStart_8219915 baseEnd_8219915 := by
    simpa [prefixWord, tailWord_8219915, baseEnd_8219915] using wordTrace_append hprefix tailTrace_8219915
  have hstable : (prefixWord ++ tailWord_8219915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219915).length < 2 ^ (prefixWord ++ tailWord_8219915).sum := by decide
  have hdescent : baseEnd_8219915 < baseStart_8219915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219918 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_8219918 : Nat := 118140960795 + 8219918 * 2 ^ 59
def prefixEnd_8219918 : Nat := 4983230072969 + 3 ^ 40 * 8219918 * 2
def baseEnd_8219918 : Nat := 468974319393808418524699

theorem tailTrace_8219918 : CollatzResearch.WordTrace tailWord_8219918 prefixEnd_8219918 468974319393808418524699 := by
  unfold tailWord_8219918
  simp only [CollatzResearch.WordTrace]
  refine ⟨37475629929331051384160551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199870026289765607382189605 37475629929331051384160551)
  ·
    refine ⟨56213444893996577076240827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37475629929331051384160551 56213444893996577076240827)
    ·
      refine ⟨84320167340994865614361241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56213444893996577076240827 84320167340994865614361241)
      ·
        refine ⟨63240125505746149210770931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84320167340994865614361241 63240125505746149210770931)
        ·
          refine ⟨94860188258619223816156397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63240125505746149210770931 94860188258619223816156397)
          ·
            refine ⟨35572570596982208931058649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94860188258619223816156397 35572570596982208931058649)
            ·
              refine ⟨26679427947736656698293987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35572570596982208931058649 26679427947736656698293987)
              ·
                refine ⟨40019141921604985047440981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26679427947736656698293987 40019141921604985047440981)
                ·
                  refine ⟨468974319393808418524699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40019141921604985047440981 468974319393808418524699)
                  ·
                    rfl

theorem cell23_8219918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_8219918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219918 prefixEnd_8219918 := by exact prefixLift 8219918
  have htrace : WordTrace (prefixWord ++ tailWord_8219918) baseStart_8219918 baseEnd_8219918 := by
    simpa [prefixWord, tailWord_8219918, baseEnd_8219918] using wordTrace_append hprefix tailTrace_8219918
  have hstable : (prefixWord ++ tailWord_8219918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219918).length < 2 ^ (prefixWord ++ tailWord_8219918).sum := by decide
  have hdescent : baseEnd_8219918 < baseStart_8219918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219931 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 9]
def baseStart_8219931 : Nat := 118140960795 + 8219931 * 2 ^ 59
def prefixEnd_8219931 : Nat := 4983230072969 + 3 ^ 40 * 8219931 * 2
def baseEnd_8219931 : Nat := 1406925183264261405286577

theorem tailTrace_8219931 : CollatzResearch.WordTrace tailWord_8219931 prefixEnd_8219931 1406925183264261405286577 := by
  unfold tailWord_8219931
  simp only [CollatzResearch.WordTrace]
  refine ⟨299805513583601314293507647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199870342389067542862338431 299805513583601314293507647)
  ·
    refine ⟨449708270375401971440261471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299805513583601314293507647 449708270375401971440261471)
    ·
      refine ⟨674562405563102957160392207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449708270375401971440261471 674562405563102957160392207)
      ·
        refine ⟨1011843608344654435740588311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674562405563102957160392207 1011843608344654435740588311)
        ·
          refine ⟨1517765412516981653610882467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011843608344654435740588311 1517765412516981653610882467)
          ·
            refine ⟨2276648118775472480416323701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517765412516981653610882467 2276648118775472480416323701)
            ·
              refine ⟨213435761135200545039030347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2276648118775472480416323701 213435761135200545039030347)
              ·
                refine ⟨320153641702800817558545521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213435761135200545039030347 320153641702800817558545521)
                ·
                  refine ⟨240115231277100613168909141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320153641702800817558545521 240115231277100613168909141)
                  ·
                    refine ⟨1406925183264261405286577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240115231277100613168909141 1406925183264261405286577)
                    ·
                      rfl

theorem cell23_8219931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_8219931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219931 prefixEnd_8219931 := by exact prefixLift 8219931
  have htrace : WordTrace (prefixWord ++ tailWord_8219931) baseStart_8219931 baseEnd_8219931 := by
    simpa [prefixWord, tailWord_8219931, baseEnd_8219931] using wordTrace_append hprefix tailTrace_8219931
  have hstable : (prefixWord ++ tailWord_8219931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219931).length < 2 ^ (prefixWord ++ tailWord_8219931).sum := by decide
  have hdescent : baseEnd_8219931 < baseStart_8219931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219935 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 6]
def baseStart_8219935 : Nat := 118140960795 + 8219935 * 2 ^ 59
def prefixEnd_8219935 : Nat := 4983230072969 + 3 ^ 40 * 8219935 * 2
def baseEnd_8219935 : Nat := 468975289301711355578857

theorem tailTrace_8219935 : CollatzResearch.WordTrace tailWord_8219935 prefixEnd_8219935 468975289301711355578857 := by
  unfold tailWord_8219935
  simp only [CollatzResearch.WordTrace]
  refine ⟨299805659475586822976653259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199870439650391215317768839 299805659475586822976653259)
  ·
    refine ⟨449708489213380234464979889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299805659475586822976653259 449708489213380234464979889)
    ·
      refine ⟨337281366910035175848734917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449708489213380234464979889 337281366910035175848734917)
      ·
        refine ⟨63240256295631595471637797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337281366910035175848734917 63240256295631595471637797)
        ·
          refine ⟨11857548055430924150932087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63240256295631595471637797 11857548055430924150932087)
          ·
            refine ⟨17786322083146386226398131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857548055430924150932087 17786322083146386226398131)
            ·
              refine ⟨26679483124719579339597197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17786322083146386226398131 26679483124719579339597197)
              ·
                refine ⟨10004806171769842252348949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26679483124719579339597197 10004806171769842252348949)
                ·
                  refine ⟨468975289301711355578857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10004806171769842252348949 468975289301711355578857)
                  ·
                    rfl

theorem cell23_8219935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 6].length) (baseStart_8219935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219935 prefixEnd_8219935 := by exact prefixLift 8219935
  have htrace : WordTrace (prefixWord ++ tailWord_8219935) baseStart_8219935 baseEnd_8219935 := by
    simpa [prefixWord, tailWord_8219935, baseEnd_8219935] using wordTrace_append hprefix tailTrace_8219935
  have hstable : (prefixWord ++ tailWord_8219935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219935).length < 2 ^ (prefixWord ++ tailWord_8219935).sum := by decide
  have hdescent : baseEnd_8219935 < baseStart_8219935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8219949 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_8219949 : Nat := 118140960795 + 8219949 * 2 ^ 59
def prefixEnd_8219949 : Nat := 4983230072969 + 3 ^ 40 * 8219949 * 2
def baseEnd_8219949 : Nat := 4220784792444565145434649

theorem tailTrace_8219949 : CollatzResearch.WordTrace tailWord_8219949 prefixEnd_8219949 4220784792444565145434649 := by
  unfold tailWord_8219949
  simp only [CollatzResearch.WordTrace]
  refine ⟨299806170097536103367662901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199870780065024068911775267 299806170097536103367662901)
  ·
    refine ⟨28106828446644009690718397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299806170097536103367662901 28106828446644009690718397)
    ·
      refine ⟨10540060667491503634019399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28106828446644009690718397 10540060667491503634019399)
      ·
        refine ⟨15810091001237255451029099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10540060667491503634019399 15810091001237255451029099)
        ·
          refine ⟨23715136501855883176543649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15810091001237255451029099 23715136501855883176543649)
          ·
            refine ⟨17786352376391912382407737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23715136501855883176543649 17786352376391912382407737)
            ·
              refine ⟨13339764282293934286805803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17786352376391912382407737 13339764282293934286805803)
              ·
                refine ⟨20009646423440901430208705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13339764282293934286805803 20009646423440901430208705)
                ·
                  refine ⟨15007234817580676072656529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20009646423440901430208705 15007234817580676072656529)
                  ·
                    refine ⟨11255426113185507054492397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15007234817580676072656529 11255426113185507054492397)
                    ·
                      refine ⟨4220784792444565145434649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255426113185507054492397 4220784792444565145434649)
                      ·
                        rfl

theorem cell23_8219949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_8219949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8219949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8219949 prefixEnd_8219949 := by exact prefixLift 8219949
  have htrace : WordTrace (prefixWord ++ tailWord_8219949) baseStart_8219949 baseEnd_8219949 := by
    simpa [prefixWord, tailWord_8219949, baseEnd_8219949] using wordTrace_append hprefix tailTrace_8219949
  have hstable : (prefixWord ++ tailWord_8219949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8219949).length < 2 ^ (prefixWord ++ tailWord_8219949).sum := by decide
  have hdescent : baseEnd_8219949 < baseStart_8219949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8219949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220002 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_8220002 : Nat := 118140960795 + 8220002 * 2 ^ 59
def prefixEnd_8220002 : Nat := 4983230072969 + 3 ^ 40 * 8220002 * 2
def baseEnd_8220002 : Nat := 4220812006919253438071905

theorem tailTrace_8220002 : CollatzResearch.WordTrace tailWord_8220002 prefixEnd_8220002 4220812006919253438071905 := by
  unfold tailWord_8220002
  simp only [CollatzResearch.WordTrace]
  refine ⟨74952025791586023354835565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199872068777562728946228173 74952025791586023354835565)
  ·
    refine ⟨28107009671844758758063337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74952025791586023354835565 28107009671844758758063337)
    ·
      refine ⟨21080257253883569068547503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28107009671844758758063337 21080257253883569068547503)
      ·
        refine ⟨31620385880825353602821255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21080257253883569068547503 31620385880825353602821255)
        ·
          refine ⟨47430578821238030404231883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31620385880825353602821255 47430578821238030404231883)
          ·
            refine ⟨71145868231857045606347825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47430578821238030404231883 71145868231857045606347825)
            ·
              refine ⟨53359401173892784204760869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71145868231857045606347825 53359401173892784204760869)
              ·
                refine ⟨10004887720104897038392663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53359401173892784204760869 10004887720104897038392663)
                ·
                  refine ⟨15007331580157345557588995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004887720104897038392663 15007331580157345557588995)
                  ·
                    refine ⟨22510997370236018336383493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15007331580157345557588995 22510997370236018336383493)
                    ·
                      refine ⟨4220812006919253438071905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22510997370236018336383493 4220812006919253438071905)
                      ·
                        rfl

theorem cell23_8220002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_8220002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220002 prefixEnd_8220002 := by exact prefixLift 8220002
  have htrace : WordTrace (prefixWord ++ tailWord_8220002) baseStart_8220002 baseEnd_8220002 := by
    simpa [prefixWord, tailWord_8220002, baseEnd_8220002] using wordTrace_append hprefix tailTrace_8220002
  have hstable : (prefixWord ++ tailWord_8220002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220002).length < 2 ^ (prefixWord ++ tailWord_8220002).sum := by decide
  have hdescent : baseEnd_8220002 < baseStart_8220002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220005 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_8220005 : Nat := 118140960795 + 8220005 * 2 ^ 59
def prefixEnd_8220005 : Nat := 4983230072969 + 3 ^ 40 * 8220005 * 2
def baseEnd_8220005 : Nat := 4220813547361216926334391

theorem tailTrace_8220005 : CollatzResearch.WordTrace tailWord_8220005 prefixEnd_8220005 4220813547361216926334391 := by
  unfold tailWord_8220005
  simp only [CollatzResearch.WordTrace]
  refine ⟨299808212585333224931701469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199872141723555483287800979 299808212585333224931701469)
  ·
    refine ⟨112428079719499959349388051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299808212585333224931701469 112428079719499959349388051)
    ·
      refine ⟨168642119579249939024082077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112428079719499959349388051 168642119579249939024082077)
      ·
        refine ⟨63240794842218727134030779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168642119579249939024082077 63240794842218727134030779)
        ·
          refine ⟨94861192263328090701046169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63240794842218727134030779 94861192263328090701046169)
          ·
            refine ⟨71145894197496068025784627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94861192263328090701046169 71145894197496068025784627)
            ·
              refine ⟨106718841296244102038676941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71145894197496068025784627 106718841296244102038676941)
              ·
                refine ⟨40019565486091538264503853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106718841296244102038676941 40019565486091538264503853)
                ·
                  refine ⟨15007337057284326849188945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40019565486091538264503853 15007337057284326849188945)
                  ·
                    refine ⟨11255502792963245136891709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15007337057284326849188945 11255502792963245136891709)
                    ·
                      refine ⟨4220813547361216926334391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255502792963245136891709 4220813547361216926334391)
                      ·
                        rfl

theorem cell23_8220005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_8220005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220005 prefixEnd_8220005 := by exact prefixLift 8220005
  have htrace : WordTrace (prefixWord ++ tailWord_8220005) baseStart_8220005 baseEnd_8220005 := by
    simpa [prefixWord, tailWord_8220005, baseEnd_8220005] using wordTrace_append hprefix tailTrace_8220005
  have hstable : (prefixWord ++ tailWord_8220005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220005).length < 2 ^ (prefixWord ++ tailWord_8220005).sum := by decide
  have hdescent : baseEnd_8220005 < baseStart_8220005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220036 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_8220036 : Nat := 118140960795 + 8220036 * 2 ^ 59
def prefixEnd_8220036 : Nat := 4983230072969 + 3 ^ 40 * 8220036 * 2
def baseEnd_8220036 : Nat := 4220829465261506305046749

theorem tailTrace_8220036 : CollatzResearch.WordTrace tailWord_8220036 prefixEnd_8220036 4220829465261506305046749 := by
  unfold tailWord_8220036
  simp only [CollatzResearch.WordTrace]
  refine ⟨149904671624110458613039981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199872895498813944817386641 149904671624110458613039981)
  ·
    refine ⟨56214251859041421979889993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149904671624110458613039981 56214251859041421979889993)
    ·
      refine ⟨42160688894281066484917495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56214251859041421979889993 42160688894281066484917495)
      ·
        refine ⟨63241033341421599727376243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42160688894281066484917495 63241033341421599727376243)
        ·
          refine ⟨94861550012132399591064365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63241033341421599727376243 94861550012132399591064365)
          ·
            refine ⟨35573081254549649846649137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94861550012132399591064365 35573081254549649846649137)
            ·
              refine ⟨26679810940912237384986853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35573081254549649846649137 26679810940912237384986853)
              ·
                refine ⟨5002464551421044509685035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26679810940912237384986853 5002464551421044509685035)
                ·
                  refine ⟨7503696827131566764527553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002464551421044509685035 7503696827131566764527553)
                  ·
                    refine ⟨5627772620348675073395665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7503696827131566764527553 5627772620348675073395665)
                    ·
                      refine ⟨4220829465261506305046749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627772620348675073395665 4220829465261506305046749)
                      ·
                        rfl

theorem cell23_8220036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_8220036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220036 prefixEnd_8220036 := by exact prefixLift 8220036
  have htrace : WordTrace (prefixWord ++ tailWord_8220036) baseStart_8220036 baseEnd_8220036 := by
    simpa [prefixWord, tailWord_8220036, baseEnd_8220036] using wordTrace_append hprefix tailTrace_8220036
  have hstable : (prefixWord ++ tailWord_8220036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220036).length < 2 ^ (prefixWord ++ tailWord_8220036).sum := by decide
  have hdescent : baseEnd_8220036 < baseStart_8220036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220046 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_8220046 : Nat := 118140960795 + 8220046 * 2 ^ 59
def prefixEnd_8220046 : Nat := 4983230072969 + 3 ^ 40 * 8220046 * 2
def baseEnd_8220046 : Nat := 1406944866689350421973901

theorem tailTrace_8220046 : CollatzResearch.WordTrace tailWord_8220046 prefixEnd_8220046 1406944866689350421973901 := by
  unfold tailWord_8220046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37476213497273086116742999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199873138652123125955962661 37476213497273086116742999)
  ·
    refine ⟨56214320245909629175114499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37476213497273086116742999 56214320245909629175114499)
    ·
      refine ⟨84321480368864443762671749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56214320245909629175114499 84321480368864443762671749)
      ·
        refine ⟨15810277569162083205500953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84321480368864443762671749 15810277569162083205500953)
        ·
          refine ⟨11857708176871562404125715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15810277569162083205500953 11857708176871562404125715)
          ·
            refine ⟨17786562265307343606188573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857708176871562404125715 17786562265307343606188573)
            ·
              refine ⟨6669960849490253852320715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17786562265307343606188573 6669960849490253852320715)
              ·
                refine ⟨10004941274235380778481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669960849490253852320715 10004941274235380778481073)
                ·
                  refine ⟨7503705955676535583860805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10004941274235380778481073 7503705955676535583860805)
                  ·
                    refine ⟨1406944866689350421973901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503705955676535583860805 1406944866689350421973901)
                    ·
                      rfl

theorem cell23_8220046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_8220046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220046 prefixEnd_8220046 := by exact prefixLift 8220046
  have htrace : WordTrace (prefixWord ++ tailWord_8220046) baseStart_8220046 baseEnd_8220046 := by
    simpa [prefixWord, tailWord_8220046, baseEnd_8220046] using wordTrace_append hprefix tailTrace_8220046
  have hstable : (prefixWord ++ tailWord_8220046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220046).length < 2 ^ (prefixWord ++ tailWord_8220046).sum := by decide
  have hdescent : baseEnd_8220046 < baseStart_8220046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220142 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_8220142 : Nat := 118140960795 + 8220142 * 2 ^ 59
def prefixEnd_8220142 : Nat := 4983230072969 + 3 ^ 40 * 8220142 * 2
def baseEnd_8220142 : Nat := 4220883894210882890321261

theorem tailTrace_8220142 : CollatzResearch.WordTrace tailWord_8220142 prefixEnd_8220142 4220883894210882890321261 := by
  unfold tailWord_8220142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37476651173229612166179835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199875472923891264886292453 37476651173229612166179835)
  ·
    refine ⟨56214976759844418249269753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37476651173229612166179835 56214976759844418249269753)
    ·
      refine ⟨42161232569883313686952315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56214976759844418249269753 42161232569883313686952315)
      ·
        refine ⟨63241848854824970530428473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42161232569883313686952315 63241848854824970530428473)
        ·
          refine ⟨47431386641118727897821355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63241848854824970530428473 47431386641118727897821355)
          ·
            refine ⟨71147079961678091846732033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47431386641118727897821355 71147079961678091846732033)
            ·
              refine ⟨53360309971258568885049025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71147079961678091846732033 53360309971258568885049025)
              ·
                refine ⟨40020232478443926663786769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53360309971258568885049025 40020232478443926663786769)
                ·
                  refine ⟨30015174358832944997840077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40020232478443926663786769 30015174358832944997840077)
                  ·
                    refine ⟨11255690384562354374190029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30015174358832944997840077 11255690384562354374190029)
                    ·
                      refine ⟨4220883894210882890321261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255690384562354374190029 4220883894210882890321261)
                      ·
                        rfl

theorem cell23_8220142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_8220142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220142 prefixEnd_8220142 := by exact prefixLift 8220142
  have htrace : WordTrace (prefixWord ++ tailWord_8220142) baseStart_8220142 baseEnd_8220142 := by
    simpa [prefixWord, tailWord_8220142, baseEnd_8220142] using wordTrace_append hprefix tailTrace_8220142
  have hstable : (prefixWord ++ tailWord_8220142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220142).length < 2 ^ (prefixWord ++ tailWord_8220142).sum := by decide
  have hdescent : baseEnd_8220142 < baseStart_8220142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220152 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 2, 5, 2]
def baseStart_8220152 : Nat := 118140960795 + 8220152 * 2 ^ 59
def prefixEnd_8220152 : Nat := 4983230072969 + 3 ^ 40 * 8220152 * 2
def baseEnd_8220152 : Nat := 4220889029017427851196215

theorem tailTrace_8220152 : CollatzResearch.WordTrace tailWord_8220152 prefixEnd_8220152 4220889029017427851196215 := by
  unfold tailWord_8220152
  simp only [CollatzResearch.WordTrace]
  refine ⟨149906787057900334518651355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199875716077200446024868473 149906787057900334518651355)
  ·
    refine ⟨224860180586850501777977033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149906787057900334518651355 224860180586850501777977033)
    ·
      refine ⟨168645135440137876333482775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224860180586850501777977033 168645135440137876333482775)
      ·
        refine ⟨252967703160206814500224163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168645135440137876333482775 252967703160206814500224163)
        ·
          refine ⟨379451554740310221750336245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252967703160206814500224163 379451554740310221750336245)
          ·
            refine ⟨35573583256904083289094023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379451554740310221750336245 35573583256904083289094023)
            ·
              refine ⟨53360374885356124933641035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35573583256904083289094023 53360374885356124933641035)
              ·
                refine ⟨80040562328034187400461553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53360374885356124933641035 80040562328034187400461553)
                ·
                  refine ⟨60030421746025640550346165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80040562328034187400461553 60030421746025640550346165)
                  ·
                    refine ⟨5627852038689903801594953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60030421746025640550346165 5627852038689903801594953)
                    ·
                      refine ⟨4220889029017427851196215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627852038689903801594953 4220889029017427851196215)
                      ·
                        rfl

theorem cell23_8220152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_8220152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220152 prefixEnd_8220152 := by exact prefixLift 8220152
  have htrace : WordTrace (prefixWord ++ tailWord_8220152) baseStart_8220152 baseEnd_8220152 := by
    simpa [prefixWord, tailWord_8220152, baseEnd_8220152] using wordTrace_append hprefix tailTrace_8220152
  have hstable : (prefixWord ++ tailWord_8220152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220152).length < 2 ^ (prefixWord ++ tailWord_8220152).sum := by decide
  have hdescent : baseEnd_8220152 < baseStart_8220152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220165 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_8220165 : Nat := 118140960795 + 8220165 * 2 ^ 59
def prefixEnd_8220165 : Nat := 4983230072969 + 3 ^ 40 * 8220165 * 2
def baseEnd_8220165 : Nat := 4220895704265936300333655

theorem tailTrace_8220165 : CollatzResearch.WordTrace tailWord_8220165 prefixEnd_8220165 4220895704265936300333655 := by
  unfold tailWord_8220165
  simp only [CollatzResearch.WordTrace]
  refine ⟨299814048264753572257525949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199876032176502381505017299 299814048264753572257525949)
  ·
    refine ⟨112430268099282589596572231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299814048264753572257525949 112430268099282589596572231)
    ·
      refine ⟨168645402148923884394858347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112430268099282589596572231 168645402148923884394858347)
      ·
        refine ⟨252968103223385826592287521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168645402148923884394858347 252968103223385826592287521)
        ·
          refine ⟨189726077417539369944215641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252968103223385826592287521 189726077417539369944215641)
          ·
            refine ⟨142294558063154527458161731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189726077417539369944215641 142294558063154527458161731)
            ·
              refine ⟨213441837094731791187242597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142294558063154527458161731 213441837094731791187242597)
              ·
                refine ⟨40020344455262210847607987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213441837094731791187242597 40020344455262210847607987)
                ·
                  refine ⟨60030516682893316271411981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40020344455262210847607987 60030516682893316271411981)
                  ·
                    refine ⟨22511443756084993601779493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60030516682893316271411981 22511443756084993601779493)
                    ·
                      refine ⟨4220895704265936300333655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22511443756084993601779493 4220895704265936300333655)
                      ·
                        rfl

theorem cell23_8220165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_8220165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220165 prefixEnd_8220165 := by exact prefixLift 8220165
  have htrace : WordTrace (prefixWord ++ tailWord_8220165) baseStart_8220165 baseEnd_8220165 := by
    simpa [prefixWord, tailWord_8220165, baseEnd_8220165] using wordTrace_append hprefix tailTrace_8220165
  have hstable : (prefixWord ++ tailWord_8220165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220165).length < 2 ^ (prefixWord ++ tailWord_8220165).sum := by decide
  have hdescent : baseEnd_8220165 < baseStart_8220165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220253 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8220253 : Nat := 118140960795 + 8220253 * 2 ^ 59
def prefixEnd_8220253 : Nat := 4983230072969 + 3 ^ 40 * 8220253 * 2
def baseEnd_8220253 : Nat := 4220940890563531956033251

theorem tailTrace_8220253 : CollatzResearch.WordTrace tailWord_8220253 prefixEnd_8220253 4220940890563531956033251 := by
  unfold tailWord_8220253
  simp only [CollatzResearch.WordTrace]
  refine ⟨299817257888434763286729413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199878171925623175524486275 299817257888434763286729413)
  ·
    refine ⟨56215735854081518116261765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299817257888434763286729413 56215735854081518116261765)
    ·
      refine ⟨10540450472640284646799081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56215735854081518116261765 10540450472640284646799081)
      ·
        refine ⟨7905337854480213485099311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10540450472640284646799081 7905337854480213485099311)
        ·
          refine ⟨11858006781720320227648967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905337854480213485099311 11858006781720320227648967)
          ·
            refine ⟨17787010172580480341473451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858006781720320227648967 17787010172580480341473451)
            ·
              refine ⟨26680515258870720512210177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17787010172580480341473451 26680515258870720512210177)
              ·
                refine ⟨20010386444153040384157633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26680515258870720512210177 20010386444153040384157633)
                ·
                  refine ⟨15007789833114780288118225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20010386444153040384157633 15007789833114780288118225)
                  ·
                    refine ⟨11255842374836085216088669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15007789833114780288118225 11255842374836085216088669)
                    ·
                      refine ⟨4220940890563531956033251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255842374836085216088669 4220940890563531956033251)
                      ·
                        rfl

theorem cell23_8220253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8220253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220253 prefixEnd_8220253 := by exact prefixLift 8220253
  have htrace : WordTrace (prefixWord ++ tailWord_8220253) baseStart_8220253 baseEnd_8220253 := by
    simpa [prefixWord, tailWord_8220253, baseEnd_8220253] using wordTrace_append hprefix tailTrace_8220253
  have hstable : (prefixWord ++ tailWord_8220253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220253).length < 2 ^ (prefixWord ++ tailWord_8220253).sum := by decide
  have hdescent : baseEnd_8220253 < baseStart_8220253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220259 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 4, 3, 2]
def baseStart_8220259 : Nat := 118140960795 + 8220259 * 2 ^ 59
def prefixEnd_8220259 : Nat := 4983230072969 + 3 ^ 40 * 8220259 * 2
def baseEnd_8220259 : Nat := 4220943971447458932558223

theorem tailTrace_8220259 : CollatzResearch.WordTrace tailWord_8220259 prefixEnd_8220259 4220943971447458932558223 := by
  unfold tailWord_8220259
  simp only [CollatzResearch.WordTrace]
  refine ⟨299817476726413026311447831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199878317817608684207631887 299817476726413026311447831)
  ·
    refine ⟨449726215089619539467171747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299817476726413026311447831 449726215089619539467171747)
    ·
      refine ⟨674589322634429309200757621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449726215089619539467171747 674589322634429309200757621)
      ·
        refine ⟨63242748996977747737571027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 674589322634429309200757621 63242748996977747737571027)
        ·
          refine ⟨94864123495466621606356541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63242748996977747737571027 94864123495466621606356541)
          ·
            refine ⟨35574046310799983102383703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94864123495466621606356541 35574046310799983102383703)
            ·
              refine ⟨53361069466199974653575555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35574046310799983102383703 53361069466199974653575555)
              ·
                refine ⟨80041604199299961980363333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53361069466199974653575555 80041604199299961980363333)
                ·
                  refine ⟨15007800787368742871318125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80041604199299961980363333 15007800787368742871318125)
                  ·
                    refine ⟨5627925295263278576744297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15007800787368742871318125 5627925295263278576744297)
                    ·
                      refine ⟨4220943971447458932558223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627925295263278576744297 4220943971447458932558223)
                      ·
                        rfl

theorem cell23_8220259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_8220259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220259 prefixEnd_8220259 := by exact prefixLift 8220259
  have htrace : WordTrace (prefixWord ++ tailWord_8220259) baseStart_8220259 baseEnd_8220259 := by
    simpa [prefixWord, tailWord_8220259, baseEnd_8220259] using wordTrace_append hprefix tailTrace_8220259
  have hstable : (prefixWord ++ tailWord_8220259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220259).length < 2 ^ (prefixWord ++ tailWord_8220259).sum := by decide
  have hdescent : baseEnd_8220259 < baseStart_8220259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220266 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_8220266 : Nat := 118140960795 + 8220266 * 2 ^ 59
def prefixEnd_8220266 : Nat := 4983230072969 + 3 ^ 40 * 8220266 * 2
def baseEnd_8220266 : Nat := 4220947565812040405170691

theorem tailTrace_8220266 : CollatzResearch.WordTrace tailWord_8220266 prefixEnd_8220266 4220947565812040405170691 := by
  unfold tailWord_8220266
  simp only [CollatzResearch.WordTrace]
  refine ⟨74954433009346916626738163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199878488024925111004635101 74954433009346916626738163)
  ·
    refine ⟨112431649514020374940107245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74954433009346916626738163 112431649514020374940107245)
    ·
      refine ⟨42161868567757640602540217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112431649514020374940107245 42161868567757640602540217)
      ·
        refine ⟨31621401425818230451905163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42161868567757640602540217 31621401425818230451905163)
        ·
          refine ⟨47432102138727345677857745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31621401425818230451905163 47432102138727345677857745)
          ·
            refine ⟨35574076604045509258393309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47432102138727345677857745 35574076604045509258393309)
            ·
              refine ⟨13340278726517065971897491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35574076604045509258393309 13340278726517065971897491)
              ·
                refine ⟨20010418089775598957846237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340278726517065971897491 20010418089775598957846237)
                ·
                  refine ⟨7503906783665849609192339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20010418089775598957846237 7503906783665849609192339)
                  ·
                    refine ⟨11255860175498774413788509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7503906783665849609192339 11255860175498774413788509)
                    ·
                      refine ⟨4220947565812040405170691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255860175498774413788509 4220947565812040405170691)
                      ·
                        rfl

theorem cell23_8220266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_8220266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220266 prefixEnd_8220266 := by exact prefixLift 8220266
  have htrace : WordTrace (prefixWord ++ tailWord_8220266) baseStart_8220266 baseEnd_8220266 := by
    simpa [prefixWord, tailWord_8220266, baseEnd_8220266] using wordTrace_append hprefix tailTrace_8220266
  have hstable : (prefixWord ++ tailWord_8220266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220266).length < 2 ^ (prefixWord ++ tailWord_8220266).sum := by decide
  have hdescent : baseEnd_8220266 < baseStart_8220266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220275 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_8220275 : Nat := 118140960795 + 8220275 * 2 ^ 59
def prefixEnd_8220275 : Nat := 4983230072969 + 3 ^ 40 * 8220275 * 2
def baseEnd_8220275 : Nat := 4220952187137930869958149

theorem tailTrace_8220275 : CollatzResearch.WordTrace tailWord_8220275 prefixEnd_8220275 4220952187137930869958149 := by
  unfold tailWord_8220275
  simp only [CollatzResearch.WordTrace]
  refine ⟨299818060294355061044030279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199878706862903374029353519 299818060294355061044030279)
  ·
    refine ⟨449727090441532591566045419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299818060294355061044030279 449727090441532591566045419)
    ·
      refine ⟨674590635662298887349068129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449727090441532591566045419 674590635662298887349068129)
      ·
        refine ⟨505942976746724165511801097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674590635662298887349068129 505942976746724165511801097)
        ·
          refine ⟨379457232560043124133850823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505942976746724165511801097 379457232560043124133850823)
          ·
            refine ⟨569185848840064686200776235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379457232560043124133850823 569185848840064686200776235)
            ·
              refine ⟨853778773260097029301164353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569185848840064686200776235 853778773260097029301164353)
              ·
                refine ⟨640334079945072771975873265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853778773260097029301164353 640334079945072771975873265)
                ·
                  refine ⟨480250559958804578981904949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640334079945072771975873265 480250559958804578981904949)
                  ·
                    refine ⟨45023489996137929279553589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 480250559958804578981904949 45023489996137929279553589)
                    ·
                      refine ⟨4220952187137930869958149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45023489996137929279553589 4220952187137930869958149)
                      ·
                        rfl

theorem cell23_8220275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_8220275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220275 prefixEnd_8220275 := by exact prefixLift 8220275
  have htrace : WordTrace (prefixWord ++ tailWord_8220275) baseStart_8220275 baseEnd_8220275 := by
    simpa [prefixWord, tailWord_8220275, baseEnd_8220275] using wordTrace_append hprefix tailTrace_8220275
  have hstable : (prefixWord ++ tailWord_8220275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220275).length < 2 ^ (prefixWord ++ tailWord_8220275).sum := by decide
  have hdescent : baseEnd_8220275 < baseStart_8220275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220282 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_8220282 : Nat := 118140960795 + 8220282 * 2 ^ 59
def prefixEnd_8220282 : Nat := 4983230072969 + 3 ^ 40 * 8220282 * 2
def baseEnd_8220282 : Nat := 1406985260500837447523539

theorem tailTrace_8220282 : CollatzResearch.WordTrace tailWord_8220282 prefixEnd_8220282 1406985260500837447523539 := by
  unfold tailWord_8220282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74954578901332425309883775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199878877070219800826356733 74954578901332425309883775)
  ·
    refine ⟨112431868351998637964825663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74954578901332425309883775 112431868351998637964825663)
    ·
      refine ⟨168647802527997956947238495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112431868351998637964825663 168647802527997956947238495)
      ·
        refine ⟨252971703791996935420857743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168647802527997956947238495 252971703791996935420857743)
        ·
          refine ⟨379457555687995403131286615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252971703791996935420857743 379457555687995403131286615)
          ·
            refine ⟨569186333531993104696929923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379457555687995403131286615 569186333531993104696929923)
            ·
              refine ⟨853779500297989657045394885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569186333531993104696929923 853779500297989657045394885)
              ·
                refine ⟨160083656305873060696011541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 853779500297989657045394885 160083656305873060696011541)
                ·
                  refine ⟨7503921389337799720125541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160083656305873060696011541 7503921389337799720125541)
                  ·
                    refine ⟨1406985260500837447523539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7503921389337799720125541 1406985260500837447523539)
                    ·
                      rfl

theorem cell23_8220282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_8220282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220282 prefixEnd_8220282 := by exact prefixLift 8220282
  have htrace : WordTrace (prefixWord ++ tailWord_8220282) baseStart_8220282 baseEnd_8220282 := by
    simpa [prefixWord, tailWord_8220282, baseEnd_8220282] using wordTrace_append hprefix tailTrace_8220282
  have hstable : (prefixWord ++ tailWord_8220282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220282).length < 2 ^ (prefixWord ++ tailWord_8220282).sum := by decide
  have hdescent : baseEnd_8220282 < baseStart_8220282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220289 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_8220289 : Nat := 118140960795 + 8220289 * 2 ^ 59
def prefixEnd_8220289 : Nat := 4983230072969 + 3 ^ 40 * 8220289 * 2
def baseEnd_8220289 : Nat := 4220959375867093815183085

theorem tailTrace_8220289 : CollatzResearch.WordTrace tailWord_8220289 prefixEnd_8220289 4220959375867093815183085 := by
  unfold tailWord_8220289
  simp only [CollatzResearch.WordTrace]
  refine ⟨299818570916304341435039921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199879047277536227623359947 299818570916304341435039921)
  ·
    refine ⟨224863928187228256076279941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299818570916304341435039921 224863928187228256076279941)
    ·
      refine ⟨42161986535105298014302489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224863928187228256076279941 42161986535105298014302489)
      ·
        refine ⟨31621489901328973510726867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42161986535105298014302489 31621489901328973510726867)
        ·
          refine ⟨47432234851993460266090301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31621489901328973510726867 47432234851993460266090301)
          ·
            refine ⟨17787088069497547599783863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47432234851993460266090301 17787088069497547599783863)
            ·
              refine ⟨26680632104246321399675795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17787088069497547599783863 26680632104246321399675795)
              ·
                refine ⟨40020948156369482099513693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26680632104246321399675795 40020948156369482099513693)
                ·
                  refine ⟨15007855558638555787317635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40020948156369482099513693 15007855558638555787317635)
                  ·
                    refine ⟨22511783337957833680976453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15007855558638555787317635 22511783337957833680976453)
                    ·
                      refine ⟨4220959375867093815183085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22511783337957833680976453 4220959375867093815183085)
                      ·
                        rfl

theorem cell23_8220289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_8220289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220289 prefixEnd_8220289 := by exact prefixLift 8220289
  have htrace : WordTrace (prefixWord ++ tailWord_8220289) baseStart_8220289 baseEnd_8220289 := by
    simpa [prefixWord, tailWord_8220289, baseEnd_8220289] using wordTrace_append hprefix tailTrace_8220289
  have hstable : (prefixWord ++ tailWord_8220289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220289).length < 2 ^ (prefixWord ++ tailWord_8220289).sum := by decide
  have hdescent : baseEnd_8220289 < baseStart_8220289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220309 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_8220309 : Nat := 118140960795 + 8220309 * 2 ^ 59
def prefixEnd_8220309 : Nat := 4983230072969 + 3 ^ 40 * 8220309 * 2
def baseEnd_8220309 : Nat := 4220969645480183736932993

theorem tailTrace_8220309 : CollatzResearch.WordTrace tailWord_8220309 prefixEnd_8220309 4220969645480183736932993 := by
  unfold tailWord_8220309
  simp only [CollatzResearch.WordTrace]
  refine ⟨299819300376231884850767981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199879533584154589900511987 299819300376231884850767981)
  ·
    refine ⟨112432237641086956819037993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299819300376231884850767981 112432237641086956819037993)
    ·
      refine ⟨84324178230815217614278495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112432237641086956819037993 84324178230815217614278495)
      ·
        refine ⟨126486267346222826421417743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84324178230815217614278495 126486267346222826421417743)
        ·
          refine ⟨189729401019334239632126615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126486267346222826421417743 189729401019334239632126615)
          ·
            refine ⟨284594101529001359448189923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189729401019334239632126615 284594101529001359448189923)
            ·
              refine ⟨426891152293502039172284885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284594101529001359448189923 426891152293502039172284885)
              ·
                refine ⟨10005261381878954043100427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 426891152293502039172284885 10005261381878954043100427)
                ·
                  refine ⟨15007892072818431064650641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10005261381878954043100427 15007892072818431064650641)
                  ·
                    refine ⟨11255919054613823298487981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15007892072818431064650641 11255919054613823298487981)
                    ·
                      refine ⟨4220969645480183736932993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255919054613823298487981 4220969645480183736932993)
                      ·
                        rfl

theorem cell23_8220309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_8220309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220309 prefixEnd_8220309 := by exact prefixLift 8220309
  have htrace : WordTrace (prefixWord ++ tailWord_8220309) baseStart_8220309 baseEnd_8220309 := by
    simpa [prefixWord, tailWord_8220309, baseEnd_8220309] using wordTrace_append hprefix tailTrace_8220309
  have hstable : (prefixWord ++ tailWord_8220309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220309).length < 2 ^ (prefixWord ++ tailWord_8220309).sum := by decide
  have hdescent : baseEnd_8220309 < baseStart_8220309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220323 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 1, 2, 2]
def baseStart_8220323 : Nat := 118140960795 + 8220323 * 2 ^ 59
def prefixEnd_8220323 : Nat := 4983230072969 + 3 ^ 40 * 8220323 * 2
def baseEnd_8220323 : Nat := 4220976834209346682157929

theorem tailTrace_8220323 : CollatzResearch.WordTrace tailWord_8220323 prefixEnd_8220323 4220976834209346682157929 := by
  unfold tailWord_8220323
  simp only [CollatzResearch.WordTrace]
  refine ⟨299819810998181165241777623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199879873998787443494518415 299819810998181165241777623)
  ·
    refine ⟨449729716497271747862666435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299819810998181165241777623 449729716497271747862666435)
    ·
      refine ⟨674594574745907621793999653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449729716497271747862666435 674594574745907621793999653)
      ·
        refine ⟨126486482764857679086374935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 674594574745907621793999653 126486482764857679086374935)
        ·
          refine ⟨189729724147286518629562403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126486482764857679086374935 189729724147286518629562403)
          ·
            refine ⟨284594586220929777944343605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189729724147286518629562403 284594586220929777944343605)
            ·
              refine ⟨26680742458212166682282213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284594586220929777944343605 26680742458212166682282213)
              ·
                refine ⟨5002639210914781252927915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26680742458212166682282213 5002639210914781252927915)
                ·
                  refine ⟨7503958816372171879391873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002639210914781252927915 7503958816372171879391873)
                  ·
                    refine ⟨5627969112279128909543905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7503958816372171879391873 5627969112279128909543905)
                    ·
                      refine ⟨4220976834209346682157929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5627969112279128909543905 4220976834209346682157929)
                      ·
                        rfl

theorem cell23_8220323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_8220323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220323 prefixEnd_8220323 := by exact prefixLift 8220323
  have htrace : WordTrace (prefixWord ++ tailWord_8220323) baseStart_8220323 baseEnd_8220323 := by
    simpa [prefixWord, tailWord_8220323, baseEnd_8220323] using wordTrace_append hprefix tailTrace_8220323
  have hstable : (prefixWord ++ tailWord_8220323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220323).length < 2 ^ (prefixWord ++ tailWord_8220323).sum := by decide
  have hdescent : baseEnd_8220323 < baseStart_8220323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220339 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 3]
def baseStart_8220339 : Nat := 118140960795 + 8220339 * 2 ^ 59
def prefixEnd_8220339 : Nat := 4983230072969 + 3 ^ 40 * 8220339 * 2
def baseEnd_8220339 : Nat := 4220985049899818619557855

theorem tailTrace_8220339 : CollatzResearch.WordTrace tailWord_8220339 prefixEnd_8220339 4220985049899818619557855 := by
  unfold tailWord_8220339
  simp only [CollatzResearch.WordTrace]
  refine ⟨299820394566123199974360071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199880263044082133316240047 299820394566123199974360071)
  ·
    refine ⟨449730591849184799961540107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299820394566123199974360071 449730591849184799961540107)
    ·
      refine ⟨674595887773777199942310161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449730591849184799961540107 674595887773777199942310161)
      ·
        refine ⟨505946915830332899956732621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674595887773777199942310161 505946915830332899956732621)
        ·
          refine ⟨189730093436374837483774733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505946915830332899956732621 189730093436374837483774733)
          ·
            refine ⟨71148785038640564056415525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189730093436374837483774733 71148785038640564056415525)
            ·
              refine ⟨13340397194745105760577911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71148785038640564056415525 13340397194745105760577911)
              ·
                refine ⟨20010595792117658640866867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340397194745105760577911 20010595792117658640866867)
                ·
                  refine ⟨30015893688176487961300301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20010595792117658640866867 30015893688176487961300301)
                  ·
                    refine ⟨11255960133066182985487613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30015893688176487961300301 11255960133066182985487613)
                    ·
                      refine ⟨4220985049899818619557855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255960133066182985487613 4220985049899818619557855)
                      ·
                        rfl

theorem cell23_8220339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_8220339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220339 prefixEnd_8220339 := by exact prefixLift 8220339
  have htrace : WordTrace (prefixWord ++ tailWord_8220339) baseStart_8220339 baseEnd_8220339 := by
    simpa [prefixWord, tailWord_8220339, baseEnd_8220339] using wordTrace_append hprefix tailTrace_8220339
  have hstable : (prefixWord ++ tailWord_8220339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220339).length < 2 ^ (prefixWord ++ tailWord_8220339).sum := by decide
  have hdescent : baseEnd_8220339 < baseStart_8220339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220352 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_8220352 : Nat := 118140960795 + 8220352 * 2 ^ 59
def prefixEnd_8220352 : Nat := 4983230072969 + 3 ^ 40 * 8220352 * 2
def baseEnd_8220352 : Nat := 4220991725148327068695295

theorem tailTrace_8220352 : CollatzResearch.WordTrace tailWord_8220352 prefixEnd_8220352 4220991725148327068695295 := by
  unfold tailWord_8220352
  simp only [CollatzResearch.WordTrace]
  refine ⟨149910434357538051597291655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199880579143384068796388873 149910434357538051597291655)
  ·
    refine ⟨224865651536307077395937483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149910434357538051597291655 224865651536307077395937483)
    ·
      refine ⟨337298477304460616093906225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224865651536307077395937483 337298477304460616093906225)
      ·
        refine ⟨252973857978345462070429669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337298477304460616093906225 252973857978345462070429669)
        ·
          refine ⟨47432598370939774138205563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252973857978345462070429669 47432598370939774138205563)
          ·
            refine ⟨71148897556409661207308345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47432598370939774138205563 71148897556409661207308345)
            ·
              refine ⟨53361673167307245905481259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71148897556409661207308345 53361673167307245905481259)
              ·
                refine ⟨80042509750960868858221889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53361673167307245905481259 80042509750960868858221889)
                ·
                  refine ⟨60031882313220651643666417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80042509750960868858221889 60031882313220651643666417)
                  ·
                    refine ⟨45023911734915488732749813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60031882313220651643666417 45023911734915488732749813)
                    ·
                      refine ⟨4220991725148327068695295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45023911734915488732749813 4220991725148327068695295)
                      ·
                        rfl

theorem cell23_8220352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_8220352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220352 prefixEnd_8220352 := by exact prefixLift 8220352
  have htrace : WordTrace (prefixWord ++ tailWord_8220352) baseStart_8220352 baseEnd_8220352 := by
    simpa [prefixWord, tailWord_8220352, baseEnd_8220352] using wordTrace_append hprefix tailTrace_8220352
  have hstable : (prefixWord ++ tailWord_8220352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220352).length < 2 ^ (prefixWord ++ tailWord_8220352).sum := by decide
  have hdescent : baseEnd_8220352 < baseStart_8220352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220354 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_8220354 : Nat := 118140960795 + 8220354 * 2 ^ 59
def prefixEnd_8220354 : Nat := 4983230072969 + 3 ^ 40 * 8220354 * 2
def baseEnd_8220354 : Nat := 1406997584036545353623429

theorem tailTrace_8220354 : CollatzResearch.WordTrace tailWord_8220354 prefixEnd_8220354 1406997584036545353623429 := by
  unfold tailWord_8220354
  simp only [CollatzResearch.WordTrace]
  refine ⟨74955235415267214384039029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199880627774045905024104077 74955235415267214384039029)
  ·
    refine ⟨7027053320181301348503659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74955235415267214384039029 7027053320181301348503659)
    ·
      refine ⟨10540579980271952022755489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027053320181301348503659 10540579980271952022755489)
      ·
        refine ⟨7905434985203964017066617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10540579980271952022755489 7905434985203964017066617)
        ·
          refine ⟨5929076238902973012799963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7905434985203964017066617 5929076238902973012799963)
          ·
            refine ⟨8893614358354459519199945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929076238902973012799963 8893614358354459519199945)
            ·
              refine ⟨6670210768765844639399959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8893614358354459519199945 6670210768765844639399959)
              ·
                refine ⟨10005316153148766959099939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670210768765844639399959 10005316153148766959099939)
                ·
                  refine ⟨15007974229723150438649909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10005316153148766959099939 15007974229723150438649909)
                  ·
                    refine ⟨1406997584036545353623429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15007974229723150438649909 1406997584036545353623429)
                    ·
                      rfl

theorem cell23_8220354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_8220354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220354 prefixEnd_8220354 := by exact prefixLift 8220354
  have htrace : WordTrace (prefixWord ++ tailWord_8220354) baseStart_8220354 baseEnd_8220354 := by
    simpa [prefixWord, tailWord_8220354, baseEnd_8220354] using wordTrace_append hprefix tailTrace_8220354
  have hstable : (prefixWord ++ tailWord_8220354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220354).length < 2 ^ (prefixWord ++ tailWord_8220354).sum := by decide
  have hdescent : baseEnd_8220354 < baseStart_8220354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220356 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_8220356 : Nat := 118140960795 + 8220356 * 2 ^ 59
def prefixEnd_8220356 : Nat := 4983230072969 + 3 ^ 40 * 8220356 * 2
def baseEnd_8220356 : Nat := 4220993779070945053045277

theorem tailTrace_8220356 : CollatzResearch.WordTrace tailWord_8220356 prefixEnd_8220356 4220993779070945053045277 := by
  unfold tailWord_8220356
  simp only [CollatzResearch.WordTrace]
  refine ⟨149910507303530805938864461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199880676404707741251819281 149910507303530805938864461)
  ·
    refine ⟨56216440238824052227074173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149910507303530805938864461 56216440238824052227074173)
    ·
      refine ⟨21081165089559019585152815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56216440238824052227074173 21081165089559019585152815)
      ·
        refine ⟨31621747634338529377729223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21081165089559019585152815 31621747634338529377729223)
        ·
          refine ⟨47432621451507794066593835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31621747634338529377729223 47432621451507794066593835)
          ·
            refine ⟨71148932177261691099890753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47432621451507794066593835 71148932177261691099890753)
            ·
              refine ⟨53361699132946268324918065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71148932177261691099890753 53361699132946268324918065)
              ·
                refine ⟨40021274349709701243688549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53361699132946268324918065 40021274349709701243688549)
                ·
                  refine ⟨7503988940570568983191603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40021274349709701243688549 7503988940570568983191603)
                  ·
                    refine ⟨11255983410855853474787405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7503988940570568983191603 11255983410855853474787405)
                    ·
                      refine ⟨4220993779070945053045277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11255983410855853474787405 4220993779070945053045277)
                      ·
                        rfl

theorem cell23_8220356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_8220356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220356 prefixEnd_8220356 := by exact prefixLift 8220356
  have htrace : WordTrace (prefixWord ++ tailWord_8220356) baseStart_8220356 baseEnd_8220356 := by
    simpa [prefixWord, tailWord_8220356, baseEnd_8220356] using wordTrace_append hprefix tailTrace_8220356
  have hstable : (prefixWord ++ tailWord_8220356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220356).length < 2 ^ (prefixWord ++ tailWord_8220356).sum := by decide
  have hdescent : baseEnd_8220356 < baseStart_8220356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220396 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 1, 4, 2]
def baseStart_8220396 : Nat := 118140960795 + 8220396 * 2 ^ 59
def prefixEnd_8220396 : Nat := 4983230072969 + 3 ^ 40 * 8220396 * 2
def baseEnd_8220396 : Nat := 4221014318297124896545093

theorem tailTrace_8220396 : CollatzResearch.WordTrace tailWord_8220396 prefixEnd_8220396 4221014318297124896545093 := by
  unfold tailWord_8220396
  simp only [CollatzResearch.WordTrace]
  refine ⟨149911236763458349354592521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199881649017944465806123361 149911236763458349354592521)
  ·
    refine ⟨112433427572593762015944391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149911236763458349354592521 112433427572593762015944391)
    ·
      refine ⟨168650141358890643023916587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112433427572593762015944391 168650141358890643023916587)
      ·
        refine ⟨252975212038335964535874881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168650141358890643023916587 252975212038335964535874881)
        ·
          refine ⟨189731409028751973401906161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252975212038335964535874881 189731409028751973401906161)
          ·
            refine ⟨142298556771563980051429621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189731409028751973401906161 142298556771563980051429621)
            ·
              refine ⟨13340489697334123129821527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142298556771563980051429621 13340489697334123129821527)
              ·
                refine ⟨20010734546001184694732291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340489697334123129821527 20010734546001184694732291)
                ·
                  refine ⟨30016101819001777042098437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20010734546001184694732291 30016101819001777042098437)
                  ·
                    refine ⟨5628019091062833195393457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30016101819001777042098437 5628019091062833195393457)
                    ·
                      refine ⟨4221014318297124896545093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628019091062833195393457 4221014318297124896545093)
                      ·
                        rfl

theorem cell23_8220396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_8220396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220396 prefixEnd_8220396 := by exact prefixLift 8220396
  have htrace : WordTrace (prefixWord ++ tailWord_8220396) baseStart_8220396 baseEnd_8220396 := by
    simpa [prefixWord, tailWord_8220396, baseEnd_8220396] using wordTrace_append hprefix tailTrace_8220396
  have hstable : (prefixWord ++ tailWord_8220396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220396).length < 2 ^ (prefixWord ++ tailWord_8220396).sum := by decide
  have hdescent : baseEnd_8220396 < baseStart_8220396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220466 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_8220466 : Nat := 118140960795 + 8220466 * 2 ^ 59
def prefixEnd_8220466 : Nat := 4983230072969 + 3 ^ 40 * 8220466 * 2
def baseEnd_8220466 : Nat := 1407016753980979874223257

theorem tailTrace_8220466 : CollatzResearch.WordTrace tailWord_8220466 prefixEnd_8220466 1407016753980979874223257 := by
  unfold tailWord_8220466
  simp only [CollatzResearch.WordTrace]
  refine ⟨74956256659165775166058313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199883351091108733776155501 74956256659165775166058313)
  ·
    refine ⟨56217192494374331374543735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74956256659165775166058313 56217192494374331374543735)
    ·
      refine ⟨84325788741561497061815603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56217192494374331374543735 84325788741561497061815603)
      ·
        refine ⟨126488683112342245592723405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84325788741561497061815603 126488683112342245592723405)
        ·
          refine ⟨47433256167128342097271277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126488683112342245592723405 47433256167128342097271277)
          ·
            refine ⟨17787471062673128286476729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47433256167128342097271277 17787471062673128286476729)
            ·
              refine ⟨13340603297004846214857547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17787471062673128286476729 13340603297004846214857547)
              ·
                refine ⟨20010904945507269322286321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340603297004846214857547 20010904945507269322286321)
                ·
                  refine ⟨15008178709130451991714741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20010904945507269322286321 15008178709130451991714741)
                  ·
                    refine ⟨1407016753980979874223257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15008178709130451991714741 1407016753980979874223257)
                    ·
                      rfl

theorem cell23_8220466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_8220466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220466 prefixEnd_8220466 := by exact prefixLift 8220466
  have htrace : WordTrace (prefixWord ++ tailWord_8220466) baseStart_8220466 baseEnd_8220466 := by
    simpa [prefixWord, tailWord_8220466, baseEnd_8220466] using wordTrace_append hprefix tailTrace_8220466
  have hstable : (prefixWord ++ tailWord_8220466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220466).length < 2 ^ (prefixWord ++ tailWord_8220466).sum := by decide
  have hdescent : baseEnd_8220466 < baseStart_8220466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220503 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 2, 4, 2]
def baseStart_8220503 : Nat := 118140960795 + 8220503 * 2 ^ 59
def prefixEnd_8220503 : Nat := 4983230072969 + 3 ^ 40 * 8220503 * 2
def baseEnd_8220503 : Nat := 4221069260727155977907101

theorem tailTrace_8220503 : CollatzResearch.WordTrace tailWord_8220503 prefixEnd_8220503 4221069260727155977907101 := by
  unfold tailWord_8220503
  simp only [CollatzResearch.WordTrace]
  refine ⟨299826376137529055983330163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199884250758352703988886775 299826376137529055983330163)
  ·
    refine ⟨449739564206293583974995245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299826376137529055983330163 449739564206293583974995245)
    ·
      refine ⟨168652336577360093990623217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449739564206293583974995245 168652336577360093990623217)
      ·
        refine ⟨126489252433020070492967413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168652336577360093990623217 126489252433020070492967413)
        ·
          refine ⟨11858367415595631608715695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126489252433020070492967413 11858367415595631608715695)
          ·
            refine ⟨17787551123393447413073543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858367415595631608715695 17787551123393447413073543)
            ·
              refine ⟨26681326685090171119610315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17787551123393447413073543 26681326685090171119610315)
              ·
                refine ⟨40021990027635256679415473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26681326685090171119610315 40021990027635256679415473)
                ·
                  refine ⟨30016492520726442509561605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40021990027635256679415473 30016492520726442509561605)
                  ·
                    refine ⟨5628092347636207970542801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30016492520726442509561605 5628092347636207970542801)
                    ·
                      refine ⟨4221069260727155977907101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628092347636207970542801 4221069260727155977907101)
                      ·
                        rfl

theorem cell23_8220503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_8220503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220503 prefixEnd_8220503 := by exact prefixLift 8220503
  have htrace : WordTrace (prefixWord ++ tailWord_8220503) baseStart_8220503 baseEnd_8220503 := by
    simpa [prefixWord, tailWord_8220503, baseEnd_8220503] using wordTrace_append hprefix tailTrace_8220503
  have hstable : (prefixWord ++ tailWord_8220503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220503).length < 2 ^ (prefixWord ++ tailWord_8220503).sum := by decide
  have hdescent : baseEnd_8220503 < baseStart_8220503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220553 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 3]
def baseStart_8220553 : Nat := 118140960795 + 8220553 * 2 ^ 59
def prefixEnd_8220553 : Nat := 4983230072969 + 3 ^ 40 * 8220553 * 2
def baseEnd_8220553 : Nat := 4221094934759880782281871

theorem tailTrace_8220553 : CollatzResearch.WordTrace tailWord_8220553 prefixEnd_8220553 4221094934759880782281871 := by
  unfold tailWord_8220553
  simp only [CollatzResearch.WordTrace]
  refine ⟨299828199787347914522650313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199885466524898609681766875 299828199787347914522650313)
  ·
    refine ⟨224871149840510935891987735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299828199787347914522650313 224871149840510935891987735)
    ·
      refine ⟨337306724760766403837981603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224871149840510935891987735 337306724760766403837981603)
      ·
        refine ⟨505960087141149605756972405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337306724760766403837981603 505960087141149605756972405)
        ·
          refine ⟨47433758169482775539716163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 505960087141149605756972405 47433758169482775539716163)
          ·
            refine ⟨71150637254224163309574245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47433758169482775539716163 71150637254224163309574245)
            ·
              refine ⟨13340744485167030620545171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71150637254224163309574245 13340744485167030620545171)
              ·
                refine ⟨20011116727750545930817757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340744485167030620545171 20011116727750545930817757)
                ·
                  refine ⟨7504168772906454724056659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20011116727750545930817757 7504168772906454724056659)
                  ·
                    refine ⟨11256253159359682086084989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504168772906454724056659 11256253159359682086084989)
                    ·
                      refine ⟨4221094934759880782281871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256253159359682086084989 4221094934759880782281871)
                      ·
                        rfl

theorem cell23_8220553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_8220553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220553 prefixEnd_8220553 := by exact prefixLift 8220553
  have htrace : WordTrace (prefixWord ++ tailWord_8220553) baseStart_8220553 baseEnd_8220553 := by
    simpa [prefixWord, tailWord_8220553, baseEnd_8220553] using wordTrace_append hprefix tailTrace_8220553
  have hstable : (prefixWord ++ tailWord_8220553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220553).length < 2 ^ (prefixWord ++ tailWord_8220553).sum := by decide
  have hdescent : baseEnd_8220553 < baseStart_8220553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220573 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_8220573 : Nat := 118140960795 + 8220573 * 2 ^ 59
def prefixEnd_8220573 : Nat := 4983230072969 + 3 ^ 40 * 8220573 * 2
def baseEnd_8220573 : Nat := 1407035068124323568010593

theorem tailTrace_8220573 : CollatzResearch.WordTrace tailWord_8220573 prefixEnd_8220573 1407035068124323568010593 := by
  unfold tailWord_8220573
  simp only [CollatzResearch.WordTrace]
  refine ⟨299828929247275457938378373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199885952831516971958918915 299828929247275457938378373)
  ·
    refine ⟨56217924233864148363445945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299828929247275457938378373 56217924233864148363445945)
    ·
      refine ⟨42163443175398111272584459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56217924233864148363445945 42163443175398111272584459)
      ·
        refine ⟨63245164763097166908876689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42163443175398111272584459 63245164763097166908876689)
        ·
          refine ⟨47433873572322875181657517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63245164763097166908876689 47433873572322875181657517)
          ·
            refine ⟨17787702589621078193121569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47433873572322875181657517 17787702589621078193121569)
            ·
              refine ⟨13340776942215808644841177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17787702589621078193121569 13340776942215808644841177)
              ·
                refine ⟨10005582706661856483630883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13340776942215808644841177 10005582706661856483630883)
                ·
                  refine ⟨15008374059992784725446325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10005582706661856483630883 15008374059992784725446325)
                  ·
                    refine ⟨1407035068124323568010593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15008374059992784725446325 1407035068124323568010593)
                    ·
                      rfl

theorem cell23_8220573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_8220573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220573 prefixEnd_8220573 := by exact prefixLift 8220573
  have htrace : WordTrace (prefixWord ++ tailWord_8220573) baseStart_8220573 baseEnd_8220573 := by
    simpa [prefixWord, tailWord_8220573, baseEnd_8220573] using wordTrace_append hprefix tailTrace_8220573
  have hstable : (prefixWord ++ tailWord_8220573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220573).length < 2 ^ (prefixWord ++ tailWord_8220573).sum := by decide
  have hdescent : baseEnd_8220573 < baseStart_8220573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220576 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 8, 2]
def baseStart_8220576 : Nat := 118140960795 + 8220576 * 2 ^ 59
def prefixEnd_8220576 : Nat := 4983230072969 + 3 ^ 40 * 8220576 * 2
def baseEnd_8220576 : Nat := 4221106744814934192294265

theorem tailTrace_8220576 : CollatzResearch.WordTrace tailWord_8220576 prefixEnd_8220576 4221106744814934192294265 := by
  unfold tailWord_8220576
  simp only [CollatzResearch.WordTrace]
  refine ⟨149914519333132294725368791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199886025777509726300491721 149914519333132294725368791)
  ·
    refine ⟨224871778999698442088053187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149914519333132294725368791 224871778999698442088053187)
    ·
      refine ⟨337307668499547663132079781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224871778999698442088053187 337307668499547663132079781)
      ·
        refine ⟨63245187843665186837264959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337307668499547663132079781 63245187843665186837264959)
        ·
          refine ⟨94867781765497780255897439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63245187843665186837264959 94867781765497780255897439)
          ·
            refine ⟨142301672648246670383846159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94867781765497780255897439 142301672648246670383846159)
            ·
              refine ⟨213452508972370005575769239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142301672648246670383846159 213452508972370005575769239)
              ·
                refine ⟨320178763458555008363653859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213452508972370005575769239 320178763458555008363653859)
                ·
                  refine ⟨480268145187832512545480789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320178763458555008363653859 480268145187832512545480789)
                  ·
                    refine ⟨5628142326419912256392353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 480268145187832512545480789 5628142326419912256392353)
                    ·
                      refine ⟨4221106744814934192294265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628142326419912256392353 4221106744814934192294265)
                      ·
                        rfl

theorem cell23_8220576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_8220576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220576 prefixEnd_8220576 := by exact prefixLift 8220576
  have htrace : WordTrace (prefixWord ++ tailWord_8220576) baseStart_8220576 baseEnd_8220576 := by
    simpa [prefixWord, tailWord_8220576, baseEnd_8220576] using wordTrace_append hprefix tailTrace_8220576
  have hstable : (prefixWord ++ tailWord_8220576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220576).length < 2 ^ (prefixWord ++ tailWord_8220576).sum := by decide
  have hdescent : baseEnd_8220576 < baseStart_8220576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220579 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5]
def baseStart_8220579 : Nat := 118140960795 + 8220579 * 2 ^ 59
def prefixEnd_8220579 : Nat := 4983230072969 + 3 ^ 40 * 8220579 * 2
def baseEnd_8220579 : Nat := 4221108285256897680556751

theorem tailTrace_8220579 : CollatzResearch.WordTrace tailWord_8220579 prefixEnd_8220579 4221108285256897680556751 := by
  unfold tailWord_8220579
  simp only [CollatzResearch.WordTrace]
  refine ⟨299829148085253720963096791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199886098723502480642064527 299829148085253720963096791)
  ·
    refine ⟨449743722127880581444645187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299829148085253720963096791 449743722127880581444645187)
    ·
      refine ⟨674615583191820872166967781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449743722127880581444645187 674615583191820872166967781)
      ·
        refine ⟨126490421848466413531306459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 674615583191820872166967781 126490421848466413531306459)
        ·
          refine ⟨189735632772699620296959689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126490421848466413531306459 189735632772699620296959689)
          ·
            refine ⟨142301724579524715222719767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189735632772699620296959689 142301724579524715222719767)
            ·
              refine ⟨213452586869287072834079651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142301724579524715222719767 213452586869287072834079651)
              ·
                refine ⟨320178880303930609251119477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213452586869287072834079651 320178880303930609251119477)
                ·
                  refine ⟨30016770028493494617292451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320178880303930609251119477 30016770028493494617292451)
                  ·
                    refine ⟨45025155042740241925938677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30016770028493494617292451 45025155042740241925938677)
                    ·
                      refine ⟨4221108285256897680556751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45025155042740241925938677 4221108285256897680556751)
                      ·
                        rfl

theorem cell23_8220579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_8220579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220579 prefixEnd_8220579 := by exact prefixLift 8220579
  have htrace : WordTrace (prefixWord ++ tailWord_8220579) baseStart_8220579 baseEnd_8220579 := by
    simpa [prefixWord, tailWord_8220579, baseEnd_8220579] using wordTrace_append hprefix tailTrace_8220579
  have hstable : (prefixWord ++ tailWord_8220579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220579).length < 2 ^ (prefixWord ++ tailWord_8220579).sum := by decide
  have hdescent : baseEnd_8220579 < baseStart_8220579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220593 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_8220593 : Nat := 118140960795 + 8220593 * 2 ^ 59
def prefixEnd_8220593 : Nat := 4983230072969 + 3 ^ 40 * 8220593 * 2
def baseEnd_8220593 : Nat := 4221115473986060625781687

theorem tailTrace_8220593 : CollatzResearch.WordTrace tailWord_8220593 prefixEnd_8220593 4221115473986060625781687 := by
  unfold tailWord_8220593
  simp only [CollatzResearch.WordTrace]
  refine ⟨299829658707203001354106433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199886439138135334236070955 299829658707203001354106433)
  ·
    refine ⟨224872244030402251015579825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299829658707203001354106433 224872244030402251015579825)
    ·
      refine ⟨168654183022801688261684869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224872244030402251015579825 168654183022801688261684869)
      ·
        refine ⟨31622659316775316549065913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168654183022801688261684869 31622659316775316549065913)
        ·
          refine ⟨23716994487581487411799435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31622659316775316549065913 23716994487581487411799435)
          ·
            refine ⟨35575491731372231117699153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23716994487581487411799435 35575491731372231117699153)
            ·
              refine ⟨26681618798529173338274365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35575491731372231117699153 26681618798529173338274365)
              ·
                refine ⟨10005607049448440001852887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26681618798529173338274365 10005607049448440001852887)
                ·
                  refine ⟨15008410574172660002779331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10005607049448440001852887 15008410574172660002779331)
                  ·
                    refine ⟨22512615861258990004168997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15008410574172660002779331 22512615861258990004168997)
                    ·
                      refine ⟨4221115473986060625781687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22512615861258990004168997 4221115473986060625781687)
                      ·
                        rfl

theorem cell23_8220593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_8220593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220593 prefixEnd_8220593 := by exact prefixLift 8220593
  have htrace : WordTrace (prefixWord ++ tailWord_8220593) baseStart_8220593 baseEnd_8220593 := by
    simpa [prefixWord, tailWord_8220593, baseEnd_8220593] using wordTrace_append hprefix tailTrace_8220593
  have hstable : (prefixWord ++ tailWord_8220593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220593).length < 2 ^ (prefixWord ++ tailWord_8220593).sum := by decide
  have hdescent : baseEnd_8220593 < baseStart_8220593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220604 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_8220604 : Nat := 118140960795 + 8220604 * 2 ^ 59
def prefixEnd_8220604 : Nat := 4983230072969 + 3 ^ 40 * 8220604 * 2
def baseEnd_8220604 : Nat := 4221121122273260082744137

theorem tailTrace_8220604 : CollatzResearch.WordTrace tailWord_8220604 prefixEnd_8220604 4221121122273260082744137 := by
  unfold tailWord_8220604
  simp only [CollatzResearch.WordTrace]
  refine ⟨149915029955081575116378433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199886706606775433488504577 149915029955081575116378433)
  ·
    refine ⟨112436272466311181337283825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149915029955081575116378433 112436272466311181337283825)
    ·
      refine ⟨84327204349733386002962869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112436272466311181337283825 84327204349733386002962869)
      ·
        refine ⟨7905675407787504937777769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84327204349733386002962869 7905675407787504937777769)
        ·
          refine ⟨5929256555840628703333327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7905675407787504937777769 5929256555840628703333327)
          ·
            refine ⟨8893884833760943054999991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929256555840628703333327 8893884833760943054999991)
            ·
              refine ⟨13340827250641414582499987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8893884833760943054999991 13340827250641414582499987)
              ·
                refine ⟨20011240875962121873749981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340827250641414582499987 20011240875962121873749981)
                ·
                  refine ⟨7504215328485795702656243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20011240875962121873749981 7504215328485795702656243)
                  ·
                    refine ⟨11256322992728693553984365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504215328485795702656243 11256322992728693553984365)
                    ·
                      refine ⟨4221121122273260082744137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256322992728693553984365 4221121122273260082744137)
                      ·
                        rfl

theorem cell23_8220604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_8220604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220604 prefixEnd_8220604 := by exact prefixLift 8220604
  have htrace : WordTrace (prefixWord ++ tailWord_8220604) baseStart_8220604 baseEnd_8220604 := by
    simpa [prefixWord, tailWord_8220604, baseEnd_8220604] using wordTrace_append hprefix tailTrace_8220604
  have hstable : (prefixWord ++ tailWord_8220604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220604).length < 2 ^ (prefixWord ++ tailWord_8220604).sum := by decide
  have hdescent : baseEnd_8220604 < baseStart_8220604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220606 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_8220606 : Nat := 118140960795 + 8220606 * 2 ^ 59
def prefixEnd_8220606 : Nat := 4983230072969 + 3 ^ 40 * 8220606 * 2
def baseEnd_8220606 : Nat := 4221122149234569074919127

theorem tailTrace_8220606 : CollatzResearch.WordTrace tailWord_8220606 prefixEnd_8220606 4221122149234569074919127 := by
  unfold tailWord_8220606
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478766607019488071791209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199886755237437269716219781 37478766607019488071791209)
  ·
    refine ⟨28109074955264616053843407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37478766607019488071791209 28109074955264616053843407)
    ·
      refine ⟨42163612432896924080765111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28109074955264616053843407 42163612432896924080765111)
      ·
        refine ⟨63245418649345386121147667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42163612432896924080765111 63245418649345386121147667)
        ·
          refine ⟨94868127974018079181721501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63245418649345386121147667 94868127974018079181721501)
          ·
            refine ⟨35575547990256779693145563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94868127974018079181721501 35575547990256779693145563)
            ·
              refine ⟨53363321985385169539718345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35575547990256779693145563 53363321985385169539718345)
              ·
                refine ⟨40022491489038877154788759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53363321985385169539718345 40022491489038877154788759)
                ·
                  refine ⟨60033737233558315732183139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40022491489038877154788759 60033737233558315732183139)
                  ·
                    refine ⟨90050605850337473598274709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60033737233558315732183139 90050605850337473598274709)
                    ·
                      refine ⟨4221122149234569074919127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90050605850337473598274709 4221122149234569074919127)
                      ·
                        rfl

theorem cell23_8220606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_8220606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220606 prefixEnd_8220606 := by exact prefixLift 8220606
  have htrace : WordTrace (prefixWord ++ tailWord_8220606) baseStart_8220606 baseEnd_8220606 := by
    simpa [prefixWord, tailWord_8220606, baseEnd_8220606] using wordTrace_append hprefix tailTrace_8220606
  have hstable : (prefixWord ++ tailWord_8220606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220606).length < 2 ^ (prefixWord ++ tailWord_8220606).sum := by decide
  have hdescent : baseEnd_8220606 < baseStart_8220606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220616 : List Nat := [2, 1, 3, 1, 4, 2, 2, 8]
def baseStart_8220616 : Nat := 118140960795 + 8220616 * 2 ^ 59
def prefixEnd_8220616 : Nat := 4983230072969 + 3 ^ 40 * 8220616 * 2
def baseEnd_8220616 : Nat := 156338047557078297622003

theorem tailTrace_8220616 : CollatzResearch.WordTrace tailWord_8220616 prefixEnd_8220616 156338047557078297622003 := by
  unfold tailWord_8220616
  simp only [CollatzResearch.WordTrace]
  refine ⟨149915248793059838141096851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199886998390746450854795801 149915248793059838141096851)
  ·
    refine ⟨224872873189589757211645277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149915248793059838141096851 224872873189589757211645277)
    ·
      refine ⟨84327327446096158954366979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224872873189589757211645277 84327327446096158954366979)
      ·
        refine ⟨126490991169144238431550469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84327327446096158954366979 126490991169144238431550469)
        ·
          refine ⟨23717060844214544705915713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126490991169144238431550469 23717060844214544705915713)
          ·
            refine ⟨17787795633160908529436785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23717060844214544705915713 17787795633160908529436785)
            ·
              refine ⟨13340846724870681397077589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17787795633160908529436785 13340846724870681397077589)
              ·
                refine ⟨156338047557078297622003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13340846724870681397077589 156338047557078297622003)
                ·
                  rfl

theorem cell23_8220616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 8].length) (baseStart_8220616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220616 prefixEnd_8220616 := by exact prefixLift 8220616
  have htrace : WordTrace (prefixWord ++ tailWord_8220616) baseStart_8220616 baseEnd_8220616 := by
    simpa [prefixWord, tailWord_8220616, baseEnd_8220616] using wordTrace_append hprefix tailTrace_8220616
  have hstable : (prefixWord ++ tailWord_8220616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220616).length < 2 ^ (prefixWord ++ tailWord_8220616).sum := by decide
  have hdescent : baseEnd_8220616 < baseStart_8220616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220619 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_8220619 : Nat := 118140960795 + 8220619 * 2 ^ 59
def prefixEnd_8220619 : Nat := 4983230072969 + 3 ^ 40 * 8220619 * 2
def baseEnd_8220619 : Nat := 4221128824483077524056567

theorem tailTrace_8220619 : CollatzResearch.WordTrace tailWord_8220619 prefixEnd_8220619 4221128824483077524056567 := by
  unfold tailWord_8220619
  simp only [CollatzResearch.WordTrace]
  refine ⟨299830607005108807794552911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199887071336739205196368607 299830607005108807794552911)
  ·
    refine ⟨449745910507663211691829367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299830607005108807794552911 449745910507663211691829367)
    ·
      refine ⟨674618865761494817537744051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449745910507663211691829367 674618865761494817537744051)
      ·
        refine ⟨1011928298642242226306616077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674618865761494817537744051 1011928298642242226306616077)
        ·
          refine ⟨379473111990840834864981029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1011928298642242226306616077 379473111990840834864981029)
          ·
            refine ⟨71151208498282656537183943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379473111990840834864981029 71151208498282656537183943)
            ·
              refine ⟨106726812747423984805775915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71151208498282656537183943 106726812747423984805775915)
              ·
                refine ⟨160090219121135977208663873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106726812747423984805775915 160090219121135977208663873)
                ·
                  refine ⟨120067664340851982906497905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160090219121135977208663873 120067664340851982906497905)
                  ·
                    refine ⟨90050748255638987179873429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120067664340851982906497905 90050748255638987179873429)
                    ·
                      refine ⟨4221128824483077524056567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90050748255638987179873429 4221128824483077524056567)
                      ·
                        rfl

theorem cell23_8220619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_8220619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220619 prefixEnd_8220619 := by exact prefixLift 8220619
  have htrace : WordTrace (prefixWord ++ tailWord_8220619) baseStart_8220619 baseEnd_8220619 := by
    simpa [prefixWord, tailWord_8220619, baseEnd_8220619] using wordTrace_append hprefix tailTrace_8220619
  have hstable : (prefixWord ++ tailWord_8220619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220619).length < 2 ^ (prefixWord ++ tailWord_8220619).sum := by decide
  have hdescent : baseEnd_8220619 < baseStart_8220619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220620 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_8220620 : Nat := 118140960795 + 8220620 * 2 ^ 59
def prefixEnd_8220620 : Nat := 4983230072969 + 3 ^ 40 * 8220620 * 2
def baseEnd_8220620 : Nat := 1407043112654577340048021

theorem tailTrace_8220620 : CollatzResearch.WordTrace tailWord_8220620 prefixEnd_8220620 1407043112654577340048021 := by
  unfold tailWord_8220620
  simp only [CollatzResearch.WordTrace]
  refine ⟨149915321739052592482669657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199887095652070123310226209 149915321739052592482669657)
  ·
    refine ⟨112436491304289444362002243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149915321739052592482669657 112436491304289444362002243)
    ·
      refine ⟨168654736956434166543003365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112436491304289444362002243 168654736956434166543003365)
      ·
        refine ⟨31622763179331406226813131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168654736956434166543003365 31622763179331406226813131)
        ·
          refine ⟨47434144768997109340219697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31622763179331406226813131 47434144768997109340219697)
          ·
            refine ⟨35575608576747832005164773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47434144768997109340219697 35575608576747832005164773)
            ·
              refine ⟨6670426608140218500968395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35575608576747832005164773 6670426608140218500968395)
              ·
                refine ⟨10005639912210327751452593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670426608140218500968395 10005639912210327751452593)
                ·
                  refine ⟨7504229934157745813589445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10005639912210327751452593 7504229934157745813589445)
                  ·
                    refine ⟨1407043112654577340048021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504229934157745813589445 1407043112654577340048021)
                    ·
                      rfl

theorem cell23_8220620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_8220620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220620 prefixEnd_8220620 := by exact prefixLift 8220620
  have htrace : WordTrace (prefixWord ++ tailWord_8220620) baseStart_8220620 baseEnd_8220620 := by
    simpa [prefixWord, tailWord_8220620, baseEnd_8220620] using wordTrace_append hprefix tailTrace_8220620
  have hstable : (prefixWord ++ tailWord_8220620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220620).length < 2 ^ (prefixWord ++ tailWord_8220620).sum := by decide
  have hdescent : baseEnd_8220620 < baseStart_8220620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220643 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 3]
def baseStart_8220643 : Nat := 118140960795 + 8220643 * 2 ^ 59
def prefixEnd_8220643 : Nat := 4983230072969 + 3 ^ 40 * 8220643 * 2
def baseEnd_8220643 : Nat := 4221141148018785430156457

theorem tailTrace_8220643 : CollatzResearch.WordTrace tailWord_8220643 prefixEnd_8220643 4221141148018785430156457 := by
  unfold tailWord_8220643
  simp only [CollatzResearch.WordTrace]
  refine ⟨299831482357021859893426583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199887654904681239928951055 299831482357021859893426583)
  ·
    refine ⟨449747223535532789840139875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299831482357021859893426583 449747223535532789840139875)
    ·
      refine ⟨674620835303299184760209813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449747223535532789840139875 674620835303299184760209813)
      ·
        refine ⟨31622851654842149285634835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 674620835303299184760209813 31622851654842149285634835)
        ·
          refine ⟨47434277482263223928452253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31622851654842149285634835 47434277482263223928452253)
          ·
            refine ⟨17787854055848708973169595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47434277482263223928452253 17787854055848708973169595)
            ·
              refine ⟨26681781083773063459754393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17787854055848708973169595 26681781083773063459754393)
              ·
                refine ⟨20011335812829797594815795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26681781083773063459754393 20011335812829797594815795)
                ·
                  refine ⟨30017003719244696392223693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20011335812829797594815795 30017003719244696392223693)
                  ·
                    refine ⟨11256376394716761147083885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30017003719244696392223693 11256376394716761147083885)
                    ·
                      refine ⟨4221141148018785430156457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256376394716761147083885 4221141148018785430156457)
                      ·
                        rfl

theorem cell23_8220643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_8220643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220643 prefixEnd_8220643 := by exact prefixLift 8220643
  have htrace : WordTrace (prefixWord ++ tailWord_8220643) baseStart_8220643 baseEnd_8220643 := by
    simpa [prefixWord, tailWord_8220643, baseEnd_8220643] using wordTrace_append hprefix tailTrace_8220643
  have hstable : (prefixWord ++ tailWord_8220643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220643).length < 2 ^ (prefixWord ++ tailWord_8220643).sum := by decide
  have hdescent : baseEnd_8220643 < baseStart_8220643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220647 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_8220647 : Nat := 118140960795 + 8220647 * 2 ^ 59
def prefixEnd_8220647 : Nat := 4983230072969 + 3 ^ 40 * 8220647 * 2
def baseEnd_8220647 : Nat := 4221143201941403414506439

theorem tailTrace_8220647 : CollatzResearch.WordTrace tailWord_8220647 prefixEnd_8220647 4221143201941403414506439 := by
  unfold tailWord_8220647
  simp only [CollatzResearch.WordTrace]
  refine ⟨299831628249007368576572195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199887752166004912384381463 299831628249007368576572195)
  ·
    refine ⟨449747442373511052864858293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299831628249007368576572195 449747442373511052864858293)
    ·
      refine ⟨42163822722516661206080465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449747442373511052864858293 42163822722516661206080465)
      ·
        refine ⟨31622867041887495904560349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42163822722516661206080465 31622867041887495904560349)
        ·
          refine ⟨11858575140707810964210131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31622867041887495904560349 11858575140707810964210131)
          ·
            refine ⟨17787862711061716446315197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858575140707810964210131 17787862711061716446315197)
            ·
              refine ⟨6670448516648143667368199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17787862711061716446315197 6670448516648143667368199)
              ·
                refine ⟨10005672774972215501052299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670448516648143667368199 10005672774972215501052299)
                ·
                  refine ⟨15008509162458323251578449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10005672774972215501052299 15008509162458323251578449)
                  ·
                    refine ⟨11256381871843742438683837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15008509162458323251578449 11256381871843742438683837)
                    ·
                      refine ⟨4221143201941403414506439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256381871843742438683837 4221143201941403414506439)
                      ·
                        rfl

theorem cell23_8220647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_8220647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220647 prefixEnd_8220647 := by exact prefixLift 8220647
  have htrace : WordTrace (prefixWord ++ tailWord_8220647) baseStart_8220647 baseEnd_8220647 := by
    simpa [prefixWord, tailWord_8220647, baseEnd_8220647] using wordTrace_append hprefix tailTrace_8220647
  have hstable : (prefixWord ++ tailWord_8220647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220647).length < 2 ^ (prefixWord ++ tailWord_8220647).sum := by decide
  have hdescent : baseEnd_8220647 < baseStart_8220647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220659 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 8]
def baseStart_8220659 : Nat := 118140960795 + 8220659 * 2 ^ 59
def prefixEnd_8220659 : Nat := 4983230072969 + 3 ^ 40 * 8220659 * 2
def baseEnd_8220659 : Nat := 1407049787903085789185461

theorem tailTrace_8220659 : CollatzResearch.WordTrace tailWord_8220659 prefixEnd_8220659 1407049787903085789185461 := by
  unfold tailWord_8220659
  simp only [CollatzResearch.WordTrace]
  refine ⟨299832065924963894626009031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199888043949975929750672687 299832065924963894626009031)
  ·
    refine ⟨449748098887445841939013547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299832065924963894626009031 449748098887445841939013547)
    ·
      refine ⟨674622148331168762908520321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449748098887445841939013547 674622148331168762908520321)
      ·
        refine ⟨505966611248376572181390241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674622148331168762908520321 505966611248376572181390241)
        ·
          refine ⟨379474958436282429136042681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505966611248376572181390241 379474958436282429136042681)
          ·
            refine ⟨284606218827211821852032011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379474958436282429136042681 284606218827211821852032011)
            ·
              refine ⟨426909328240817732778048017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284606218827211821852032011 426909328240817732778048017)
              ·
                refine ⟨320181996180613299583536013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426909328240817732778048017 320181996180613299583536013)
                ·
                  refine ⟨120068248567729987343826005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320181996180613299583536013 120068248567729987343826005)
                  ·
                    refine ⟨1407049787903085789185461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120068248567729987343826005 1407049787903085789185461)
                    ·
                      rfl

theorem cell23_8220659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_8220659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220659 prefixEnd_8220659 := by exact prefixLift 8220659
  have htrace : WordTrace (prefixWord ++ tailWord_8220659) baseStart_8220659 baseEnd_8220659 := by
    simpa [prefixWord, tailWord_8220659, baseEnd_8220659] using wordTrace_append hprefix tailTrace_8220659
  have hstable : (prefixWord ++ tailWord_8220659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220659).length < 2 ^ (prefixWord ++ tailWord_8220659).sum := by decide
  have hdescent : baseEnd_8220659 < baseStart_8220659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220678 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_8220678 : Nat := 118140960795 + 8220678 * 2 ^ 59
def prefixEnd_8220678 : Nat := 4983230072969 + 3 ^ 40 * 8220678 * 2
def baseEnd_8220678 : Nat := 4221159119841692793218797

theorem tailTrace_8220678 : CollatzResearch.WordTrace tailWord_8220678 prefixEnd_8220678 4221159119841692793218797 := by
  unfold tailWord_8220678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369773715996720652217209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199888505941263373913967125 9369773715996720652217209)
  ·
    refine ⟨7027330286997540489162907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9369773715996720652217209 7027330286997540489162907)
    ·
      refine ⟨10540995430496310733744361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027330286997540489162907 10540995430496310733744361)
      ·
        refine ⟨7905746572872233050308271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10540995430496310733744361 7905746572872233050308271)
        ·
          refine ⟨11858619859308349575462407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905746572872233050308271 11858619859308349575462407)
          ·
            refine ⟨17787929788962524363193611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858619859308349575462407 17787929788962524363193611)
            ·
              refine ⟨26681894683443786544790417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17787929788962524363193611 26681894683443786544790417)
              ·
                refine ⟨20011421012582839908592813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26681894683443786544790417 20011421012582839908592813)
                ·
                  refine ⟨7504282879718564965722305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20011421012582839908592813 7504282879718564965722305)
                  ·
                    refine ⟨5628212159788923724291729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7504282879718564965722305 5628212159788923724291729)
                    ·
                      refine ⟨4221159119841692793218797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628212159788923724291729 4221159119841692793218797)
                      ·
                        rfl

theorem cell23_8220678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_8220678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220678 prefixEnd_8220678 := by exact prefixLift 8220678
  have htrace : WordTrace (prefixWord ++ tailWord_8220678) baseStart_8220678 baseEnd_8220678 := by
    simpa [prefixWord, tailWord_8220678, baseEnd_8220678] using wordTrace_append hprefix tailTrace_8220678
  have hstable : (prefixWord ++ tailWord_8220678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220678).length < 2 ^ (prefixWord ++ tailWord_8220678).sum := by decide
  have hdescent : baseEnd_8220678 < baseStart_8220678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220696 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_8220696 : Nat := 118140960795 + 8220696 * 2 ^ 59
def prefixEnd_8220696 : Nat := 4983230072969 + 3 ^ 40 * 8220696 * 2
def baseEnd_8220696 : Nat := 4221168362493473722793713

theorem tailTrace_8220696 : CollatzResearch.WordTrace tailWord_8220696 prefixEnd_8220696 4221168362493473722793713 := by
  unfold tailWord_8220696
  simp only [CollatzResearch.WordTrace]
  refine ⟨149916707712914924972552971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199888943617219899963403961 149916707712914924972552971)
  ·
    refine ⟨224875061569372387458829457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149916707712914924972552971 224875061569372387458829457)
    ·
      refine ⟨168656296177029290594122093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224875061569372387458829457 168656296177029290594122093)
      ·
        refine ⟨63246111066385983972795785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168656296177029290594122093 63246111066385983972795785)
        ·
          refine ⟨47434583299789487979596839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63246111066385983972795785 47434583299789487979596839)
          ·
            refine ⟨71151874949684231969395259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47434583299789487979596839 71151874949684231969395259)
            ·
              refine ⟨106727812424526347954092889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71151874949684231969395259 106727812424526347954092889)
              ·
                refine ⟨80045859318394760965569667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106727812424526347954092889 80045859318394760965569667)
                ·
                  refine ⟨120068788977592141448354501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80045859318394760965569667 120068788977592141448354501)
                  ·
                    refine ⟨22512897933298526521566469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120068788977592141448354501 22512897933298526521566469)
                    ·
                      refine ⟨4221168362493473722793713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22512897933298526521566469 4221168362493473722793713)
                      ·
                        rfl

theorem cell23_8220696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_8220696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220696 prefixEnd_8220696 := by exact prefixLift 8220696
  have htrace : WordTrace (prefixWord ++ tailWord_8220696) baseStart_8220696 baseEnd_8220696 := by
    simpa [prefixWord, tailWord_8220696, baseEnd_8220696] using wordTrace_append hprefix tailTrace_8220696
  have hstable : (prefixWord ++ tailWord_8220696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220696).length < 2 ^ (prefixWord ++ tailWord_8220696).sum := by decide
  have hdescent : baseEnd_8220696 < baseStart_8220696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220700 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_8220700 : Nat := 118140960795 + 8220700 * 2 ^ 59
def prefixEnd_8220700 : Nat := 4983230072969 + 3 ^ 40 * 8220700 * 2
def baseEnd_8220700 : Nat := 4221170416416091707143695

theorem tailTrace_8220700 : CollatzResearch.WordTrace tailWord_8220700 prefixEnd_8220700 4221170416416091707143695 := by
  unfold tailWord_8220700
  simp only [CollatzResearch.WordTrace]
  refine ⟨149916780658907679314125777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199889040878543572418834369 149916780658907679314125777)
  ·
    refine ⟨112437585494180759485594333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149916780658907679314125777 112437585494180759485594333)
    ·
      refine ⟨42164094560317784807097875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112437585494180759485594333 42164094560317784807097875)
      ·
        refine ⟨63246141840476677210646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42164094560317784807097875 63246141840476677210646813)
        ·
          refine ⟨23717303190178753953992555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63246141840476677210646813 23717303190178753953992555)
          ·
            refine ⟨35575954785268130930988833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23717303190178753953992555 35575954785268130930988833)
            ·
              refine ⟨26681966088951098198241625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35575954785268130930988833 26681966088951098198241625)
              ·
                refine ⟨20011474566713323648681219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26681966088951098198241625 20011474566713323648681219)
                ·
                  refine ⟨30017211850069985473021829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20011474566713323648681219 30017211850069985473021829)
                  ·
                    refine ⟨5628227221888122276191593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30017211850069985473021829 5628227221888122276191593)
                    ·
                      refine ⟨4221170416416091707143695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628227221888122276191593 4221170416416091707143695)
                      ·
                        rfl

theorem cell23_8220700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_8220700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220700 prefixEnd_8220700 := by exact prefixLift 8220700
  have htrace : WordTrace (prefixWord ++ tailWord_8220700) baseStart_8220700 baseEnd_8220700 := by
    simpa [prefixWord, tailWord_8220700, baseEnd_8220700] using wordTrace_append hprefix tailTrace_8220700
  have hstable : (prefixWord ++ tailWord_8220700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220700).length < 2 ^ (prefixWord ++ tailWord_8220700).sum := by decide
  have hdescent : baseEnd_8220700 < baseStart_8220700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220706 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_8220706 : Nat := 118140960795 + 8220706 * 2 ^ 59
def prefixEnd_8220706 : Nat := 4983230072969 + 3 ^ 40 * 8220706 * 2
def baseEnd_8220706 : Nat := 469019277477779853740963

theorem tailTrace_8220706 : CollatzResearch.WordTrace tailWord_8220706 prefixEnd_8220706 469019277477779853740963 := by
  unfold tailWord_8220706
  simp only [CollatzResearch.WordTrace]
  refine ⟨74958445038948405413242493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199889186770529081101979981 74958445038948405413242493)
  ·
    refine ⟨28109416889605652029965935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74958445038948405413242493 28109416889605652029965935)
    ·
      refine ⟨42164125334408478044948903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28109416889605652029965935 42164125334408478044948903)
      ·
        refine ⟨63246188001612717067423355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42164125334408478044948903 63246188001612717067423355)
        ·
          refine ⟨94869282002419075601135033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63246188001612717067423355 94869282002419075601135033)
          ·
            refine ⟨71151961501814306700851275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94869282002419075601135033 71151961501814306700851275)
            ·
              refine ⟨106727942252721460051276913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71151961501814306700851275 106727942252721460051276913)
              ·
                refine ⟨80045956689541095038457685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106727942252721460051276913 80045956689541095038457685)
                ·
                  refine ⟨469019277477779853740963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80045956689541095038457685 469019277477779853740963)
                  ·
                    rfl

theorem cell23_8220706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_8220706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220706 prefixEnd_8220706 := by exact prefixLift 8220706
  have htrace : WordTrace (prefixWord ++ tailWord_8220706) baseStart_8220706 baseEnd_8220706 := by
    simpa [prefixWord, tailWord_8220706, baseEnd_8220706] using wordTrace_append hprefix tailTrace_8220706
  have hstable : (prefixWord ++ tailWord_8220706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220706).length < 2 ^ (prefixWord ++ tailWord_8220706).sum := by decide
  have hdescent : baseEnd_8220706 < baseStart_8220706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220711 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_8220711 : Nat := 118140960795 + 8220711 * 2 ^ 59
def prefixEnd_8220711 : Nat := 4983230072969 + 3 ^ 40 * 8220711 * 2
def baseEnd_8220711 : Nat := 4221176064703291164106145

theorem tailTrace_8220711 : CollatzResearch.WordTrace tailWord_8220711 prefixEnd_8220711 4221176064703291164106145 := by
  unfold tailWord_8220711
  simp only [CollatzResearch.WordTrace]
  refine ⟨299833962520775507506901987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199889308347183671671267991 299833962520775507506901987)
  ·
    refine ⟨449750943781163261260352981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299833962520775507506901987 449750943781163261260352981)
    ·
      refine ⟨10541037744871013935789523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 449750943781163261260352981 10541037744871013935789523)
      ·
        refine ⟨15811556617306520903684285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10541037744871013935789523 15811556617306520903684285)
        ·
          refine ⟨5929333731489945338881607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15811556617306520903684285 5929333731489945338881607)
          ·
            refine ⟨8894000597234918008322411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929333731489945338881607 8894000597234918008322411)
            ·
              refine ⟨13341000895852377012483617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8894000597234918008322411 13341000895852377012483617)
              ·
                refine ⟨10005750671889282759362713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13341000895852377012483617 10005750671889282759362713)
                ·
                  refine ⟨7504313003916962069522035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10005750671889282759362713 7504313003916962069522035)
                  ·
                    refine ⟨11256469505875443104283053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504313003916962069522035 11256469505875443104283053)
                    ·
                      refine ⟨4221176064703291164106145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256469505875443104283053 4221176064703291164106145)
                      ·
                        rfl

theorem cell23_8220711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_8220711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220711 prefixEnd_8220711 := by exact prefixLift 8220711
  have htrace : WordTrace (prefixWord ++ tailWord_8220711) baseStart_8220711 baseEnd_8220711 := by
    simpa [prefixWord, tailWord_8220711, baseEnd_8220711] using wordTrace_append hprefix tailTrace_8220711
  have hstable : (prefixWord ++ tailWord_8220711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220711).length < 2 ^ (prefixWord ++ tailWord_8220711).sum := by decide
  have hdescent : baseEnd_8220711 < baseStart_8220711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220723 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 5]
def baseStart_8220723 : Nat := 118140960795 + 8220723 * 2 ^ 59
def prefixEnd_8220723 : Nat := 4983230072969 + 3 ^ 40 * 8220723 * 2
def baseEnd_8220723 : Nat := 469020247385682790795121

theorem tailTrace_8220723 : CollatzResearch.WordTrace tailWord_8220723 prefixEnd_8220723 469020247385682790795121 := by
  unfold tailWord_8220723
  simp only [CollatzResearch.WordTrace]
  refine ⟨299834400196732033556338823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199889600131154689037559215 299834400196732033556338823)
  ·
    refine ⟨449751600295098050334508235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299834400196732033556338823 449751600295098050334508235)
    ·
      refine ⟨674627400442647075501762353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449751600295098050334508235 674627400442647075501762353)
      ·
        refine ⟨505970550331985306626321765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674627400442647075501762353 505970550331985306626321765)
        ·
          refine ⟨94869478187247244992435331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505970550331985306626321765 94869478187247244992435331)
          ·
            refine ⟨142304217280870867488652997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94869478187247244992435331 142304217280870867488652997)
            ·
              refine ⟨26682040740163287654122437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142304217280870867488652997 26682040740163287654122437)
              ·
                refine ⟨5002882638780616435147957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26682040740163287654122437 5002882638780616435147957)
                ·
                  refine ⟨469020247385682790795121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5002882638780616435147957 469020247385682790795121)
                  ·
                    rfl

theorem cell23_8220723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 5].length) (baseStart_8220723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220723 prefixEnd_8220723 := by exact prefixLift 8220723
  have htrace : WordTrace (prefixWord ++ tailWord_8220723) baseStart_8220723 baseEnd_8220723 := by
    simpa [prefixWord, tailWord_8220723, baseEnd_8220723] using wordTrace_append hprefix tailTrace_8220723
  have hstable : (prefixWord ++ tailWord_8220723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220723).length < 2 ^ (prefixWord ++ tailWord_8220723).sum := by decide
  have hdescent : baseEnd_8220723 < baseStart_8220723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220733 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_8220733 : Nat := 118140960795 + 8220733 * 2 ^ 59
def prefixEnd_8220733 : Nat := 4983230072969 + 3 ^ 40 * 8220733 * 2
def baseEnd_8220733 : Nat := 4221187361277690078031043

theorem tailTrace_8220733 : CollatzResearch.WordTrace tailWord_8220733 prefixEnd_8220733 4221187361277690078031043 := by
  unfold tailWord_8220733
  simp only [CollatzResearch.WordTrace]
  refine ⟨299834764926695805264202853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199889843284463870176135235 299834764926695805264202853)
  ·
    refine ⟨56219018423755463487038035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299834764926695805264202853 56219018423755463487038035)
    ·
      refine ⟨84328527635633195230557053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56219018423755463487038035 84328527635633195230557053)
      ·
        refine ⟨31623197863362448211458895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84328527635633195230557053 31623197863362448211458895)
        ·
          refine ⟨47434796795043672317188343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31623197863362448211458895 47434796795043672317188343)
          ·
            refine ⟨71152195192565508475782515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47434796795043672317188343 71152195192565508475782515)
            ·
              refine ⟨106728292788848262713673773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71152195192565508475782515 106728292788848262713673773)
              ·
                refine ⟨40023109795818098517627665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106728292788848262713673773 40023109795818098517627665)
                ·
                  refine ⟨30017332346863573888220749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40023109795818098517627665 30017332346863573888220749)
                  ·
                    refine ⟨11256499630073840208082781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30017332346863573888220749 11256499630073840208082781)
                    ·
                      refine ⟨4221187361277690078031043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256499630073840208082781 4221187361277690078031043)
                      ·
                        rfl

theorem cell23_8220733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_8220733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220733 prefixEnd_8220733 := by exact prefixLift 8220733
  have htrace : WordTrace (prefixWord ++ tailWord_8220733) baseStart_8220733 baseEnd_8220733 := by
    simpa [prefixWord, tailWord_8220733, baseEnd_8220733] using wordTrace_append hprefix tailTrace_8220733
  have hstable : (prefixWord ++ tailWord_8220733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220733).length < 2 ^ (prefixWord ++ tailWord_8220733).sum := by decide
  have hdescent : baseEnd_8220733 < baseStart_8220733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220734 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_8220734 : Nat := 118140960795 + 8220734 * 2 ^ 59
def prefixEnd_8220734 : Nat := 4983230072969 + 3 ^ 40 * 8220734 * 2
def baseEnd_8220734 : Nat := 4221187874758344574118539

theorem tailTrace_8220734 : CollatzResearch.WordTrace tailWord_8220734 prefixEnd_8220734 4221187874758344574118539 := by
  unfold tailWord_8220734
  simp only [CollatzResearch.WordTrace]
  refine ⟨37479350174961522804373657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199889867599794788289992837 37479350174961522804373657)
  ·
    refine ⟨28109512631221142103280243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37479350174961522804373657 28109512631221142103280243)
    ·
      refine ⟨42164268946831713154920365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28109512631221142103280243 42164268946831713154920365)
      ·
        refine ⟨15811600855061892433095137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42164268946831713154920365 15811600855061892433095137)
        ·
          refine ⟨11858700641296419324821353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15811600855061892433095137 11858700641296419324821353)
          ·
            refine ⟨8894025480972314493616015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11858700641296419324821353 8894025480972314493616015)
            ·
              refine ⟨13341038221458471740424023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8894025480972314493616015 13341038221458471740424023)
              ·
                refine ⟨20011557332187707610636035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13341038221458471740424023 20011557332187707610636035)
                ·
                  refine ⟨30017335998281561415954053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20011557332187707610636035 30017335998281561415954053)
                  ·
                    refine ⟨5628250499677792765491385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30017335998281561415954053 5628250499677792765491385)
                    ·
                      refine ⟨4221187874758344574118539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628250499677792765491385 4221187874758344574118539)
                      ·
                        rfl

theorem cell23_8220734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_8220734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220734 prefixEnd_8220734 := by exact prefixLift 8220734
  have htrace : WordTrace (prefixWord ++ tailWord_8220734) baseStart_8220734 baseEnd_8220734 := by
    simpa [prefixWord, tailWord_8220734, baseEnd_8220734] using wordTrace_append hprefix tailTrace_8220734
  have hstable : (prefixWord ++ tailWord_8220734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220734).length < 2 ^ (prefixWord ++ tailWord_8220734).sum := by decide
  have hdescent : baseEnd_8220734 < baseStart_8220734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220736 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_8220736 : Nat := 118140960795 + 8220736 * 2 ^ 59
def prefixEnd_8220736 : Nat := 4983230072969 + 3 ^ 40 * 8220736 * 2
def baseEnd_8220736 : Nat := 1407062967239884522097843

theorem tailTrace_8220736 : CollatzResearch.WordTrace tailWord_8220736 prefixEnd_8220736 1407062967239884522097843 := by
  unfold tailWord_8220736
  simp only [CollatzResearch.WordTrace]
  refine ⟨149917437172842468388281031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199889916230456624517708041 149917437172842468388281031)
  ·
    refine ⟨224876155759263702582421547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149917437172842468388281031 224876155759263702582421547)
    ·
      refine ⟨337314233638895553873632321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224876155759263702582421547 337314233638895553873632321)
      ·
        refine ⟨252985675229171665405224241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337314233638895553873632321 252985675229171665405224241)
        ·
          refine ⟨189739256421878749053918181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252985675229171665405224241 189739256421878749053918181)
          ·
            refine ⟨35576110579102265447609659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189739256421878749053918181 35576110579102265447609659)
            ·
              refine ⟨53364165868653398171414489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35576110579102265447609659 53364165868653398171414489)
              ·
                refine ⟨40023124401490048628560867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53364165868653398171414489 40023124401490048628560867)
                ·
                  refine ⟨60034686602235072942841301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40023124401490048628560867 60034686602235072942841301)
                  ·
                    refine ⟨1407062967239884522097843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60034686602235072942841301 1407062967239884522097843)
                    ·
                      rfl

theorem cell23_8220736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_8220736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220736 prefixEnd_8220736 := by exact prefixLift 8220736
  have htrace : WordTrace (prefixWord ++ tailWord_8220736) baseStart_8220736 baseEnd_8220736 := by
    simpa [prefixWord, tailWord_8220736, baseEnd_8220736] using wordTrace_append hprefix tailTrace_8220736
  have hstable : (prefixWord ++ tailWord_8220736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220736).length < 2 ^ (prefixWord ++ tailWord_8220736).sum := by decide
  have hdescent : baseEnd_8220736 < baseStart_8220736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220746 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_8220746 : Nat := 118140960795 + 8220746 * 2 ^ 59
def prefixEnd_8220746 : Nat := 4983230072969 + 3 ^ 40 * 8220746 * 2
def baseEnd_8220746 : Nat := 4221194036526198527168483

theorem tailTrace_8220746 : CollatzResearch.WordTrace tailWord_8220746 prefixEnd_8220746 4221194036526198527168483 := by
  unfold tailWord_8220746
  simp only [CollatzResearch.WordTrace]
  refine ⟨74958809768912177121106523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199890159383765805656284061 74958809768912177121106523)
  ·
    refine ⟨112438214653368265681659785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74958809768912177121106523 112438214653368265681659785)
    ·
      refine ⟨84328660990026199261244839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112438214653368265681659785 84328660990026199261244839)
      ·
        refine ⟨126492991485039298891867259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84328660990026199261244839 126492991485039298891867259)
        ·
          refine ⟨189739487227558948337800889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126492991485039298891867259 189739487227558948337800889)
          ·
            refine ⟨142304615420669211253350667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189739487227558948337800889 142304615420669211253350667)
            ·
              refine ⟨213456923131003816880026001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142304615420669211253350667 213456923131003816880026001)
              ·
                refine ⟨160092692348252862660019501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213456923131003816880026001 160092692348252862660019501)
                ·
                  refine ⟨60034759630594823497507313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160092692348252862660019501 60034759630594823497507313)
                  ·
                    refine ⟨45026069722946117623130485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60034759630594823497507313 45026069722946117623130485)
                    ·
                      refine ⟨4221194036526198527168483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45026069722946117623130485 4221194036526198527168483)
                      ·
                        rfl

theorem cell23_8220746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_8220746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220746 prefixEnd_8220746 := by exact prefixLift 8220746
  have htrace : WordTrace (prefixWord ++ tailWord_8220746) baseStart_8220746 baseEnd_8220746 := by
    simpa [prefixWord, tailWord_8220746, baseEnd_8220746] using wordTrace_append hprefix tailTrace_8220746
  have hstable : (prefixWord ++ tailWord_8220746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220746).length < 2 ^ (prefixWord ++ tailWord_8220746).sum := by decide
  have hdescent : baseEnd_8220746 < baseStart_8220746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220773 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_8220773 : Nat := 118140960795 + 8220773 * 2 ^ 59
def prefixEnd_8220773 : Nat := 4983230072969 + 3 ^ 40 * 8220773 * 2
def baseEnd_8220773 : Nat := 4221207900503869921530859

theorem tailTrace_8220773 : CollatzResearch.WordTrace tailWord_8220773 prefixEnd_8220773 4221207900503869921530859 := by
  unfold tailWord_8220773
  simp only [CollatzResearch.WordTrace]
  refine ⟨299836223846550892095658973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199890815897700594730439315 299836223846550892095658973)
  ·
    refine ⟨112438583942456584535872115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299836223846550892095658973 112438583942456584535872115)
    ·
      refine ⟨168657875913684876803808173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112438583942456584535872115 168657875913684876803808173)
      ·
        refine ⟨63246703467631828801428065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168657875913684876803808173 63246703467631828801428065)
        ·
          refine ⟨47435027600723871601071049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63246703467631828801428065 47435027600723871601071049)
          ·
            refine ⟨35576270700542903700803287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47435027600723871601071049 35576270700542903700803287)
            ·
              refine ⟨53364406050814355551204931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35576270700542903700803287 53364406050814355551204931)
              ·
                refine ⟨80046609076221533326807397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53364406050814355551204931 80046609076221533326807397)
                ·
                  refine ⟨15008739201791537498776387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80046609076221533326807397 15008739201791537498776387)
                  ·
                    refine ⟨22513108802687306248164581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15008739201791537498776387 22513108802687306248164581)
                    ·
                      refine ⟨4221207900503869921530859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22513108802687306248164581 4221207900503869921530859)
                      ·
                        rfl

theorem cell23_8220773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_8220773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220773 prefixEnd_8220773 := by exact prefixLift 8220773
  have htrace : WordTrace (prefixWord ++ tailWord_8220773) baseStart_8220773 baseEnd_8220773 := by
    simpa [prefixWord, tailWord_8220773, baseEnd_8220773] using wordTrace_append hprefix tailTrace_8220773
  have hstable : (prefixWord ++ tailWord_8220773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220773).length < 2 ^ (prefixWord ++ tailWord_8220773).sum := by decide
  have hdescent : baseEnd_8220773 < baseStart_8220773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220810 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_8220810 : Nat := 118140960795 + 8220810 * 2 ^ 59
def prefixEnd_8220810 : Nat := 4983230072969 + 3 ^ 40 * 8220810 * 2
def baseEnd_8220810 : Nat := 4221226899288086276768189

theorem tailTrace_8220810 : CollatzResearch.WordTrace tailWord_8220810 prefixEnd_8220810 4221226899288086276768189 := by
  unfold tailWord_8220810
  simp only [CollatzResearch.WordTrace]
  refine ⟨74959393336854211853688971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199891715564944564943170589 74959393336854211853688971)
  ·
    refine ⟨112439090005281317780533457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74959393336854211853688971 112439090005281317780533457)
    ·
      refine ⟨84329317503960988335400093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112439090005281317780533457 84329317503960988335400093)
      ·
        refine ⟨31623494063985370625775035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84329317503960988335400093 31623494063985370625775035)
        ·
          refine ⟨47435241095978055938662553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31623494063985370625775035 47435241095978055938662553)
          ·
            refine ⟨35576430821983541953996915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47435241095978055938662553 35576430821983541953996915)
            ·
              refine ⟨53364646232975312930995373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35576430821983541953996915 53364646232975312930995373)
              ·
                refine ⟨20011742337365742349123265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53364646232975312930995373 20011742337365742349123265)
                ·
                  refine ⟨15008806753024306761842449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20011742337365742349123265 15008806753024306761842449)
                  ·
                    refine ⟨11256605064768230071381837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15008806753024306761842449 11256605064768230071381837)
                    ·
                      refine ⟨4221226899288086276768189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256605064768230071381837 4221226899288086276768189)
                      ·
                        rfl

theorem cell23_8220810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_8220810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220810 prefixEnd_8220810 := by exact prefixLift 8220810
  have htrace : WordTrace (prefixWord ++ tailWord_8220810) baseStart_8220810 baseEnd_8220810 := by
    simpa [prefixWord, tailWord_8220810, baseEnd_8220810] using wordTrace_append hprefix tailTrace_8220810
  have hstable : (prefixWord ++ tailWord_8220810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220810).length < 2 ^ (prefixWord ++ tailWord_8220810).sum := by decide
  have hdescent : baseEnd_8220810 < baseStart_8220810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220834 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_8220834 : Nat := 118140960795 + 8220834 * 2 ^ 59
def prefixEnd_8220834 : Nat := 4983230072969 + 3 ^ 40 * 8220834 * 2
def baseEnd_8220834 : Nat := 1407079740941264727622693

theorem tailTrace_8220834 : CollatzResearch.WordTrace tailWord_8220834 prefixEnd_8220834 1407079740941264727622693 := by
  unfold tailWord_8220834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74959612174832474878407389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199892299132886599675753037 74959612174832474878407389)
  ·
    refine ⟨28109854565562178079402771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74959612174832474878407389 28109854565562178079402771)
    ·
      refine ⟨42164781848343267119104157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28109854565562178079402771 42164781848343267119104157)
      ·
        refine ⟨15811793193128725169664059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42164781848343267119104157 15811793193128725169664059)
        ·
          refine ⟨23717689789693087754496089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15811793193128725169664059 23717689789693087754496089)
          ·
            refine ⟨17788267342269815815872067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23717689789693087754496089 17788267342269815815872067)
            ·
              refine ⟨26682401013404723723808101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17788267342269815815872067 26682401013404723723808101)
              ·
                refine ⟨5002950190013385698214019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26682401013404723723808101 5002950190013385698214019)
                ·
                  refine ⟨7504425285020078547321029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002950190013385698214019 7504425285020078547321029)
                  ·
                    refine ⟨1407079740941264727622693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504425285020078547321029 1407079740941264727622693)
                    ·
                      rfl

theorem cell23_8220834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_8220834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220834 prefixEnd_8220834 := by exact prefixLift 8220834
  have htrace : WordTrace (prefixWord ++ tailWord_8220834) baseStart_8220834 baseEnd_8220834 := by
    simpa [prefixWord, tailWord_8220834, baseEnd_8220834] using wordTrace_append hprefix tailTrace_8220834
  have hstable : (prefixWord ++ tailWord_8220834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220834).length < 2 ^ (prefixWord ++ tailWord_8220834).sum := by decide
  have hdescent : baseEnd_8220834 < baseStart_8220834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220850 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_8220850 : Nat := 118140960795 + 8220850 * 2 ^ 59
def prefixEnd_8220850 : Nat := 4983230072969 + 3 ^ 40 * 8220850 * 2
def baseEnd_8220850 : Nat := 4221247438514266120268005

theorem tailTrace_8220850 : CollatzResearch.WordTrace tailWord_8220850 prefixEnd_8220850 4221247438514266120268005 := by
  unfold tailWord_8220850
  simp only [CollatzResearch.WordTrace]
  refine ⟨74959758066817983561553001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199892688178181289497474669 74959758066817983561553001)
  ·
    refine ⟨56219818550113487671164751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74959758066817983561553001 56219818550113487671164751)
    ·
      refine ⟨84329727825170231506747127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56219818550113487671164751 84329727825170231506747127)
      ·
        refine ⟨126494591737755347260120691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84329727825170231506747127 126494591737755347260120691)
        ·
          refine ⟨189741887606633020890181037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126494591737755347260120691 189741887606633020890181037)
          ·
            refine ⟨71153207852487382833817889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189741887606633020890181037 71153207852487382833817889)
            ·
              refine ⟨53364905889365537125363417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71153207852487382833817889 53364905889365537125363417)
              ·
                refine ⟨40023679417024152844022563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53364905889365537125363417 40023679417024152844022563)
                ·
                  refine ⟨60035519125536229266033845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40023679417024152844022563 60035519125536229266033845)
                  ·
                    refine ⟨5628329918019021493690673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60035519125536229266033845 5628329918019021493690673)
                    ·
                      refine ⟨4221247438514266120268005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628329918019021493690673 4221247438514266120268005)
                      ·
                        rfl

theorem cell23_8220850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_8220850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220850 prefixEnd_8220850 := by exact prefixLift 8220850
  have htrace : WordTrace (prefixWord ++ tailWord_8220850) baseStart_8220850 baseEnd_8220850 := by
    simpa [prefixWord, tailWord_8220850, baseEnd_8220850] using wordTrace_append hprefix tailTrace_8220850
  have hstable : (prefixWord ++ tailWord_8220850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220850).length < 2 ^ (prefixWord ++ tailWord_8220850).sum := by decide
  have hdescent : baseEnd_8220850 < baseStart_8220850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220874 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_8220874 : Nat := 118140960795 + 8220874 * 2 ^ 59
def prefixEnd_8220874 : Nat := 4983230072969 + 3 ^ 40 * 8220874 * 2
def baseEnd_8220874 : Nat := 4221259762049974026367895

theorem tailTrace_8220874 : CollatzResearch.WordTrace tailWord_8220874 prefixEnd_8220874 4221259762049974026367895 := by
  unfold tailWord_8220874
  simp only [CollatzResearch.WordTrace]
  refine ⟨74959976904796246586271419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199893271746123324230057117 74959976904796246586271419)
  ·
    refine ⟨112439965357194369879407129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74959976904796246586271419 112439965357194369879407129)
    ·
      refine ⟨84329974017895777409555347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112439965357194369879407129 84329974017895777409555347)
      ·
        refine ⟨126494961026843666114333021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84329974017895777409555347 126494961026843666114333021)
        ·
          refine ⟨47435610385066374792874883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126494961026843666114333021 47435610385066374792874883)
          ·
            refine ⟨71153415577599562189312325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47435610385066374792874883 71153415577599562189312325)
            ·
              refine ⟨13341265420799917910496061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71153415577599562189312325 13341265420799917910496061)
              ·
                refine ⟨5002974532799969216436023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13341265420799917910496061 5002974532799969216436023)
                ·
                  refine ⟨7504461799199953824654035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002974532799969216436023 7504461799199953824654035)
                  ·
                    refine ⟨11256692698799930736981053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504461799199953824654035 11256692698799930736981053)
                    ·
                      refine ⟨4221259762049974026367895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256692698799930736981053 4221259762049974026367895)
                      ·
                        rfl

theorem cell23_8220874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_8220874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220874 prefixEnd_8220874 := by exact prefixLift 8220874
  have htrace : WordTrace (prefixWord ++ tailWord_8220874) baseStart_8220874 baseEnd_8220874 := by
    simpa [prefixWord, tailWord_8220874, baseEnd_8220874] using wordTrace_append hprefix tailTrace_8220874
  have hstable : (prefixWord ++ tailWord_8220874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220874).length < 2 ^ (prefixWord ++ tailWord_8220874).sum := by decide
  have hdescent : baseEnd_8220874 < baseStart_8220874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220907 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 2, 4]
def baseStart_8220907 : Nat := 118140960795 + 8220907 * 2 ^ 59
def prefixEnd_8220907 : Nat := 4983230072969 + 3 ^ 40 * 8220907 * 2
def baseEnd_8220907 : Nat := 1407092235637190799085081

theorem tailTrace_8220907 : CollatzResearch.WordTrace tailWord_8220907 prefixEnd_8220907 1407092235637190799085081 := by
  unfold tailWord_8220907
  simp only [CollatzResearch.WordTrace]
  refine ⟨299841111228065432981036975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199894074152043621987357983 299841111228065432981036975)
  ·
    refine ⟨449761666842098149471555463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299841111228065432981036975 449761666842098149471555463)
    ·
      refine ⟨674642500263147224207333195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449761666842098149471555463 674642500263147224207333195)
      ·
        refine ⟨1011963750394720836310999793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674642500263147224207333195 1011963750394720836310999793)
        ·
          refine ⟨758972812796040627233249845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011963750394720836310999793 758972812796040627233249845)
          ·
            refine ⟨71153701199628808803117173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 758972812796040627233249845 71153701199628808803117173)
            ·
              refine ⟨6670659487465200825292235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71153701199628808803117173 6670659487465200825292235)
              ·
                refine ⟨10005989231197801237938353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670659487465200825292235 10005989231197801237938353)
                ·
                  refine ⟨7504491923398350928453765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10005989231197801237938353 7504491923398350928453765)
                  ·
                    refine ⟨1407092235637190799085081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504491923398350928453765 1407092235637190799085081)
                    ·
                      rfl

theorem cell23_8220907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 4].length) (baseStart_8220907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220907 prefixEnd_8220907 := by exact prefixLift 8220907
  have htrace : WordTrace (prefixWord ++ tailWord_8220907) baseStart_8220907 baseEnd_8220907 := by
    simpa [prefixWord, tailWord_8220907, baseEnd_8220907] using wordTrace_append hprefix tailTrace_8220907
  have hstable : (prefixWord ++ tailWord_8220907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220907).length < 2 ^ (prefixWord ++ tailWord_8220907).sum := by decide
  have hdescent : baseEnd_8220907 < baseStart_8220907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220914 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_8220914 : Nat := 118140960795 + 8220914 * 2 ^ 59
def prefixEnd_8220914 : Nat := 4983230072969 + 3 ^ 40 * 8220914 * 2
def baseEnd_8220914 : Nat := 4221280301276153869867711

theorem tailTrace_8220914 : CollatzResearch.WordTrace tailWord_8220914 prefixEnd_8220914 4221280301276153869867711 := by
  unfold tailWord_8220914
  simp only [CollatzResearch.WordTrace]
  refine ⟨74960341634760018294135449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199894244359360048784361197 74960341634760018294135449)
  ·
    refine ⟨56220256226070013720601587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74960341634760018294135449 56220256226070013720601587)
    ·
      refine ⟨84330384339105020580902381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56220256226070013720601587 84330384339105020580902381)
      ·
        refine ⟨31623894127164382717838393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84330384339105020580902381 31623894127164382717838393)
        ·
          refine ⟨23717920595373287038378795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31623894127164382717838393 23717920595373287038378795)
          ·
            refine ⟨35576880893059930557568193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23717920595373287038378795 35576880893059930557568193)
            ·
              refine ⟨26682660669794947918176145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35576880893059930557568193 26682660669794947918176145)
              ·
                refine ⟨20011995502346210938632109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26682660669794947918176145 20011995502346210938632109)
                ·
                  refine ⟨7504498313379829101987041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20011995502346210938632109 7504498313379829101987041)
                  ·
                    refine ⟨5628373735034871826490281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7504498313379829101987041 5628373735034871826490281)
                    ·
                      refine ⟨4221280301276153869867711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628373735034871826490281 4221280301276153869867711)
                      ·
                        rfl

theorem cell23_8220914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_8220914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220914 prefixEnd_8220914 := by exact prefixLift 8220914
  have htrace : WordTrace (prefixWord ++ tailWord_8220914) baseStart_8220914 baseEnd_8220914 := by
    simpa [prefixWord, tailWord_8220914, baseEnd_8220914] using wordTrace_append hprefix tailTrace_8220914
  have hstable : (prefixWord ++ tailWord_8220914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220914).length < 2 ^ (prefixWord ++ tailWord_8220914).sum := by decide
  have hdescent : baseEnd_8220914 < baseStart_8220914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220958 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_8220958 : Nat := 118140960795 + 8220958 * 2 ^ 59
def prefixEnd_8220958 : Nat := 4983230072969 + 3 ^ 40 * 8220958 * 2
def baseEnd_8220958 : Nat := 1407100964808317232572503

theorem tailTrace_8220958 : CollatzResearch.WordTrace tailWord_8220958 prefixEnd_8220958 1407100964808317232572503 := by
  unfold tailWord_8220958
  simp only [CollatzResearch.WordTrace]
  refine ⟨37480371418860083586392941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199895314233920445794095685 37480371418860083586392941)
  ·
    refine ⟨14055139282072531344897353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37480371418860083586392941 14055139282072531344897353)
    ·
      refine ⟨10541354461554398508673015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14055139282072531344897353 10541354461554398508673015)
      ·
        refine ⟨15812031692331597763009523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10541354461554398508673015 15812031692331597763009523)
        ·
          refine ⟨23718047538497396644514285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15812031692331597763009523 23718047538497396644514285)
          ·
            refine ⟨8894267826936523741692857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23718047538497396644514285 8894267826936523741692857)
            ·
              refine ⟨6670700870202392806269643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8894267826936523741692857 6670700870202392806269643)
              ·
                refine ⟨10006051305303589209404465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670700870202392806269643 10006051305303589209404465)
                ·
                  refine ⟨7504538478977691907053349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006051305303589209404465 7504538478977691907053349)
                  ·
                    refine ⟨1407100964808317232572503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504538478977691907053349 1407100964808317232572503)
                    ·
                      rfl

theorem cell23_8220958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_8220958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220958 prefixEnd_8220958 := by exact prefixLift 8220958
  have htrace : WordTrace (prefixWord ++ tailWord_8220958) baseStart_8220958 baseEnd_8220958 := by
    simpa [prefixWord, tailWord_8220958, baseEnd_8220958] using wordTrace_append hprefix tailTrace_8220958
  have hstable : (prefixWord ++ tailWord_8220958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220958).length < 2 ^ (prefixWord ++ tailWord_8220958).sum := by decide
  have hdescent : baseEnd_8220958 < baseStart_8220958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220963 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 8]
def baseStart_8220963 : Nat := 118140960795 + 8220963 * 2 ^ 59
def prefixEnd_8220963 : Nat := 4983230072969 + 3 ^ 40 * 8220963 * 2
def baseEnd_8220963 : Nat := 1407101820609408059384995

theorem tailTrace_8220963 : CollatzResearch.WordTrace tailWord_8220963 prefixEnd_8220963 1407101820609408059384995 := by
  unfold tailWord_8220963
  simp only [CollatzResearch.WordTrace]
  refine ⟨299843153715862554545075543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199895435810575036363383695 299843153715862554545075543)
  ·
    refine ⟨449764730573793831817613315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299843153715862554545075543 449764730573793831817613315)
    ·
      refine ⟨674647095860690747726419973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449764730573793831817613315 674647095860690747726419973)
      ·
        refine ⟨126496330473879515198703745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 674647095860690747726419973 126496330473879515198703745)
        ·
          refine ⟨94872247855409636399027809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126496330473879515198703745 94872247855409636399027809)
          ·
            refine ⟨71154185891557227299270857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94872247855409636399027809 71154185891557227299270857)
            ·
              refine ⟨53365639418667920474453143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71154185891557227299270857 53365639418667920474453143)
              ·
                refine ⟨80048459128001880711679715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53365639418667920474453143 80048459128001880711679715)
                ·
                  refine ⟨120072688692002821067519573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80048459128001880711679715 120072688692002821067519573)
                  ·
                    refine ⟨1407101820609408059384995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120072688692002821067519573 1407101820609408059384995)
                    ·
                      rfl

theorem cell23_8220963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_8220963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220963 prefixEnd_8220963 := by exact prefixLift 8220963
  have htrace : WordTrace (prefixWord ++ tailWord_8220963) baseStart_8220963 baseEnd_8220963 := by
    simpa [prefixWord, tailWord_8220963, baseEnd_8220963] using wordTrace_append hprefix tailTrace_8220963
  have hstable : (prefixWord ++ tailWord_8220963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220963).length < 2 ^ (prefixWord ++ tailWord_8220963).sum := by decide
  have hdescent : baseEnd_8220963 < baseStart_8220963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8220964 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_8220964 : Nat := 118140960795 + 8220964 * 2 ^ 59
def prefixEnd_8220964 : Nat := 4983230072969 + 3 ^ 40 * 8220964 * 2
def baseEnd_8220964 : Nat := 4221305975308878674242481

theorem tailTrace_8220964 : CollatzResearch.WordTrace tailWord_8220964 prefixEnd_8220964 4221305975308878674242481 := by
  unfold tailWord_8220964
  simp only [CollatzResearch.WordTrace]
  refine ⟨149921595094429465857930973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199895460125905954477241297 149921595094429465857930973)
  ·
    refine ⟨56220598160411049696724115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149921595094429465857930973 56220598160411049696724115)
    ·
      refine ⟨84330897240616574545086173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56220598160411049696724115 84330897240616574545086173)
      ·
        refine ⟨31624086465231215454407315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84330897240616574545086173 31624086465231215454407315)
        ·
          refine ⟨47436129697846823181610973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31624086465231215454407315 47436129697846823181610973)
          ·
            refine ⟨17788548636692558693104115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47436129697846823181610973 17788548636692558693104115)
            ·
              refine ⟨26682822955038838039656173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17788548636692558693104115 26682822955038838039656173)
              ·
                refine ⟨10006058608139564264871065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26682822955038838039656173 10006058608139564264871065)
                ·
                  refine ⟨7504543956104673198653299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006058608139564264871065 7504543956104673198653299)
                  ·
                    refine ⟨11256815934157009797979949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504543956104673198653299 11256815934157009797979949)
                    ·
                      refine ⟨4221305975308878674242481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11256815934157009797979949 4221305975308878674242481)
                      ·
                        rfl

theorem cell23_8220964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_8220964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8220964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8220964 prefixEnd_8220964 := by exact prefixLift 8220964
  have htrace : WordTrace (prefixWord ++ tailWord_8220964) baseStart_8220964 baseEnd_8220964 := by
    simpa [prefixWord, tailWord_8220964, baseEnd_8220964] using wordTrace_append hprefix tailTrace_8220964
  have hstable : (prefixWord ++ tailWord_8220964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8220964).length < 2 ^ (prefixWord ++ tailWord_8220964).sum := by decide
  have hdescent : baseEnd_8220964 < baseStart_8220964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8220964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221040 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_8221040 : Nat := 118140960795 + 8221040 * 2 ^ 59
def prefixEnd_8221040 : Nat := 4983230072969 + 3 ^ 40 * 8221040 * 2
def baseEnd_8221040 : Nat := 1407114999946206792297377

theorem tailTrace_8221040 : CollatzResearch.WordTrace tailWord_8221040 prefixEnd_8221040 1407114999946206792297377 := by
  unfold tailWord_8221040
  simp only [CollatzResearch.WordTrace]
  refine ⟨149922981068291798347814287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199897308091055731130419049 149922981068291798347814287)
  ·
    refine ⟨224884471602437697521721431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149922981068291798347814287 224884471602437697521721431)
    ·
      refine ⟨337326707403656546282582147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224884471602437697521721431 337326707403656546282582147)
      ·
        refine ⟨505990061105484819423873221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337326707403656546282582147 505990061105484819423873221)
        ·
          refine ⟨94873136457278403641976229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505990061105484819423873221 94873136457278403641976229)
          ·
            refine ⟨17788713085739700682870543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94873136457278403641976229 17788713085739700682870543)
            ·
              refine ⟨26683069628609551024305815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17788713085739700682870543 26683069628609551024305815)
              ·
                refine ⟨40024604442914326536458723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26683069628609551024305815 40024604442914326536458723)
                ·
                  refine ⟨60036906664371489804688085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40024604442914326536458723 60036906664371489804688085)
                  ·
                    refine ⟨1407114999946206792297377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60036906664371489804688085 1407114999946206792297377)
                    ·
                      rfl

theorem cell23_8221040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_8221040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221040 prefixEnd_8221040 := by exact prefixLift 8221040
  have htrace : WordTrace (prefixWord ++ tailWord_8221040) baseStart_8221040 baseEnd_8221040 := by
    simpa [prefixWord, tailWord_8221040, baseEnd_8221040] using wordTrace_append hprefix tailTrace_8221040
  have hstable : (prefixWord ++ tailWord_8221040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221040).length < 2 ^ (prefixWord ++ tailWord_8221040).sum := by decide
  have hdescent : baseEnd_8221040 < baseStart_8221040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221087 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 3, 4]
def baseStart_8221087 : Nat := 118140960795 + 8221087 * 2 ^ 59
def prefixEnd_8221087 : Nat := 4983230072969 + 3 ^ 40 * 8221087 * 2
def baseEnd_8221087 : Nat := 1407123044476460564334805

theorem tailTrace_8221087 : CollatzResearch.WordTrace tailWord_8221087 prefixEnd_8221087 1407123044476460564334805 := by
  unfold tailWord_8221087
  simp only [CollatzResearch.WordTrace]
  refine ⟨299847676367413323722589515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199898450911608882481726343 299847676367413323722589515)
  ·
    refine ⟨449771514551119985583884273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299847676367413323722589515 449771514551119985583884273)
    ·
      refine ⟨337328635913339989187913205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449771514551119985583884273 337328635913339989187913205)
      ·
        refine ⟨31624559616875623986366863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337328635913339989187913205 31624559616875623986366863)
        ·
          refine ⟨47436839425313435979550295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31624559616875623986366863 47436839425313435979550295)
          ·
            refine ⟨71155259137970153969325443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47436839425313435979550295 71155259137970153969325443)
            ·
              refine ⟨106732888706955230953988165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71155259137970153969325443 106732888706955230953988165)
              ·
                refine ⟨20012416632554105803872781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106732888706955230953988165 20012416632554105803872781)
                ·
                  refine ⟨7504656237207789676452293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20012416632554105803872781 7504656237207789676452293)
                  ·
                    refine ⟨1407123044476460564334805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504656237207789676452293 1407123044476460564334805)
                    ·
                      rfl

theorem cell23_8221087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_8221087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221087 prefixEnd_8221087 := by exact prefixLift 8221087
  have htrace : WordTrace (prefixWord ++ tailWord_8221087) baseStart_8221087 baseEnd_8221087 := by
    simpa [prefixWord, tailWord_8221087, baseEnd_8221087] using wordTrace_append hprefix tailTrace_8221087
  have hstable : (prefixWord ++ tailWord_8221087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221087).length < 2 ^ (prefixWord ++ tailWord_8221087).sum := by decide
  have hdescent : baseEnd_8221087 < baseStart_8221087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221137 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 3, 5, 2]
def baseStart_8221137 : Nat := 118140960795 + 8221137 * 2 ^ 59
def prefixEnd_8221137 : Nat := 4983230072969 + 3 ^ 40 * 8221137 * 2
def baseEnd_8221137 : Nat := 4221394807462106497379185

theorem tailTrace_8221137 : CollatzResearch.WordTrace tailWord_8221137 prefixEnd_8221137 4221394807462106497379185 := by
  unfold tailWord_8221137
  simp only [CollatzResearch.WordTrace]
  refine ⟨299849500017232182261909665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199899666678154788174606443 299849500017232182261909665)
  ·
    refine ⟨224887125012924136696432249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299849500017232182261909665 224887125012924136696432249)
    ·
      refine ⟨168665343759693102522324187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224887125012924136696432249 168665343759693102522324187)
      ·
        refine ⟨252998015639539653783486281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168665343759693102522324187 252998015639539653783486281)
        ·
          refine ⟨189748511729654740337614711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252998015639539653783486281 189748511729654740337614711)
          ·
            refine ⟨284622767594482110506422067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189748511729654740337614711 284622767594482110506422067)
            ·
              refine ⟨426934151391723165759633101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284622767594482110506422067 426934151391723165759633101)
              ·
                refine ⟨160100306771896187159862413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426934151391723165759633101 160100306771896187159862413)
                ·
                  refine ⟨60037615039461070184948405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160100306771896187159862413 60037615039461070184948405)
                  ·
                    refine ⟨5628526409949475329838913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60037615039461070184948405 5628526409949475329838913)
                    ·
                      refine ⟨4221394807462106497379185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628526409949475329838913 4221394807462106497379185)
                      ·
                        rfl

theorem cell23_8221137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_8221137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221137 prefixEnd_8221137 := by exact prefixLift 8221137
  have htrace : WordTrace (prefixWord ++ tailWord_8221137) baseStart_8221137 baseEnd_8221137 := by
    simpa [prefixWord, tailWord_8221137, baseEnd_8221137] using wordTrace_append hprefix tailTrace_8221137
  have hstable : (prefixWord ++ tailWord_8221137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221137).length < 2 ^ (prefixWord ++ tailWord_8221137).sum := by decide
  have hdescent : baseEnd_8221137 < baseStart_8221137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221164 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_8221164 : Nat := 118140960795 + 8221164 * 2 ^ 59
def prefixEnd_8221164 : Nat := 4983230072969 + 3 ^ 40 * 8221164 * 2
def baseEnd_8221164 : Nat := 1407136223813259297247187

theorem tailTrace_8221164 : CollatzResearch.WordTrace tailWord_8221164 prefixEnd_8221164 1407136223813259297247187 := by
  unfold tailWord_8221164
  simp only [CollatzResearch.WordTrace]
  refine ⟨149925242394067182936571273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199900323192089577248761697 149925242394067182936571273)
  ·
    refine ⟨112443931795550387202428455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149925242394067182936571273 112443931795550387202428455)
    ·
      refine ⟨168665897693325580803642683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112443931795550387202428455 168665897693325580803642683)
      ·
        refine ⟨252998846539988371205464025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168665897693325580803642683 252998846539988371205464025)
        ·
          refine ⟨189749134904991278404098019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252998846539988371205464025 189749134904991278404098019)
          ·
            refine ⟨284623702357486917606147029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189749134904991278404098019 284623702357486917606147029)
            ·
              refine ⟨6670868024003599631394071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 284623702357486917606147029 6670868024003599631394071)
              ·
                refine ⟨10006302036005399447091107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670868024003599631394071 10006302036005399447091107)
                ·
                  refine ⟨15009453054008099170636661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10006302036005399447091107 15009453054008099170636661)
                  ·
                    refine ⟨1407136223813259297247187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15009453054008099170636661 1407136223813259297247187)
                    ·
                      rfl

theorem cell23_8221164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_8221164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221164 prefixEnd_8221164 := by exact prefixLift 8221164
  have htrace : WordTrace (prefixWord ++ tailWord_8221164) baseStart_8221164 baseEnd_8221164 := by
    simpa [prefixWord, tailWord_8221164, baseEnd_8221164] using wordTrace_append hprefix tailTrace_8221164
  have hstable : (prefixWord ++ tailWord_8221164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221164).length < 2 ^ (prefixWord ++ tailWord_8221164).sum := by decide
  have hdescent : baseEnd_8221164 < baseStart_8221164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
