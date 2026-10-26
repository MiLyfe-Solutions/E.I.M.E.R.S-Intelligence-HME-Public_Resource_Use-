import V185TrunkScan23Chunk0687

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4068364 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 1, 1, 3]
def baseStart_4068364 : Nat := 118140960795 + 4068364 * 2 ^ 59
def prefixEnd_4068364 : Nat := 4983230072969 + 3 ^ 40 * 4068364 * 2
def baseEnd_4068364 : Nat := 2089026209448425740839941

theorem tailTrace_4068364 : CollatzResearch.WordTrace tailWord_4068364 prefixEnd_4068364 2089026209448425740839941 := by
  unfold tailWord_4068364
  simp only [CollatzResearch.WordTrace]
  refine ⟨74192712716509762049382073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98923616955346349399176097 74192712716509762049382073)
  ·
    refine ⟨55644534537382321537036555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74192712716509762049382073 55644534537382321537036555)
    ·
      refine ⟨83466801806073482305554833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55644534537382321537036555 83466801806073482305554833)
      ·
        refine ⟨62600101354555111729166125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83466801806073482305554833 62600101354555111729166125)
        ·
          refine ⟨23475038007958166898437297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62600101354555111729166125 23475038007958166898437297)
          ·
            refine ⟨17606278505968625173827973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23475038007958166898437297 17606278505968625173827973)
            ·
              refine ⟨3301177219869117220092745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17606278505968625173827973 3301177219869117220092745)
              ·
                refine ⟨2475882914901837915069559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301177219869117220092745 2475882914901837915069559)
                ·
                  refine ⟨3713824372352756872604339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475882914901837915069559 3713824372352756872604339)
                  ·
                    refine ⟨5570736558529135308906509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713824372352756872604339 5570736558529135308906509)
                    ·
                      refine ⟨2089026209448425740839941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5570736558529135308906509 2089026209448425740839941)
                      ·
                        rfl

theorem cell23_4068364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_4068364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068364 prefixEnd_4068364 := by exact prefixLift 4068364
  have htrace : WordTrace (prefixWord ++ tailWord_4068364) baseStart_4068364 baseEnd_4068364 := by
    simpa [prefixWord, tailWord_4068364, baseEnd_4068364] using wordTrace_append hprefix tailTrace_4068364
  have hstable : (prefixWord ++ tailWord_4068364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068364).length < 2 ^ (prefixWord ++ tailWord_4068364).sum := by decide
  have hdescent : baseEnd_4068364 < baseStart_4068364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068380 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_4068380 : Nat := 118140960795 + 4068380 * 2 ^ 59
def prefixEnd_4068380 : Nat := 4983230072969 + 3 ^ 40 * 4068380 * 2
def baseEnd_4068380 : Nat := 696344808379632559413289

theorem tailTrace_4068380 : CollatzResearch.WordTrace tailWord_4068380 prefixEnd_4068380 696344808379632559413289 := by
  unfold tailWord_4068380
  simp only [CollatzResearch.WordTrace]
  refine ⟨74193004500480779415673297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98924006000641039220897729 74193004500480779415673297)
  ·
    refine ⟨55644753375360584561754973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74193004500480779415673297 55644753375360584561754973)
    ·
      refine ⟨20866782515760219210658115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55644753375360584561754973 20866782515760219210658115)
      ·
        refine ⟨31300173773640328815987173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20866782515760219210658115 31300173773640328815987173)
        ·
          refine ⟨5868782582557561652997595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31300173773640328815987173 5868782582557561652997595)
          ·
            refine ⟨8803173873836342479496393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868782582557561652997595 8803173873836342479496393)
            ·
              refine ⟨6602380405377256859622295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8803173873836342479496393 6602380405377256859622295)
              ·
                refine ⟨9903570608065885289433443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602380405377256859622295 9903570608065885289433443)
                ·
                  refine ⟨14855355912098827934150165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9903570608065885289433443 14855355912098827934150165)
                  ·
                    refine ⟨696344808379632559413289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14855355912098827934150165 696344808379632559413289)
                    ·
                      rfl

theorem cell23_4068380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_4068380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068380 prefixEnd_4068380 := by exact prefixLift 4068380
  have htrace : WordTrace (prefixWord ++ tailWord_4068380) baseStart_4068380 baseEnd_4068380 := by
    simpa [prefixWord, tailWord_4068380, baseEnd_4068380] using wordTrace_append hprefix tailTrace_4068380
  have hstable : (prefixWord ++ tailWord_4068380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068380).length < 2 ^ (prefixWord ++ tailWord_4068380).sum := by decide
  have hdescent : baseEnd_4068380 < baseStart_4068380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068383 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4068383 : Nat := 118140960795 + 4068383 * 2 ^ 59
def prefixEnd_4068383 : Nat := 4983230072969 + 3 ^ 40 * 4068383 * 2
def baseEnd_4068383 : Nat := 2089035965580861166502353

theorem tailTrace_4068383 : CollatzResearch.WordTrace tailWord_4068383 prefixEnd_4068383 2089035965580861166502353 := by
  unfold tailWord_4068383
  simp only [CollatzResearch.WordTrace]
  refine ⟨148386118419950690343705803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98924078946633793562470535 148386118419950690343705803)
  ·
    refine ⟨222579177629926035515558705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148386118419950690343705803 222579177629926035515558705)
    ·
      refine ⟨166934383222444526636669029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222579177629926035515558705 166934383222444526636669029)
      ·
        refine ⟨31300196854208348744375443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166934383222444526636669029 31300196854208348744375443)
        ·
          refine ⟨46950295281312523116563165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31300196854208348744375443 46950295281312523116563165)
          ·
            refine ⟨17606360730492196168711187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46950295281312523116563165 17606360730492196168711187)
            ·
              refine ⟨26409541095738294253066781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606360730492196168711187 26409541095738294253066781)
              ·
                refine ⟨9903577910901860344900043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26409541095738294253066781 9903577910901860344900043)
                ·
                  refine ⟨14855366866352790517350065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9903577910901860344900043 14855366866352790517350065)
                  ·
                    refine ⟨11141525149764592888012549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14855366866352790517350065 11141525149764592888012549)
                    ·
                      refine ⟨2089035965580861166502353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11141525149764592888012549 2089035965580861166502353)
                      ·
                        rfl

theorem cell23_4068383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4068383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068383 prefixEnd_4068383 := by exact prefixLift 4068383
  have htrace : WordTrace (prefixWord ++ tailWord_4068383) baseStart_4068383 baseEnd_4068383 := by
    simpa [prefixWord, tailWord_4068383, baseEnd_4068383] using wordTrace_append hprefix tailTrace_4068383
  have hstable : (prefixWord ++ tailWord_4068383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068383).length < 2 ^ (prefixWord ++ tailWord_4068383).sum := by decide
  have hdescent : baseEnd_4068383 < baseStart_4068383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068387 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 3, 2, 2]
def baseStart_4068387 : Nat := 118140960795 + 4068387 * 2 ^ 59
def prefixEnd_4068387 : Nat := 4983230072969 + 3 ^ 40 * 4068387 * 2
def baseEnd_4068387 : Nat := 2089038019503479150852335

theorem tailTrace_4068387 : CollatzResearch.WordTrace tailWord_4068387 prefixEnd_4068387 2089038019503479150852335 := by
  unfold tailWord_4068387
  simp only [CollatzResearch.WordTrace]
  refine ⟨148386264311936199026851415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98924176207957466017900943 148386264311936199026851415)
  ·
    refine ⟨222579396467904298540277123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148386264311936199026851415 222579396467904298540277123)
    ·
      refine ⟨333869094701856447810415685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222579396467904298540277123 333869094701856447810415685)
      ·
        refine ⟨62600455256598083964452941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333869094701856447810415685 62600455256598083964452941)
        ·
          refine ⟨23475170721224281486669853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62600455256598083964452941 23475170721224281486669853)
          ·
            refine ⟨8803189020459105557501195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23475170721224281486669853 8803189020459105557501195)
            ·
              refine ⟨13204783530688658336251793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8803189020459105557501195 13204783530688658336251793)
              ·
                refine ⟨9903587648016493752188845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13204783530688658336251793 9903587648016493752188845)
                ·
                  refine ⟨3713845368006185157070817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9903587648016493752188845 3713845368006185157070817)
                  ·
                    refine ⟨2785384026004638867803113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713845368006185157070817 2785384026004638867803113)
                    ·
                      refine ⟨2089038019503479150852335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785384026004638867803113 2089038019503479150852335)
                      ·
                        rfl

theorem cell23_4068387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_4068387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068387 prefixEnd_4068387 := by exact prefixLift 4068387
  have htrace : WordTrace (prefixWord ++ tailWord_4068387) baseStart_4068387 baseEnd_4068387 := by
    simpa [prefixWord, tailWord_4068387, baseEnd_4068387] using wordTrace_append hprefix tailTrace_4068387
  have hstable : (prefixWord ++ tailWord_4068387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068387).length < 2 ^ (prefixWord ++ tailWord_4068387).sum := by decide
  have hdescent : baseEnd_4068387 < baseStart_4068387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068404 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4068404 : Nat := 118140960795 + 4068404 * 2 ^ 59
def prefixEnd_4068404 : Nat := 4983230072969 + 3 ^ 40 * 4068404 * 2
def baseEnd_4068404 : Nat := 2089046748674605584339757

theorem tailTrace_4068404 : CollatzResearch.WordTrace tailWord_4068404 prefixEnd_4068404 2089046748674605584339757 := by
  unfold tailWord_4068404
  simp only [CollatzResearch.WordTrace]
  refine ⟨74193442176437305465110133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98924589568583073953480177 74193442176437305465110133)
  ·
    refine ⟨6955635204040997387354075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74193442176437305465110133 6955635204040997387354075)
    ·
      refine ⟨10433452806061496081031113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955635204040997387354075 10433452806061496081031113)
      ·
        refine ⟨7825089604546122060773335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10433452806061496081031113 7825089604546122060773335)
        ·
          refine ⟨11737634406819183091160003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825089604546122060773335 11737634406819183091160003)
          ·
            refine ⟨17606451610228774636740005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737634406819183091160003 17606451610228774636740005)
            ·
              refine ⟨3301209676917895244388751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17606451610228774636740005 3301209676917895244388751)
              ·
                refine ⟨4951814515376842866583127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301209676917895244388751 4951814515376842866583127)
                ·
                  refine ⟨7427721773065264299874691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951814515376842866583127 7427721773065264299874691)
                  ·
                    refine ⟨11141582659597896449812037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7427721773065264299874691 11141582659597896449812037)
                    ·
                      refine ⟨2089046748674605584339757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11141582659597896449812037 2089046748674605584339757)
                      ·
                        rfl

theorem cell23_4068404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4068404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068404 prefixEnd_4068404 := by exact prefixLift 4068404
  have htrace : WordTrace (prefixWord ++ tailWord_4068404) baseStart_4068404 baseEnd_4068404 := by
    simpa [prefixWord, tailWord_4068404, baseEnd_4068404] using wordTrace_append hprefix tailTrace_4068404
  have hstable : (prefixWord ++ tailWord_4068404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068404).length < 2 ^ (prefixWord ++ tailWord_4068404).sum := by decide
  have hdescent : baseEnd_4068404 < baseStart_4068404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068414 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_4068414 : Nat := 118140960795 + 4068414 * 2 ^ 59
def prefixEnd_4068414 : Nat := 4983230072969 + 3 ^ 40 * 4068414 * 2
def baseEnd_4068414 : Nat := 696350627827050181738237

theorem tailTrace_4068414 : CollatzResearch.WordTrace tailWord_4068414 prefixEnd_4068414 696350627827050181738237 := by
  unfold tailWord_4068414
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548406135354797829760537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98924832721892255092056197 18548406135354797829760537)
  ·
    refine ⟨13911304601516098372320403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18548406135354797829760537 13911304601516098372320403)
    ·
      refine ⟨20866956902274147558480605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13911304601516098372320403 20866956902274147558480605)
      ·
        refine ⟨7825108838352805334430227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20866956902274147558480605 7825108838352805334430227)
        ·
          refine ⟨11737663257529208001645341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825108838352805334430227 11737663257529208001645341)
          ·
            refine ⟨4401623721573453000617003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11737663257529208001645341 4401623721573453000617003)
            ·
              refine ⟨6602435582360179500925505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4401623721573453000617003 6602435582360179500925505)
              ·
                refine ⟨4951826686770134625694129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6602435582360179500925505 4951826686770134625694129)
                ·
                  refine ⟨3713870015077600969270597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951826686770134625694129 3713870015077600969270597)
                  ·
                    refine ⟨696350627827050181738237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3713870015077600969270597 696350627827050181738237)
                    ·
                      rfl

theorem cell23_4068414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_4068414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068414 prefixEnd_4068414 := by exact prefixLift 4068414
  have htrace : WordTrace (prefixWord ++ tailWord_4068414) baseStart_4068414 baseEnd_4068414 := by
    simpa [prefixWord, tailWord_4068414, baseEnd_4068414] using wordTrace_append hprefix tailTrace_4068414
  have hstable : (prefixWord ++ tailWord_4068414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068414).length < 2 ^ (prefixWord ++ tailWord_4068414).sum := by decide
  have hdescent : baseEnd_4068414 < baseStart_4068414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068447 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 1, 3, 2]
def baseStart_4068447 : Nat := 118140960795 + 4068447 * 2 ^ 59
def prefixEnd_4068447 : Nat := 4983230072969 + 3 ^ 40 * 4068447 * 2
def baseEnd_4068447 : Nat := 2089068828342748916102059

theorem tailTrace_4068447 : CollatzResearch.WordTrace tailWord_4068447 prefixEnd_4068447 2089068828342748916102059 := by
  unfold tailWord_4068447
  simp only [CollatzResearch.WordTrace]
  refine ⟨148388452691718829274035595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98925635127812552849357063 148388452691718829274035595)
  ·
    refine ⟨222582679037578243911053393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148388452691718829274035595 222582679037578243911053393)
    ·
      refine ⟨166937009278183682933290045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222582679037578243911053393 166937009278183682933290045)
      ·
        refine ⟨62601378479318881099983767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166937009278183682933290045 62601378479318881099983767)
        ·
          refine ⟨93902067718978321649975651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62601378479318881099983767 93902067718978321649975651)
          ·
            refine ⟨140853101578467482474963477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93902067718978321649975651 140853101578467482474963477)
            ·
              refine ⟨6602489136490663241013913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140853101578467482474963477 6602489136490663241013913)
              ·
                refine ⟨4951866852367997430760435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6602489136490663241013913 4951866852367997430760435)
                ·
                  refine ⟨7427800278551996146140653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951866852367997430760435 7427800278551996146140653)
                  ·
                    refine ⟨2785425104456998554802745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7427800278551996146140653 2785425104456998554802745)
                    ·
                      refine ⟨2089068828342748916102059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785425104456998554802745 2089068828342748916102059)
                      ·
                        rfl

theorem cell23_4068447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_4068447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068447 prefixEnd_4068447 := by exact prefixLift 4068447
  have htrace : WordTrace (prefixWord ++ tailWord_4068447) baseStart_4068447 baseEnd_4068447 := by
    simpa [prefixWord, tailWord_4068447, baseEnd_4068447] using wordTrace_append hprefix tailTrace_4068447
  have hstable : (prefixWord ++ tailWord_4068447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068447).length < 2 ^ (prefixWord ++ tailWord_4068447).sum := by decide
  have hdescent : baseEnd_4068447 < baseStart_4068447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068450 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4068450 : Nat := 118140960795 + 4068450 * 2 ^ 59
def prefixEnd_4068450 : Nat := 4983230072969 + 3 ^ 40 * 4068450 * 2
def baseEnd_4068450 : Nat := 2089070368784712404364545

theorem tailTrace_4068450 : CollatzResearch.WordTrace tailWord_4068450 prefixEnd_4068450 2089070368784712404364545 := by
  unfold tailWord_4068450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37097140527676990196598701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98925708073805307190929869 37097140527676990196598701)
  ·
    refine ⟨13911427697878871323724513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37097140527676990196598701 13911427697878871323724513)
    ·
      refine ⟨10433570773409153492793385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13911427697878871323724513 10433570773409153492793385)
      ·
        refine ⟨7825178080056865119595039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10433570773409153492793385 7825178080056865119595039)
        ·
          refine ⟨11737767120085297679392559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825178080056865119595039 11737767120085297679392559)
          ·
            refine ⟨17606650680127946519088839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737767120085297679392559 17606650680127946519088839)
            ·
              refine ⟨26409976020191919778633259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606650680127946519088839 26409976020191919778633259)
              ·
                refine ⟨39614964030287879667949889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26409976020191919778633259 39614964030287879667949889)
                ·
                  refine ⟨29711223022715909750962417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39614964030287879667949889 29711223022715909750962417)
                  ·
                    refine ⟨22283417267036932313221813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29711223022715909750962417 22283417267036932313221813)
                    ·
                      refine ⟨2089070368784712404364545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22283417267036932313221813 2089070368784712404364545)
                      ·
                        rfl

theorem cell23_4068450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4068450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068450 prefixEnd_4068450 := by exact prefixLift 4068450
  have htrace : WordTrace (prefixWord ++ tailWord_4068450) baseStart_4068450 baseEnd_4068450 := by
    simpa [prefixWord, tailWord_4068450, baseEnd_4068450] using wordTrace_append hprefix tailTrace_4068450
  have hstable : (prefixWord ++ tailWord_4068450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068450).length < 2 ^ (prefixWord ++ tailWord_4068450).sum := by decide
  have hdescent : baseEnd_4068450 < baseStart_4068450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068460 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 3, 4, 2]
def baseStart_4068460 : Nat := 118140960795 + 4068460 * 2 ^ 59
def prefixEnd_4068460 : Nat := 4983230072969 + 3 ^ 40 * 4068460 * 2
def baseEnd_4068460 : Nat := 2089075503591257365239499

theorem tailTrace_4068460 : CollatzResearch.WordTrace tailWord_4068460 prefixEnd_4068460 2089075503591257365239499 := by
  unfold tailWord_4068460
  simp only [CollatzResearch.WordTrace]
  refine ⟨74194463420335866247129417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98925951227114488329505889 74194463420335866247129417)
  ·
    refine ⟨55645847565251899685347063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74194463420335866247129417 55645847565251899685347063)
    ·
      refine ⟨83468771347877849528020595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55645847565251899685347063 83468771347877849528020595)
      ·
        refine ⟨125203157021816774292030893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83468771347877849528020595 125203157021816774292030893)
        ·
          refine ⟨46951183883181290359511585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125203157021816774292030893 46951183883181290359511585)
          ·
            refine ⟨35213387912385967769633689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46951183883181290359511585 35213387912385967769633689)
            ·
              refine ⟨26410040934289475827225267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35213387912385967769633689 26410040934289475827225267)
              ·
                refine ⟨39615061401434213740837901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26410040934289475827225267 39615061401434213740837901)
                ·
                  refine ⟨14855648025537830152814213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39615061401434213740837901 14855648025537830152814213)
                  ·
                    refine ⟨2785434004788343153652665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14855648025537830152814213 2785434004788343153652665)
                    ·
                      refine ⟨2089075503591257365239499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785434004788343153652665 2089075503591257365239499)
                      ·
                        rfl

theorem cell23_4068460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_4068460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068460 prefixEnd_4068460 := by exact prefixLift 4068460
  have htrace : WordTrace (prefixWord ++ tailWord_4068460) baseStart_4068460 baseEnd_4068460 := by
    simpa [prefixWord, tailWord_4068460, baseEnd_4068460] using wordTrace_append hprefix tailTrace_4068460
  have hstable : (prefixWord ++ tailWord_4068460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068460).length < 2 ^ (prefixWord ++ tailWord_4068460).sum := by decide
  have hdescent : baseEnd_4068460 < baseStart_4068460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068463 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_4068463 : Nat := 118140960795 + 4068463 * 2 ^ 59
def prefixEnd_4068463 : Nat := 4983230072969 + 3 ^ 40 * 4068463 * 2
def baseEnd_4068463 : Nat := 2089077044033220853501985

theorem tailTrace_4068463 : CollatzResearch.WordTrace tailWord_4068463 prefixEnd_4068463 2089077044033220853501985 := by
  unfold tailWord_4068463
  simp only [CollatzResearch.WordTrace]
  refine ⟨148389036259660864006618043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98926024173107242671078695 148389036259660864006618043)
  ·
    refine ⟨222583554389491296009927065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148389036259660864006618043 222583554389491296009927065)
    ·
      refine ⟨166937665792118472007445299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222583554389491296009927065 166937665792118472007445299)
      ·
        refine ⟨250406498688177708011167949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166937665792118472007445299 250406498688177708011167949)
        ·
          refine ⟨93902437008066640504187981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250406498688177708011167949 93902437008066640504187981)
          ·
            refine ⟨35213413878024990189070493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93902437008066640504187981 35213413878024990189070493)
            ·
              refine ⟨13205030204259371320901435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35213413878024990189070493 13205030204259371320901435)
              ·
                refine ⟨19807545306389056981352153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13205030204259371320901435 19807545306389056981352153)
                ·
                  refine ⟨14855658979791792736014115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19807545306389056981352153 14855658979791792736014115)
                  ·
                    refine ⟨22283488469687689104021173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14855658979791792736014115 22283488469687689104021173)
                    ·
                      refine ⟨2089077044033220853501985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22283488469687689104021173 2089077044033220853501985)
                      ·
                        rfl

theorem cell23_4068463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_4068463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068463 prefixEnd_4068463 := by exact prefixLift 4068463
  have htrace : WordTrace (prefixWord ++ tailWord_4068463) baseStart_4068463 baseEnd_4068463 := by
    simpa [prefixWord, tailWord_4068463, baseEnd_4068463] using wordTrace_append hprefix tailTrace_4068463
  have hstable : (prefixWord ++ tailWord_4068463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068463).length < 2 ^ (prefixWord ++ tailWord_4068463).sum := by decide
  have hdescent : baseEnd_4068463 < baseStart_4068463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068477 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_4068477 : Nat := 118140960795 + 4068477 * 2 ^ 59
def prefixEnd_4068477 : Nat := 4983230072969 + 3 ^ 40 * 4068477 * 2
def baseEnd_4068477 : Nat := 2089084232762383798726921

theorem tailTrace_4068477 : CollatzResearch.WordTrace tailWord_4068477 prefixEnd_4068477 2089084232762383798726921 := by
  unfold tailWord_4068477
  simp only [CollatzResearch.WordTrace]
  refine ⟨148389546881610144397627685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98926364587740096265085123 148389546881610144397627685)
  ·
    refine ⟨27823040040301902074555191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148389546881610144397627685 27823040040301902074555191)
    ·
      refine ⟨41734560060452853111832787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27823040040301902074555191 41734560060452853111832787)
      ·
        refine ⟨62601840090679279667749181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41734560060452853111832787 62601840090679279667749181)
        ·
          refine ⟨23475690034004729875405943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62601840090679279667749181 23475690034004729875405943)
          ·
            refine ⟨35213535051007094813108915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23475690034004729875405943 35213535051007094813108915)
            ·
              refine ⟨52820302576510642219663373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35213535051007094813108915 52820302576510642219663373)
              ·
                refine ⟨19807613466191490832373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52820302576510642219663373 19807613466191490832373765)
                ·
                  refine ⟨3713927524910904531070081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19807613466191490832373765 3713927524910904531070081)
                  ·
                    refine ⟨2785445643683178398302561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713927524910904531070081 2785445643683178398302561)
                    ·
                      refine ⟨2089084232762383798726921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785445643683178398302561 2089084232762383798726921)
                      ·
                        rfl

theorem cell23_4068477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_4068477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068477 prefixEnd_4068477 := by exact prefixLift 4068477
  have htrace : WordTrace (prefixWord ++ tailWord_4068477) baseStart_4068477 baseEnd_4068477 := by
    simpa [prefixWord, tailWord_4068477, baseEnd_4068477] using wordTrace_append hprefix tailTrace_4068477
  have hstable : (prefixWord ++ tailWord_4068477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068477).length < 2 ^ (prefixWord ++ tailWord_4068477).sum := by decide
  have hdescent : baseEnd_4068477 < baseStart_4068477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068488 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4068488 : Nat := 118140960795 + 4068488 * 2 ^ 59
def prefixEnd_4068488 : Nat := 4983230072969 + 3 ^ 40 * 4068488 * 2
def baseEnd_4068488 : Nat := 2089089881049583255689371

theorem tailTrace_4068488 : CollatzResearch.WordTrace tailWord_4068488 prefixEnd_4068488 2089089881049583255689371 := by
  unfold tailWord_4068488
  simp only [CollatzResearch.WordTrace]
  refine ⟨74194974042285146638139059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98926632056380195517518745 74194974042285146638139059)
  ·
    refine ⟨111292461063427719957208589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74194974042285146638139059 111292461063427719957208589)
    ·
      refine ⟨41734672898785394983953221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111292461063427719957208589 41734672898785394983953221)
      ·
        refine ⟨7825251168522261559491229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41734672898785394983953221 7825251168522261559491229)
        ·
          refine ⟨2934469188195848084809211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7825251168522261559491229 2934469188195848084809211)
          ·
            refine ⟨4401703782293772127213817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934469188195848084809211 4401703782293772127213817)
            ·
              refine ⟨3301277836720329095410363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401703782293772127213817 3301277836720329095410363)
              ·
                refine ⟨4951916755080493643115545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301277836720329095410363 4951916755080493643115545)
                ·
                  refine ⟨3713937566310370232336659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951916755080493643115545 3713937566310370232336659)
                  ·
                    refine ⟨5570906349465555348504989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713937566310370232336659 5570906349465555348504989)
                    ·
                      refine ⟨2089089881049583255689371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5570906349465555348504989 2089089881049583255689371)
                      ·
                        rfl

theorem cell23_4068488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4068488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068488 prefixEnd_4068488 := by exact prefixLift 4068488
  have htrace : WordTrace (prefixWord ++ tailWord_4068488) baseStart_4068488 baseEnd_4068488 := by
    simpa [prefixWord, tailWord_4068488, baseEnd_4068488] using wordTrace_append hprefix tailTrace_4068488
  have hstable : (prefixWord ++ tailWord_4068488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068488).length < 2 ^ (prefixWord ++ tailWord_4068488).sum := by decide
  have hdescent : baseEnd_4068488 < baseStart_4068488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068530 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_4068530 : Nat := 118140960795 + 4068530 * 2 ^ 59
def prefixEnd_4068530 : Nat := 4983230072969 + 3 ^ 40 * 4068530 * 2
def baseEnd_4068530 : Nat := 696370482412357363788059

theorem tailTrace_4068530 : CollatzResearch.WordTrace tailWord_4068530 prefixEnd_4068530 696370482412357363788059 := by
  unfold tailWord_4068530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37097869987604533612326761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98927653300278756299538029 37097869987604533612326761)
  ·
    refine ⟨27823402490703400209245071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37097869987604533612326761 27823402490703400209245071)
    ·
      refine ⟨41735103736055100313867607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27823402490703400209245071 41735103736055100313867607)
      ·
        refine ⟨62602655604082650470801411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41735103736055100313867607 62602655604082650470801411)
        ·
          refine ⟨93903983406123975706202117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62602655604082650470801411 93903983406123975706202117)
          ·
            refine ⟨17606996888648245444912897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93903983406123975706202117 17606996888648245444912897)
            ·
              refine ⟨13205247666486184083684673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17606996888648245444912897 13205247666486184083684673)
              ·
                refine ⟨9903935749864638062763505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13205247666486184083684673 9903935749864638062763505)
                ·
                  refine ⟨7427951812398478547072629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9903935749864638062763505 7427951812398478547072629)
                  ·
                    refine ⟨696370482412357363788059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7427951812398478547072629 696370482412357363788059)
                    ·
                      rfl

theorem cell23_4068530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_4068530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068530 prefixEnd_4068530 := by exact prefixLift 4068530
  have htrace : WordTrace (prefixWord ++ tailWord_4068530) baseStart_4068530 baseEnd_4068530 := by
    simpa [prefixWord, tailWord_4068530, baseEnd_4068530] using wordTrace_append hprefix tailTrace_4068530
  have hstable : (prefixWord ++ tailWord_4068530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068530).length < 2 ^ (prefixWord ++ tailWord_4068530).sum := by decide
  have hdescent : baseEnd_4068530 < baseStart_4068530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068540 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4068540 : Nat := 118140960795 + 4068540 * 2 ^ 59
def prefixEnd_4068540 : Nat := 4983230072969 + 3 ^ 40 * 4068540 * 2
def baseEnd_4068540 : Nat := 2089116582043617052239131

theorem tailTrace_4068540 : CollatzResearch.WordTrace tailWord_4068540 prefixEnd_4068540 2089116582043617052239131 := by
  unfold tailWord_4068540
  simp only [CollatzResearch.WordTrace]
  refine ⟨74195922340190953078585537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98927896453587937438114049 74195922340190953078585537)
  ·
    refine ⟨55646941755143214808939153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74195922340190953078585537 55646941755143214808939153)
    ·
      refine ⟨41735206316357411106704365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55646941755143214808939153 41735206316357411106704365)
      ·
        refine ⟨15650702368634029165014137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41735206316357411106704365 15650702368634029165014137)
        ·
          refine ⟨11738026776475521873760603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15650702368634029165014137 11738026776475521873760603)
          ·
            refine ⟨17607040164713282810640905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11738026776475521873760603 17607040164713282810640905)
            ·
              refine ⟨13205280123534962107980679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17607040164713282810640905 13205280123534962107980679)
              ·
                refine ⟨19807920185302443161971019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13205280123534962107980679 19807920185302443161971019)
                ·
                  refine ⟨29711880277953664742956529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19807920185302443161971019 29711880277953664742956529)
                  ·
                    refine ⟨22283910208465248557217397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29711880277953664742956529 22283910208465248557217397)
                    ·
                      refine ⟨2089116582043617052239131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22283910208465248557217397 2089116582043617052239131)
                      ·
                        rfl

theorem cell23_4068540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4068540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068540 prefixEnd_4068540 := by exact prefixLift 4068540
  have htrace : WordTrace (prefixWord ++ tailWord_4068540) baseStart_4068540 baseEnd_4068540 := by
    simpa [prefixWord, tailWord_4068540, baseEnd_4068540] using wordTrace_append hprefix tailTrace_4068540
  have hstable : (prefixWord ++ tailWord_4068540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068540).length < 2 ^ (prefixWord ++ tailWord_4068540).sum := by decide
  have hdescent : baseEnd_4068540 < baseStart_4068540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068563 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4]
def baseStart_4068563 : Nat := 118140960795 + 4068563 * 2 ^ 59
def prefixEnd_4068563 : Nat := 4983230072969 + 3 ^ 40 * 4068563 * 2
def baseEnd_4068563 : Nat := 2089128392098670462251525

theorem tailTrace_4068563 : CollatzResearch.WordTrace tailWord_4068563 prefixEnd_4068563 2089128392098670462251525 := by
  unfold tailWord_4068563
  simp only [CollatzResearch.WordTrace]
  refine ⟨148392683559298581085258343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98928455706199054056838895 148392683559298581085258343)
  ·
    refine ⟨222589025338947871627887515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148392683559298581085258343 222589025338947871627887515)
    ·
      refine ⟨333883538008421807441831273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222589025338947871627887515 333883538008421807441831273)
      ·
        refine ⟨250412653506316355581373455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333883538008421807441831273 250412653506316355581373455)
        ·
          refine ⟨375618980259474533372060183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250412653506316355581373455 375618980259474533372060183)
          ·
            refine ⟨563428470389211800058090275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375618980259474533372060183 563428470389211800058090275)
            ·
              refine ⟨845142705583817700087135413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563428470389211800058090275 845142705583817700087135413)
              ·
                refine ⟨79232128648482909383168945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845142705583817700087135413 79232128648482909383168945)
                ·
                  refine ⟨59424096486362182037376709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79232128648482909383168945 59424096486362182037376709)
                  ·
                    refine ⟨11142018091192909132008133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59424096486362182037376709 11142018091192909132008133)
                    ·
                      refine ⟨2089128392098670462251525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11142018091192909132008133 2089128392098670462251525)
                      ·
                        rfl

theorem cell23_4068563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_4068563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068563 prefixEnd_4068563 := by exact prefixLift 4068563
  have htrace : WordTrace (prefixWord ++ tailWord_4068563) baseStart_4068563 baseEnd_4068563 := by
    simpa [prefixWord, tailWord_4068563, baseEnd_4068563] using wordTrace_append hprefix tailTrace_4068563
  have hstable : (prefixWord ++ tailWord_4068563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068563).length < 2 ^ (prefixWord ++ tailWord_4068563).sum := by decide
  have hdescent : baseEnd_4068563 < baseStart_4068563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068594 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_4068594 : Nat := 118140960795 + 4068594 * 2 ^ 59
def prefixEnd_4068594 : Nat := 4983230072969 + 3 ^ 40 * 4068594 * 2
def baseEnd_4068594 : Nat := 696381436666319946987961

theorem tailTrace_4068594 : CollatzResearch.WordTrace tailWord_4068594 prefixEnd_4068594 696381436666319946987961 := by
  unfold tailWord_4068594
  simp only [CollatzResearch.WordTrace]
  refine ⟨37098453555546568344909209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98929209481457515586424557 37098453555546568344909209)
  ·
    refine ⟨27823840166659926258681907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37098453555546568344909209 27823840166659926258681907)
    ·
      refine ⟨41735760249989889388022861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27823840166659926258681907 41735760249989889388022861)
      ·
        refine ⟨15650910093746208520508573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41735760249989889388022861 15650910093746208520508573)
        ·
          refine ⟨5869091285154828195190715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15650910093746208520508573 5869091285154828195190715)
          ·
            refine ⟨8803636927732242292786073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869091285154828195190715 8803636927732242292786073)
            ·
              refine ⟨6602727695799181719589555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8803636927732242292786073 6602727695799181719589555)
              ·
                refine ⟨9904091543698772579384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602727695799181719589555 9904091543698772579384333)
                ·
                  refine ⟨3714034328887039717269125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9904091543698772579384333 3714034328887039717269125)
                  ·
                    refine ⟨696381436666319946987961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3714034328887039717269125 696381436666319946987961)
                    ·
                      rfl

theorem cell23_4068594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_4068594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068594 prefixEnd_4068594 := by exact prefixLift 4068594
  have htrace : WordTrace (prefixWord ++ tailWord_4068594) baseStart_4068594 baseEnd_4068594 := by
    simpa [prefixWord, tailWord_4068594, baseEnd_4068594] using wordTrace_append hprefix tailTrace_4068594
  have hstable : (prefixWord ++ tailWord_4068594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068594).length < 2 ^ (prefixWord ++ tailWord_4068594).sum := by decide
  have hdescent : baseEnd_4068594 < baseStart_4068594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068607 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 6]
def baseStart_4068607 : Nat := 118140960795 + 4068607 * 2 ^ 59
def prefixEnd_4068607 : Nat := 4983230072969 + 3 ^ 40 * 4068607 * 2
def baseEnd_4068607 : Nat := 232127887249718698900147

theorem tailTrace_4068607 : CollatzResearch.WordTrace tailWord_4068607 prefixEnd_4068607 232127887249718698900147 := by
  unfold tailWord_4068607
  simp only [CollatzResearch.WordTrace]
  refine ⟨148394288371139176599860075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98929525580759451066573383 148394288371139176599860075)
  ·
    refine ⟨222591432556708764899790113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148394288371139176599860075 222591432556708764899790113)
    ·
      refine ⟨166943574417531573674842585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222591432556708764899790113 166943574417531573674842585)
      ·
        refine ⟨125207680813148680256131939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166943574417531573674842585 125207680813148680256131939)
        ·
          refine ⟨187811521219723020384197909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125207680813148680256131939 187811521219723020384197909)
          ·
            refine ⟨8803665057174516580509277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187811521219723020384197909 8803665057174516580509277)
            ·
              refine ⟨3301374396440443717690979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8803665057174516580509277 3301374396440443717690979)
              ·
                refine ⟨4952061594660665576536469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301374396440443717690979 4952061594660665576536469)
                ·
                  refine ⟨232127887249718698900147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4952061594660665576536469 232127887249718698900147)
                  ·
                    rfl

theorem cell23_4068607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 6].length) (baseStart_4068607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068607 prefixEnd_4068607 := by exact prefixLift 4068607
  have htrace : WordTrace (prefixWord ++ tailWord_4068607) baseStart_4068607 baseEnd_4068607 := by
    simpa [prefixWord, tailWord_4068607, baseEnd_4068607] using wordTrace_append hprefix tailTrace_4068607
  have hstable : (prefixWord ++ tailWord_4068607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068607).length < 2 ^ (prefixWord ++ tailWord_4068607).sum := by decide
  have hdescent : baseEnd_4068607 < baseStart_4068607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068617 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 3]
def baseStart_4068617 : Nat := 118140960795 + 4068617 * 2 ^ 59
def prefixEnd_4068617 : Nat := 4983230072969 + 3 ^ 40 * 4068617 * 2
def baseEnd_4068617 : Nat := 2089156120054013250976277

theorem tailTrace_4068617 : CollatzResearch.WordTrace tailWord_4068617 prefixEnd_4068617 2089156120054013250976277 := by
  unfold tailWord_4068617
  simp only [CollatzResearch.WordTrace]
  refine ⟨148394653101102948307724105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98929768734068632205149403 148394653101102948307724105)
  ·
    refine ⟨111295989825827211230793079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148394653101102948307724105 111295989825827211230793079)
    ·
      refine ⟨166943984738740816846189619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111295989825827211230793079 166943984738740816846189619)
      ·
        refine ⟨250415977108111225269284429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166943984738740816846189619 250415977108111225269284429)
        ·
          refine ⟨93905991415541709475981661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250415977108111225269284429 93905991415541709475981661)
          ·
            refine ⟨35214746780828141053493123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93905991415541709475981661 35214746780828141053493123)
            ·
              refine ⟨52822120171242211580239685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35214746780828141053493123 52822120171242211580239685)
              ·
                refine ⟨9904147532107914671294941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52822120171242211580239685 9904147532107914671294941)
                ·
                  refine ⟨3714055324540468001735603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9904147532107914671294941 3714055324540468001735603)
                  ·
                    refine ⟨5571082986810702002603405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3714055324540468001735603 5571082986810702002603405)
                    ·
                      refine ⟨2089156120054013250976277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5571082986810702002603405 2089156120054013250976277)
                      ·
                        rfl

theorem cell23_4068617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_4068617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068617 prefixEnd_4068617 := by exact prefixLift 4068617
  have htrace : WordTrace (prefixWord ++ tailWord_4068617) baseStart_4068617 baseEnd_4068617 := by
    simpa [prefixWord, tailWord_4068617, baseEnd_4068617] using wordTrace_append hprefix tailTrace_4068617
  have hstable : (prefixWord ++ tailWord_4068617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068617).length < 2 ^ (prefixWord ++ tailWord_4068617).sum := by decide
  have hdescent : baseEnd_4068617 < baseStart_4068617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068644 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_4068644 : Nat := 118140960795 + 4068644 * 2 ^ 59
def prefixEnd_4068644 : Nat := 4983230072969 + 3 ^ 40 * 4068644 * 2
def baseEnd_4068644 : Nat := 2089169984031684645338653

theorem tailTrace_4068644 : CollatzResearch.WordTrace tailWord_4068644 prefixEnd_4068644 2089169984031684645338653 := by
  unfold tailWord_4068644
  simp only [CollatzResearch.WordTrace]
  refine ⟨74197818936002565959478493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98930425248003421279304657 74197818936002565959478493)
  ·
    refine ⟨27824182101000962234804435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74197818936002565959478493 27824182101000962234804435)
    ·
      refine ⟨41736273151501443352206653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27824182101000962234804435 41736273151501443352206653)
      ·
        refine ⟨15651102431813041257077495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41736273151501443352206653 15651102431813041257077495)
        ·
          refine ⟨23476653647719561885616243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651102431813041257077495 23476653647719561885616243)
          ·
            refine ⟨35214980471579342828424365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23476653647719561885616243 35214980471579342828424365)
            ·
              refine ⟨13205617676842253560659137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35214980471579342828424365 13205617676842253560659137)
              ·
                refine ⟨9904213257631690170494353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13205617676842253560659137 9904213257631690170494353)
                ·
                  refine ⟨7428159943223767627870765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9904213257631690170494353 7428159943223767627870765)
                  ·
                    refine ⟨2785559978708912860451537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7428159943223767627870765 2785559978708912860451537)
                    ·
                      refine ⟨2089169984031684645338653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785559978708912860451537 2089169984031684645338653)
                      ·
                        rfl

theorem cell23_4068644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_4068644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068644 prefixEnd_4068644 := by exact prefixLift 4068644
  have htrace : WordTrace (prefixWord ++ tailWord_4068644) baseStart_4068644 baseEnd_4068644 := by
    simpa [prefixWord, tailWord_4068644, baseEnd_4068644] using wordTrace_append hprefix tailTrace_4068644
  have hstable : (prefixWord ++ tailWord_4068644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068644).length < 2 ^ (prefixWord ++ tailWord_4068644).sum := by decide
  have hdescent : baseEnd_4068644 < baseStart_4068644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068691 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 1, 2, 2]
def baseStart_4068691 : Nat := 118140960795 + 4068691 * 2 ^ 59
def prefixEnd_4068691 : Nat := 4983230072969 + 3 ^ 40 * 4068691 * 2
def baseEnd_4068691 : Nat := 2089194117622445961450937

theorem tailTrace_4068691 : CollatzResearch.WordTrace tailWord_4068691 prefixEnd_4068691 2089194117622445961450937 := by
  unfold tailWord_4068691
  simp only [CollatzResearch.WordTrace]
  refine ⟨148397352102834858945917927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98931568068556572630611951 148397352102834858945917927)
  ·
    refine ⟨222596028154252288418876891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148397352102834858945917927 222596028154252288418876891)
    ·
      refine ⟨333894042231378432628315337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222596028154252288418876891 333894042231378432628315337)
      ·
        refine ⟨250420531673533824471236503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333894042231378432628315337 250420531673533824471236503)
        ·
          refine ⟨375630797510300736706854755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250420531673533824471236503 375630797510300736706854755)
          ·
            refine ⟨563446196265451105060282133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375630797510300736706854755 563446196265451105060282133)
            ·
              refine ⟨26411540449943020549700725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 563446196265451105060282133 26411540449943020549700725)
              ·
                refine ⟨2476081917182158176534443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26411540449943020549700725 2476081917182158176534443)
                ·
                  refine ⟨3714122875773237264801665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476081917182158176534443 3714122875773237264801665)
                  ·
                    refine ⟨2785592156829927948601249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3714122875773237264801665 2785592156829927948601249)
                    ·
                      refine ⟨2089194117622445961450937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785592156829927948601249 2089194117622445961450937)
                      ·
                        rfl

theorem cell23_4068691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 2, 2].length) (baseStart_4068691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068691 prefixEnd_4068691 := by exact prefixLift 4068691
  have htrace : WordTrace (prefixWord ++ tailWord_4068691) baseStart_4068691 baseEnd_4068691 := by
    simpa [prefixWord, tailWord_4068691, baseEnd_4068691] using wordTrace_append hprefix tailTrace_4068691
  have hstable : (prefixWord ++ tailWord_4068691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068691).length < 2 ^ (prefixWord ++ tailWord_4068691).sum := by decide
  have hdescent : baseEnd_4068691 < baseStart_4068691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068708 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_4068708 : Nat := 118140960795 + 4068708 * 2 ^ 59
def prefixEnd_4068708 : Nat := 4983230072969 + 3 ^ 40 * 4068708 * 2
def baseEnd_4068708 : Nat := 2089202846793572394938359

theorem tailTrace_4068708 : CollatzResearch.WordTrace tailWord_4068708 prefixEnd_4068708 2089202846793572394938359 := by
  unfold tailWord_4068708
  simp only [CollatzResearch.WordTrace]
  refine ⟨74198986071886635424643389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98931981429182180566191185 74198986071886635424643389)
  ·
    refine ⟨27824619776957488284241271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74198986071886635424643389 27824619776957488284241271)
    ·
      refine ⟨41736929665436232426361907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27824619776957488284241271 41736929665436232426361907)
      ·
        refine ⟨62605394498154348639542861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41736929665436232426361907 62605394498154348639542861)
        ·
          refine ⟨23477022936807880739828573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62605394498154348639542861 23477022936807880739828573)
          ·
            refine ⟨8803883601302955277435715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23477022936807880739828573 8803883601302955277435715)
            ·
              refine ⟨13205825401954432916153573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8803883601302955277435715 13205825401954432916153573)
              ·
                refine ⟨2476092262866456171778795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13205825401954432916153573 2476092262866456171778795)
                ·
                  refine ⟨3714138394299684257668193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476092262866456171778795 3714138394299684257668193)
                  ·
                    refine ⟨2785603795724763193251145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3714138394299684257668193 2785603795724763193251145)
                    ·
                      refine ⟨2089202846793572394938359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785603795724763193251145 2089202846793572394938359)
                      ·
                        rfl

theorem cell23_4068708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_4068708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068708 prefixEnd_4068708 := by exact prefixLift 4068708
  have htrace : WordTrace (prefixWord ++ tailWord_4068708) baseStart_4068708 baseEnd_4068708 := by
    simpa [prefixWord, tailWord_4068708, baseEnd_4068708] using wordTrace_append hprefix tailTrace_4068708
  have hstable : (prefixWord ++ tailWord_4068708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068708).length < 2 ^ (prefixWord ++ tailWord_4068708).sum := by decide
  have hdescent : baseEnd_4068708 < baseStart_4068708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068714 : List Nat := [3, 1, 3, 3, 2, 2, 1, 8]
def baseStart_4068714 : Nat := 118140960795 + 4068714 * 2 ^ 59
def prefixEnd_4068714 : Nat := 4983230072969 + 3 ^ 40 * 4068714 * 2
def baseEnd_4068714 : Nat := 77377997321388865609753

theorem tailTrace_4068714 : CollatzResearch.WordTrace tailWord_4068714 prefixEnd_4068714 77377997321388865609753 := by
  unfold tailWord_4068714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37099547745437883468501299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98932127321167689249336797 37099547745437883468501299)
  ·
    refine ⟨55649321618156825202751949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37099547745437883468501299 55649321618156825202751949)
    ·
      refine ⟨20868495606808809451031981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55649321618156825202751949 20868495606808809451031981)
      ·
        refine ⟨7825685852553303544136993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20868495606808809451031981 7825685852553303544136993)
        ·
          refine ⟨5869264389414977658102745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7825685852553303544136993 5869264389414977658102745)
          ·
            refine ⟨4401948292061233243577059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5869264389414977658102745 4401948292061233243577059)
            ·
              refine ⟨6602922438091849865365589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4401948292061233243577059 6602922438091849865365589)
              ·
                refine ⟨77377997321388865609753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6602922438091849865365589 77377997321388865609753)
                ·
                  rfl

theorem cell23_4068714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_4068714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068714 prefixEnd_4068714 := by exact prefixLift 4068714
  have htrace : WordTrace (prefixWord ++ tailWord_4068714) baseStart_4068714 baseEnd_4068714 := by
    simpa [prefixWord, tailWord_4068714, baseEnd_4068714] using wordTrace_append hprefix tailTrace_4068714
  have hstable : (prefixWord ++ tailWord_4068714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068714).length < 2 ^ (prefixWord ++ tailWord_4068714).sum := by decide
  have hdescent : baseEnd_4068714 < baseStart_4068714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068821 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 5]
def baseStart_4068821 : Nat := 118140960795 + 4068821 * 2 ^ 59
def prefixEnd_4068821 : Nat := 4983230072969 + 3 ^ 40 * 4068821 * 2
def baseEnd_4068821 : Nat := 232140096678614494758371

theorem tailTrace_4068821 : CollatzResearch.WordTrace tailWord_4068821 prefixEnd_4068821 232140096678614494758371 := by
  unfold tailWord_4068821
  simp only [CollatzResearch.WordTrace]
  refine ⟨148402093592363891148150317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98934729061575927432100211 148402093592363891148150317)
  ·
    refine ⟨55650785097136459180556369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148402093592363891148150317 55650785097136459180556369)
    ·
      refine ⟨41738088822852344385417277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55650785097136459180556369 41738088822852344385417277)
      ·
        refine ⟨15651783308569629144531479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41738088822852344385417277 15651783308569629144531479)
        ·
          refine ⟨23477674962854443716797219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651783308569629144531479 23477674962854443716797219)
          ·
            refine ⟨35216512444281665575195829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23477674962854443716797219 35216512444281665575195829)
            ·
              refine ⟨3301548041651406147674609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35216512444281665575195829 3301548041651406147674609)
              ·
                refine ⟨2476161031238554610755957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301548041651406147674609 2476161031238554610755957)
                ·
                  refine ⟨232140096678614494758371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476161031238554610755957 232140096678614494758371)
                  ·
                    rfl

theorem cell23_4068821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_4068821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068821 prefixEnd_4068821 := by exact prefixLift 4068821
  have htrace : WordTrace (prefixWord ++ tailWord_4068821) baseStart_4068821 baseEnd_4068821 := by
    simpa [prefixWord, tailWord_4068821, baseEnd_4068821] using wordTrace_append hprefix tailTrace_4068821
  have hstable : (prefixWord ++ tailWord_4068821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068821).length < 2 ^ (prefixWord ++ tailWord_4068821).sum := by decide
  have hdescent : baseEnd_4068821 < baseStart_4068821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068881 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 1, 4]
def baseStart_4068881 : Nat := 118140960795 + 4068881 * 2 ^ 59
def prefixEnd_4068881 : Nat := 4983230072969 + 3 ^ 40 * 4068881 * 2
def baseEnd_4068881 : Nat := 696430559648933406025021

theorem tailTrace_4068881 : CollatzResearch.WordTrace tailWord_4068881 prefixEnd_4068881 696430559648933406025021 := by
  unfold tailWord_4068881
  simp only [CollatzResearch.WordTrace]
  refine ⟨148404281972146521395334497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98936187981431014263556331 148404281972146521395334497)
  ·
    refine ⟨111303211479109891046500873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148404281972146521395334497 111303211479109891046500873)
    ·
      refine ⟨83477408609332418284875655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111303211479109891046500873 83477408609332418284875655)
      ·
        refine ⟨125216112913998627427313483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83477408609332418284875655 125216112913998627427313483)
        ·
          refine ⟨187824169370997941140970225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125216112913998627427313483 187824169370997941140970225)
          ·
            refine ⟨140868127028248455855727669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187824169370997941140970225 140868127028248455855727669)
            ·
              refine ⟨13206386908898292736474469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140868127028248455855727669 13206386908898292736474469)
              ·
                refine ⟨2476197545418429888088963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13206386908898292736474469 2476197545418429888088963)
                ·
                  refine ⟨3714296318127644832133445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476197545418429888088963 3714296318127644832133445)
                  ·
                    refine ⟨696430559648933406025021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3714296318127644832133445 696430559648933406025021)
                    ·
                      rfl

theorem cell23_4068881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_4068881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068881 prefixEnd_4068881 := by exact prefixLift 4068881
  have htrace : WordTrace (prefixWord ++ tailWord_4068881) baseStart_4068881 baseEnd_4068881 := by
    simpa [prefixWord, tailWord_4068881, baseEnd_4068881] using wordTrace_append hprefix tailTrace_4068881
  have hstable : (prefixWord ++ tailWord_4068881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068881).length < 2 ^ (prefixWord ++ tailWord_4068881).sum := by decide
  have hdescent : baseEnd_4068881 < baseStart_4068881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068937 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_4068937 : Nat := 118140960795 + 4068937 * 2 ^ 59
def prefixEnd_4068937 : Nat := 4983230072969 + 3 ^ 40 * 4068937 * 2
def baseEnd_4068937 : Nat := 696440144621150666324935

theorem tailTrace_4068937 : CollatzResearch.WordTrace tailWord_4068937 prefixEnd_4068937 696440144621150666324935 := by
  unfold tailWord_4068937
  simp only [CollatzResearch.WordTrace]
  refine ⟨148406324459943642959373065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98937549639962428639582043 148406324459943642959373065)
  ·
    refine ⟨111304743344957732219529799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148406324459943642959373065 111304743344957732219529799)
    ·
      refine ⟨166957115017436598329294699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111304743344957732219529799 166957115017436598329294699)
      ·
        refine ⟨250435672526154897493942049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166957115017436598329294699 250435672526154897493942049)
        ·
          refine ⟨187826754394616173120456537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250435672526154897493942049 187826754394616173120456537)
          ·
            refine ⟨140870065795962129840342403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187826754394616173120456537 140870065795962129840342403)
            ·
              refine ⟨211305098693943194760513605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140870065795962129840342403 211305098693943194760513605)
              ·
                refine ⟨39619706005114349017596301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211305098693943194760513605 39619706005114349017596301)
                ·
                  refine ⟨14857389751917880881598613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39619706005114349017596301 14857389751917880881598613)
                  ·
                    refine ⟨696440144621150666324935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14857389751917880881598613 696440144621150666324935)
                    ·
                      rfl

theorem cell23_4068937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_4068937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068937 prefixEnd_4068937 := by exact prefixLift 4068937
  have htrace : WordTrace (prefixWord ++ tailWord_4068937) baseStart_4068937 baseEnd_4068937 := by
    simpa [prefixWord, tailWord_4068937, baseEnd_4068937] using wordTrace_append hprefix tailTrace_4068937
  have hstable : (prefixWord ++ tailWord_4068937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068937).length < 2 ^ (prefixWord ++ tailWord_4068937).sum := by decide
  have hdescent : baseEnd_4068937 < baseStart_4068937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068938 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_4068938 : Nat := 118140960795 + 4068938 * 2 ^ 59
def prefixEnd_4068938 : Nat := 4983230072969 + 3 ^ 40 * 4068938 * 2
def baseEnd_4068938 : Nat := 2089320947344106495062301

theorem tailTrace_4068938 : CollatzResearch.WordTrace tailWord_4068938 prefixEnd_4068938 2089320947344106495062301 := by
  unfold tailWord_4068938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37101590233235005032539867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98937573955293346753439645 37101590233235005032539867)
  ·
    refine ⟨55652385349852507548809801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37101590233235005032539867 55652385349852507548809801)
    ·
      refine ⟨41739289012389380661607351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55652385349852507548809801 41739289012389380661607351)
      ·
        refine ⟨62608933518584070992411027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41739289012389380661607351 62608933518584070992411027)
        ·
          refine ⟨93913400277876106488616541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62608933518584070992411027 93913400277876106488616541)
          ·
            refine ⟨35217525104203539933231203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93913400277876106488616541 35217525104203539933231203)
            ·
              refine ⟨52826287656305309899846805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35217525104203539933231203 52826287656305309899846805)
              ·
                refine ⟨2476232233889311401555319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52826287656305309899846805 2476232233889311401555319)
                ·
                  refine ⟨3714348350833967102332979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476232233889311401555319 3714348350833967102332979)
                  ·
                    refine ⟨5571522526250950653499469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3714348350833967102332979 5571522526250950653499469)
                    ·
                      refine ⟨2089320947344106495062301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5571522526250950653499469 2089320947344106495062301)
                      ·
                        rfl

theorem cell23_4068938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_4068938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068938 prefixEnd_4068938 := by exact prefixLift 4068938
  have htrace : WordTrace (prefixWord ++ tailWord_4068938) baseStart_4068938 baseEnd_4068938 := by
    simpa [prefixWord, tailWord_4068938, baseEnd_4068938] using wordTrace_append hprefix tailTrace_4068938
  have hstable : (prefixWord ++ tailWord_4068938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068938).length < 2 ^ (prefixWord ++ tailWord_4068938).sum := by decide
  have hdescent : baseEnd_4068938 < baseStart_4068938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068961 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_4068961 : Nat := 118140960795 + 4068961 * 2 ^ 59
def prefixEnd_4068961 : Nat := 4983230072969 + 3 ^ 40 * 4068961 * 2
def baseEnd_4068961 : Nat := 2089332757399159905074695

theorem tailTrace_4068961 : CollatzResearch.WordTrace tailWord_4068961 prefixEnd_4068961 2089332757399159905074695 := by
  unfold tailWord_4068961
  simp only [CollatzResearch.WordTrace]
  refine ⟨148407199811856695058246737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98938133207904463372164491 148407199811856695058246737)
  ·
    refine ⟨111305399858892521293685053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148407199811856695058246737 111305399858892521293685053)
    ·
      refine ⟨41739524947084695485131895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111305399858892521293685053 41739524947084695485131895)
      ·
        refine ⟨62609287420627043227697843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41739524947084695485131895 62609287420627043227697843)
        ·
          refine ⟨93913931130940564841546765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62609287420627043227697843 93913931130940564841546765)
          ·
            refine ⟨35217724174102711815580037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93913931130940564841546765 35217724174102711815580037)
            ·
              refine ⟨6603323282644258465421257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35217724174102711815580037 6603323282644258465421257)
              ·
                refine ⟨4952492461983193849065943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6603323282644258465421257 4952492461983193849065943)
                ·
                  refine ⟨7428738692974790773598915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952492461983193849065943 7428738692974790773598915)
                  ·
                    refine ⟨11143108039462186160398373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7428738692974790773598915 11143108039462186160398373)
                    ·
                      refine ⟨2089332757399159905074695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11143108039462186160398373 2089332757399159905074695)
                      ·
                        rfl

theorem cell23_4068961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_4068961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068961 prefixEnd_4068961 := by exact prefixLift 4068961
  have htrace : WordTrace (prefixWord ++ tailWord_4068961) baseStart_4068961 baseEnd_4068961 := by
    simpa [prefixWord, tailWord_4068961, baseEnd_4068961] using wordTrace_append hprefix tailTrace_4068961
  have hstable : (prefixWord ++ tailWord_4068961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068961).length < 2 ^ (prefixWord ++ tailWord_4068961).sum := by decide
  have hdescent : baseEnd_4068961 < baseStart_4068961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068981 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4068981 : Nat := 118140960795 + 4068981 * 2 ^ 59
def prefixEnd_4068981 : Nat := 4983230072969 + 3 ^ 40 * 4068981 * 2
def baseEnd_4068981 : Nat := 2089343027012249826824603

theorem tailTrace_4068981 : CollatzResearch.WordTrace tailWord_4068981 prefixEnd_4068981 2089343027012249826824603 := by
  unfold tailWord_4068981
  simp only [CollatzResearch.WordTrace]
  refine ⟨148407929271784238473974797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98938619514522825649316531 148407929271784238473974797)
  ·
    refine ⟨55652973476919089427740549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148407929271784238473974797 55652973476919089427740549)
    ·
      refine ⟨10434932526922329267701353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55652973476919089427740549 10434932526922329267701353)
      ·
        refine ⟨7826199395191746950776015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10434932526922329267701353 7826199395191746950776015)
        ·
          refine ⟨11739299092787620426164023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826199395191746950776015 11739299092787620426164023)
          ·
            refine ⟨17608948639181430639246035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739299092787620426164023 17608948639181430639246035)
            ·
              refine ⟨26413422958772145958869053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17608948639181430639246035 26413422958772145958869053)
              ·
                refine ⟨9905033609539554734575895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26413422958772145958869053 9905033609539554734575895)
                ·
                  refine ⟨14857550414309332101863843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905033609539554734575895 14857550414309332101863843)
                  ·
                    refine ⟨22286325621463998152795765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14857550414309332101863843 22286325621463998152795765)
                    ·
                      refine ⟨2089343027012249826824603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22286325621463998152795765 2089343027012249826824603)
                      ·
                        rfl

theorem cell23_4068981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4068981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068981 prefixEnd_4068981 := by exact prefixLift 4068981
  have htrace : WordTrace (prefixWord ++ tailWord_4068981) baseStart_4068981 baseEnd_4068981 := by
    simpa [prefixWord, tailWord_4068981, baseEnd_4068981] using wordTrace_append hprefix tailTrace_4068981
  have hstable : (prefixWord ++ tailWord_4068981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068981).length < 2 ^ (prefixWord ++ tailWord_4068981).sum := by decide
  have hdescent : baseEnd_4068981 < baseStart_4068981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069012 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4069012 : Nat := 118140960795 + 4069012 * 2 ^ 59
def prefixEnd_4069012 : Nat := 4983230072969 + 3 ^ 40 * 4069012 * 2
def baseEnd_4069012 : Nat := 2089358944912539205536961

theorem tailTrace_4069012 : CollatzResearch.WordTrace tailWord_4069012 prefixEnd_4069012 2089358944912539205536961 := by
  unfold tailWord_4069012
  simp only [CollatzResearch.WordTrace]
  refine ⟨74204529967335965384176645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98939373289781287178902193 74204529967335965384176645)
  ·
    refine ⟨13913349368875493509533121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74204529967335965384176645 13913349368875493509533121)
    ·
      refine ⟨10435012026656620132149841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13913349368875493509533121 10435012026656620132149841)
      ·
        refine ⟨7826259019992465099112381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10435012026656620132149841 7826259019992465099112381)
        ·
          refine ⟨2934847132497174412167143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7826259019992465099112381 2934847132497174412167143)
          ·
            refine ⟨4402270698745761618250715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934847132497174412167143 4402270698745761618250715)
            ·
              refine ⟨6603406048118642427376073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402270698745761618250715 6603406048118642427376073)
              ·
                refine ⟨4952554536088981820532055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6603406048118642427376073 4952554536088981820532055)
                ·
                  refine ⟨7428831804133472730798083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952554536088981820532055 7428831804133472730798083)
                  ·
                    refine ⟨11143247706200209096197125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7428831804133472730798083 11143247706200209096197125)
                    ·
                      refine ⟨2089358944912539205536961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11143247706200209096197125 2089358944912539205536961)
                      ·
                        rfl

theorem cell23_4069012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4069012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069012 prefixEnd_4069012 := by exact prefixLift 4069012
  have htrace : WordTrace (prefixWord ++ tailWord_4069012) baseStart_4069012 baseEnd_4069012 := by
    simpa [prefixWord, tailWord_4069012, baseEnd_4069012] using wordTrace_append hprefix tailTrace_4069012
  have hstable : (prefixWord ++ tailWord_4069012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069012).length < 2 ^ (prefixWord ++ tailWord_4069012).sum := by decide
  have hdescent : baseEnd_4069012 < baseStart_4069012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069032 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4069032 : Nat := 118140960795 + 4069032 * 2 ^ 59
def prefixEnd_4069032 : Nat := 4983230072969 + 3 ^ 40 * 4069032 * 2
def baseEnd_4069032 : Nat := 2089369214525629127286869

theorem tailTrace_4069032 : CollatzResearch.WordTrace tailWord_4069032 prefixEnd_4069032 2089369214525629127286869 := by
  unfold tailWord_4069032
  simp only [CollatzResearch.WordTrace]
  refine ⟨74204894697299737092040675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98939859596399649456054233 74204894697299737092040675)
  ·
    refine ⟨111307342045949605638061013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74204894697299737092040675 111307342045949605638061013)
    ·
      refine ⟨2608765829201943882142055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 111307342045949605638061013 2608765829201943882142055)
      ·
        refine ⟨3913148743802915823213083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2608765829201943882142055 3913148743802915823213083)
        ·
          refine ⟨5869723115704373734819625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913148743802915823213083 5869723115704373734819625)
          ·
            refine ⟨4402292336778280301114719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5869723115704373734819625 4402292336778280301114719)
            ·
              refine ⟨6603438505167420451672079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402292336778280301114719 6603438505167420451672079)
              ·
                refine ⟨9905157757751130677508119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6603438505167420451672079 9905157757751130677508119)
                ·
                  refine ⟨14857736636626696016262179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905157757751130677508119 14857736636626696016262179)
                  ·
                    refine ⟨22286604954940044024393269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14857736636626696016262179 22286604954940044024393269)
                    ·
                      refine ⟨2089369214525629127286869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22286604954940044024393269 2089369214525629127286869)
                      ·
                        rfl

theorem cell23_4069032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4069032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069032 prefixEnd_4069032 := by exact prefixLift 4069032
  have htrace : WordTrace (prefixWord ++ tailWord_4069032) baseStart_4069032 baseEnd_4069032 := by
    simpa [prefixWord, tailWord_4069032, baseEnd_4069032] using wordTrace_append hprefix tailTrace_4069032
  have hstable : (prefixWord ++ tailWord_4069032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069032).length < 2 ^ (prefixWord ++ tailWord_4069032).sum := by decide
  have hdescent : baseEnd_4069032 < baseStart_4069032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069046 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4069046 : Nat := 118140960795 + 4069046 * 2 ^ 59
def prefixEnd_4069046 : Nat := 4983230072969 + 3 ^ 40 * 4069046 * 2
def baseEnd_4069046 : Nat := 2089376403254792072511805

theorem tailTrace_4069046 : CollatzResearch.WordTrace tailWord_4069046 prefixEnd_4069046 2089376403254792072511805 := by
  unfold tailWord_4069046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275643751034297160943187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98940200011032503050060661 9275643751034297160943187)
  ·
    refine ⟨13913465626551445741414781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9275643751034297160943187 13913465626551445741414781)
    ·
      refine ⟨5217549609956792153030543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13913465626551445741414781 5217549609956792153030543)
      ·
        refine ⟨7826324414935188229545815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217549609956792153030543 7826324414935188229545815)
        ·
          refine ⟨11739486622402782344318723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826324414935188229545815 11739486622402782344318723)
          ·
            refine ⟨17609229933604173516478085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739486622402782344318723 17609229933604173516478085)
            ·
              refine ⟨3301730612550782534339641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17609229933604173516478085 3301730612550782534339641)
              ·
                refine ⟨2476297959413086900754731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301730612550782534339641 2476297959413086900754731)
                ·
                  refine ⟨3714446939119630351132097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476297959413086900754731 3714446939119630351132097)
                  ·
                    refine ⟨2785835204339722763349073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3714446939119630351132097 2785835204339722763349073)
                    ·
                      refine ⟨2089376403254792072511805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785835204339722763349073 2089376403254792072511805)
                      ·
                        rfl

theorem cell23_4069046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4069046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069046 prefixEnd_4069046 := by exact prefixLift 4069046
  have htrace : WordTrace (prefixWord ++ tailWord_4069046) baseStart_4069046 baseEnd_4069046 := by
    simpa [prefixWord, tailWord_4069046, baseEnd_4069046] using wordTrace_append hprefix tailTrace_4069046
  have hstable : (prefixWord ++ tailWord_4069046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069046).length < 2 ^ (prefixWord ++ tailWord_4069046).sum := by decide
  have hdescent : baseEnd_4069046 < baseStart_4069046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069062 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4069062 : Nat := 118140960795 + 4069062 * 2 ^ 59
def prefixEnd_4069062 : Nat := 4983230072969 + 3 ^ 40 * 4069062 * 2
def baseEnd_4069062 : Nat := 2089384618945264009911731

theorem tailTrace_4069062 : CollatzResearch.WordTrace tailWord_4069062 prefixEnd_4069062 2089384618945264009911731 := by
  unfold tailWord_4069062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637840112015337165864795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98940589056327192871782293 4637840112015337165864795)
  ·
    refine ⟨6956760168023005748797193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637840112015337165864795 6956760168023005748797193)
    ·
      refine ⟨5217570126017254311597895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6956760168023005748797193 5217570126017254311597895)
      ·
        refine ⟨7826355189025881467396843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217570126017254311597895 7826355189025881467396843)
        ·
          refine ⟨11739532783538822201095265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826355189025881467396843 11739532783538822201095265)
          ·
            refine ⟨8804649587654116650821449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11739532783538822201095265 8804649587654116650821449)
            ·
              refine ⟨6603487190740587488116087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8804649587654116650821449 6603487190740587488116087)
              ·
                refine ⟨9905230786110881232174131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6603487190740587488116087 9905230786110881232174131)
                ·
                  refine ⟨14857846179166321848261197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905230786110881232174131 14857846179166321848261197)
                  ·
                    refine ⟨5571692317187370693097949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14857846179166321848261197 5571692317187370693097949)
                    ·
                      refine ⟨2089384618945264009911731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5571692317187370693097949 2089384618945264009911731)
                      ·
                        rfl

theorem cell23_4069062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4069062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069062 prefixEnd_4069062 := by exact prefixLift 4069062
  have htrace : WordTrace (prefixWord ++ tailWord_4069062) baseStart_4069062 baseEnd_4069062 := by
    simpa [prefixWord, tailWord_4069062, baseEnd_4069062] using wordTrace_append hprefix tailTrace_4069062
  have hstable : (prefixWord ++ tailWord_4069062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069062).length < 2 ^ (prefixWord ++ tailWord_4069062).sum := by decide
  have hdescent : baseEnd_4069062 < baseStart_4069062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069089 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_4069089 : Nat := 118140960795 + 4069089 * 2 ^ 59
def prefixEnd_4069089 : Nat := 4983230072969 + 3 ^ 40 * 4069089 * 2
def baseEnd_4069089 : Nat := 2089398482922935404274107

theorem tailTrace_4069089 : CollatzResearch.WordTrace tailWord_4069089 prefixEnd_4069089 2089398482922935404274107 := by
  unfold tailWord_4069089
  simp only [CollatzResearch.WordTrace]
  refine ⟨148411868355392972918906321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98941245570261981945937547 148411868355392972918906321)
  ·
    refine ⟨111308901266544729689179741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148411868355392972918906321 111308901266544729689179741)
    ·
      refine ⟨41740837974954273633442403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111308901266544729689179741 41740837974954273633442403)
      ·
        refine ⟨62611256962431410450163605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41740837974954273633442403 62611256962431410450163605)
        ·
          refine ⟨2934902670113972364851419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62611256962431410450163605 2934902670113972364851419)
          ·
            refine ⟨4402354005170958547277129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934902670113972364851419 4402354005170958547277129)
            ·
              refine ⟨3301765503878218910457847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402354005170958547277129 3301765503878218910457847)
              ·
                refine ⟨4952648255817328365686771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301765503878218910457847 4952648255817328365686771)
                ·
                  refine ⟨7428972383725992548530157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952648255817328365686771 7428972383725992548530157)
                  ·
                    refine ⟨2785864643897247205698809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7428972383725992548530157 2785864643897247205698809)
                    ·
                      refine ⟨2089398482922935404274107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785864643897247205698809 2089398482922935404274107)
                      ·
                        rfl

theorem cell23_4069089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_4069089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069089 prefixEnd_4069089 := by exact prefixLift 4069089
  have htrace : WordTrace (prefixWord ++ tailWord_4069089) baseStart_4069089 baseEnd_4069089 := by
    simpa [prefixWord, tailWord_4069089, baseEnd_4069089] using wordTrace_append hprefix tailTrace_4069089
  have hstable : (prefixWord ++ tailWord_4069089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069089).length < 2 ^ (prefixWord ++ tailWord_4069089).sum := by decide
  have hdescent : baseEnd_4069089 < baseStart_4069089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069111 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 7, 2]
def baseStart_4069111 : Nat := 118140960795 + 4069111 * 2 ^ 59
def prefixEnd_4069111 : Nat := 4983230072969 + 3 ^ 40 * 4069111 * 2
def baseEnd_4069111 : Nat := 2089409779497334318199005

theorem tailTrace_4069111 : CollatzResearch.WordTrace tailWord_4069111 prefixEnd_4069111 2089409779497334318199005 := by
  unfold tailWord_4069111
  simp only [CollatzResearch.WordTrace]
  refine ⟨148412670761313270676207187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98941780507542180450804791 148412670761313270676207187)
  ·
    refine ⟨222619006141969906014310781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148412670761313270676207187 222619006141969906014310781)
    ·
      refine ⟨83482127303238714755366543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222619006141969906014310781 83482127303238714755366543)
      ·
        refine ⟨125223190954858072133049815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83482127303238714755366543 125223190954858072133049815)
        ·
          refine ⟨187834786432287108199574723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125223190954858072133049815 187834786432287108199574723)
          ·
            refine ⟨281752179648430662299362085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187834786432287108199574723 281752179648430662299362085)
            ·
              refine ⟨52828533684080749181130391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281752179648430662299362085 52828533684080749181130391)
              ·
                refine ⟨79242800526121123771695587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52828533684080749181130391 79242800526121123771695587)
                ·
                  refine ⟨118864200789181685657543381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79242800526121123771695587 118864200789181685657543381)
                  ·
                    refine ⟨2785879705996445757598673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118864200789181685657543381 2785879705996445757598673)
                    ·
                      refine ⟨2089409779497334318199005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785879705996445757598673 2089409779497334318199005)
                      ·
                        rfl

theorem cell23_4069111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_4069111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069111 prefixEnd_4069111 := by exact prefixLift 4069111
  have htrace : WordTrace (prefixWord ++ tailWord_4069111) baseStart_4069111 baseEnd_4069111 := by
    simpa [prefixWord, tailWord_4069111, baseEnd_4069111] using wordTrace_append hprefix tailTrace_4069111
  have hstable : (prefixWord ++ tailWord_4069111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069111).length < 2 ^ (prefixWord ++ tailWord_4069111).sum := by decide
  have hdescent : baseEnd_4069111 < baseStart_4069111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069114 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_4069114 : Nat := 118140960795 + 4069114 * 2 ^ 59
def prefixEnd_4069114 : Nat := 4983230072969 + 3 ^ 40 * 4069114 * 2
def baseEnd_4069114 : Nat := 2089411319939297806461491

theorem tailTrace_4069114 : CollatzResearch.WordTrace tailWord_4069114 prefixEnd_4069114 2089411319939297806461491 := by
  unfold tailWord_4069114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37103195045075600547141599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98941853453534934792377597 37103195045075600547141599)
  ·
    refine ⟨55654792567613400820712399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37103195045075600547141599 55654792567613400820712399)
    ·
      refine ⟨83482188851420101231068599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55654792567613400820712399 83482188851420101231068599)
      ·
        refine ⟨125223283277130151846602899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83482188851420101231068599 125223283277130151846602899)
        ·
          refine ⟨187834924915695227769904349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125223283277130151846602899 187834924915695227769904349)
          ·
            refine ⟨70438096843385710413714131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187834924915695227769904349 70438096843385710413714131)
            ·
              refine ⟨105657145265078565620571197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70438096843385710413714131 105657145265078565620571197)
              ·
                refine ⟨39621429474404462107714199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105657145265078565620571197 39621429474404462107714199)
                ·
                  refine ⟨59432144211606693161571299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39621429474404462107714199 59432144211606693161571299)
                  ·
                    refine ⟨89148216317410039742356949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59432144211606693161571299 89148216317410039742356949)
                    ·
                      refine ⟨2089411319939297806461491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89148216317410039742356949 2089411319939297806461491)
                      ·
                        rfl

theorem cell23_4069114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_4069114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069114 prefixEnd_4069114 := by exact prefixLift 4069114
  have htrace : WordTrace (prefixWord ++ tailWord_4069114) baseStart_4069114 baseEnd_4069114 := by
    simpa [prefixWord, tailWord_4069114, baseEnd_4069114] using wordTrace_append hprefix tailTrace_4069114
  have hstable : (prefixWord ++ tailWord_4069114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069114).length < 2 ^ (prefixWord ++ tailWord_4069114).sum := by decide
  have hdescent : baseEnd_4069114 < baseStart_4069114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069138 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4069138 : Nat := 118140960795 + 4069138 * 2 ^ 59
def prefixEnd_4069138 : Nat := 4983230072969 + 3 ^ 40 * 4069138 * 2
def baseEnd_4069138 : Nat := 696474547825001904187127

theorem tailTrace_4069138 : CollatzResearch.WordTrace tailWord_4069138 prefixEnd_4069138 696474547825001904187127 := by
  unfold tailWord_4069138
  simp only [CollatzResearch.WordTrace]
  refine ⟨37103413883053863571860017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98942437021476969524960045 37103413883053863571860017)
  ·
    refine ⟨27827560412290397678895013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37103413883053863571860017 27827560412290397678895013)
    ·
      refine ⟨5217667577304449564792815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27827560412290397678895013 5217667577304449564792815)
      ·
        refine ⟨7826501365956674347189223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217667577304449564792815 7826501365956674347189223)
        ·
          refine ⟨11739752048935011520783835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826501365956674347189223 11739752048935011520783835)
          ·
            refine ⟨17609628073402517281175753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739752048935011520783835 17609628073402517281175753)
            ·
              refine ⟨13207221055051887960881815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17609628073402517281175753 13207221055051887960881815)
              ·
                refine ⟨19810831582577831941322723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207221055051887960881815 19810831582577831941322723)
                ·
                  refine ⟨29716247373866747911984085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19810831582577831941322723 29716247373866747911984085)
                  ·
                    refine ⟨696474547825001904187127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29716247373866747911984085 696474547825001904187127)
                    ·
                      rfl

theorem cell23_4069138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4069138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069138 prefixEnd_4069138 := by exact prefixLift 4069138
  have htrace : WordTrace (prefixWord ++ tailWord_4069138) baseStart_4069138 baseEnd_4069138 := by
    simpa [prefixWord, tailWord_4069138, baseEnd_4069138] using wordTrace_append hprefix tailTrace_4069138
  have hstable : (prefixWord ++ tailWord_4069138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069138).length < 2 ^ (prefixWord ++ tailWord_4069138).sum := by decide
  have hdescent : baseEnd_4069138 < baseStart_4069138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069141 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4069141 : Nat := 118140960795 + 4069141 * 2 ^ 59
def prefixEnd_4069141 : Nat := 4983230072969 + 3 ^ 40 * 4069141 * 2
def baseEnd_4069141 : Nat := 2089425183916969200823867

theorem tailTrace_4069141 : CollatzResearch.WordTrace tailWord_4069141 prefixEnd_4069141 2089425183916969200823867 := by
  unfold tailWord_4069141
  simp only [CollatzResearch.WordTrace]
  refine ⟨148413764951204585799799277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98942509967469723866532851 148413764951204585799799277)
  ·
    refine ⟨55655161856701719674924729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148413764951204585799799277 55655161856701719674924729)
    ·
      refine ⟨41741371392526289756193547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55655161856701719674924729 41741371392526289756193547)
      ·
        refine ⟨62612057088789434634290321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41741371392526289756193547 62612057088789434634290321)
        ·
          refine ⟨46959042816592075975717741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62612057088789434634290321 46959042816592075975717741)
          ·
            refine ⟨17609641056222028490894153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46959042816592075975717741 17609641056222028490894153)
            ·
              refine ⟨13207230792166521368170615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17609641056222028490894153 13207230792166521368170615)
              ·
                refine ⟨19810846188249782052255923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207230792166521368170615 19810846188249782052255923)
                ·
                  refine ⟨29716269282374673078383885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19810846188249782052255923 29716269282374673078383885)
                  ·
                    refine ⟨11143600980890502404393957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29716269282374673078383885 11143600980890502404393957)
                    ·
                      refine ⟨2089425183916969200823867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11143600980890502404393957 2089425183916969200823867)
                      ·
                        rfl

theorem cell23_4069141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4069141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069141 prefixEnd_4069141 := by exact prefixLift 4069141
  have htrace : WordTrace (prefixWord ++ tailWord_4069141) baseStart_4069141 baseEnd_4069141 := by
    simpa [prefixWord, tailWord_4069141, baseEnd_4069141] using wordTrace_append hprefix tailTrace_4069141
  have hstable : (prefixWord ++ tailWord_4069141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069141).length < 2 ^ (prefixWord ++ tailWord_4069141).sum := by decide
  have hdescent : baseEnd_4069141 < baseStart_4069141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069191 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_4069191 : Nat := 118140960795 + 4069191 * 2 ^ 59
def prefixEnd_4069191 : Nat := 4983230072969 + 3 ^ 40 * 4069191 * 2
def baseEnd_4069191 : Nat := 2089450857949694005198637

theorem tailTrace_4069191 : CollatzResearch.WordTrace tailWord_4069191 prefixEnd_4069191 2089450857949694005198637 := by
  unfold tailWord_4069191
  simp only [CollatzResearch.WordTrace]
  refine ⟨148415588601023444339119427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98943725734015629559412951 148415588601023444339119427)
  ·
    refine ⟨222623382901535166508679141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148415588601023444339119427 222623382901535166508679141)
    ·
      refine ⟨41741884294037843720377339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222623382901535166508679141 41741884294037843720377339)
      ·
        refine ⟨62612826441056765580566009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41741884294037843720377339 62612826441056765580566009)
        ·
          refine ⟨46959619830792574185424507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62612826441056765580566009 46959619830792574185424507)
          ·
            refine ⟨70439429746188861278136761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46959619830792574185424507 70439429746188861278136761)
            ·
              refine ⟨52829572309641645958602571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70439429746188861278136761 52829572309641645958602571)
              ·
                refine ⟨79244358464462468937903857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52829572309641645958602571 79244358464462468937903857)
                ·
                  refine ⟨59433268848346851703427893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79244358464462468937903857 59433268848346851703427893)
                  ·
                    refine ⟨5571868954532517347196365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59433268848346851703427893 5571868954532517347196365)
                    ·
                      refine ⟨2089450857949694005198637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5571868954532517347196365 2089450857949694005198637)
                      ·
                        rfl

theorem cell23_4069191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_4069191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069191 prefixEnd_4069191 := by exact prefixLift 4069191
  have htrace : WordTrace (prefixWord ++ tailWord_4069191) baseStart_4069191 baseEnd_4069191 := by
    simpa [prefixWord, tailWord_4069191, baseEnd_4069191] using wordTrace_append hprefix tailTrace_4069191
  have hstable : (prefixWord ++ tailWord_4069191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069191).length < 2 ^ (prefixWord ++ tailWord_4069191).sum := by decide
  have hdescent : baseEnd_4069191 < baseStart_4069191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069219 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 1, 4]
def baseStart_4069219 : Nat := 118140960795 + 4069219 * 2 ^ 59
def prefixEnd_4069219 : Nat := 4983230072969 + 3 ^ 40 * 4069219 * 2
def baseEnd_4069219 : Nat := 696488411802673298549503

theorem tailTrace_4069219 : CollatzResearch.WordTrace tailWord_4069219 prefixEnd_4069219 696488411802673298549503 := by
  unfold tailWord_4069219
  simp only [CollatzResearch.WordTrace]
  refine ⟨148416609844922005121138711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98944406563281336747425807 148416609844922005121138711)
  ·
    refine ⟨222624914767383007681708067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148416609844922005121138711 222624914767383007681708067)
    ·
      refine ⟨333937372151074511522562101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222624914767383007681708067 333937372151074511522562101)
      ·
        refine ⟨31306628639163235455240197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333937372151074511522562101 31306628639163235455240197)
        ·
          refine ⟨5869992869843106647857537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31306628639163235455240197 5869992869843106647857537)
          ·
            refine ⟨4402494652382329985893153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5869992869843106647857537 4402494652382329985893153)
            ·
              refine ⟨3301870989286747489419865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402494652382329985893153 3301870989286747489419865)
              ·
                refine ⟨2476403241965060617064899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301870989286747489419865 2476403241965060617064899)
                ·
                  refine ⟨3714604862947590925597349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476403241965060617064899 3714604862947590925597349)
                  ·
                    refine ⟨696488411802673298549503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3714604862947590925597349 696488411802673298549503)
                    ·
                      rfl

theorem cell23_4069219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 4].length) (baseStart_4069219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069219 prefixEnd_4069219 := by exact prefixLift 4069219
  have htrace : WordTrace (prefixWord ++ tailWord_4069219) baseStart_4069219 baseEnd_4069219 := by
    simpa [prefixWord, tailWord_4069219, baseEnd_4069219] using wordTrace_append hprefix tailTrace_4069219
  have hstable : (prefixWord ++ tailWord_4069219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069219).length < 2 ^ (prefixWord ++ tailWord_4069219).sum := by decide
  have hdescent : baseEnd_4069219 < baseStart_4069219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069248 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4]
def baseStart_4069248 : Nat := 118140960795 + 4069248 * 2 ^ 59
def prefixEnd_4069248 : Nat := 4983230072969 + 3 ^ 40 * 4069248 * 2
def baseEnd_4069248 : Nat := 2089480126347000282185875

theorem tailTrace_4069248 : CollatzResearch.WordTrace tailWord_4069248 prefixEnd_4069248 2089480126347000282185875 := by
  unfold tailWord_4069248
  simp only [CollatzResearch.WordTrace]
  refine ⟨74208833780908471536972199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98945111707877962049296265 74208833780908471536972199)
  ·
    refine ⟨111313250671362707305458299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74208833780908471536972199 111313250671362707305458299)
    ·
      refine ⟨166969876007044060958187449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111313250671362707305458299 166969876007044060958187449)
      ·
        refine ⟨125227407005283045718640587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166969876007044060958187449 125227407005283045718640587)
        ·
          refine ⟨187841110507924568577960881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125227407005283045718640587 187841110507924568577960881)
          ·
            refine ⟨140880832880943426433470661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187841110507924568577960881 140880832880943426433470661)
            ·
              refine ⟨26415156165176892456275749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140880832880943426433470661 26415156165176892456275749)
              ·
                refine ⟨4952841780970667335551703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26415156165176892456275749 4952841780970667335551703)
                ·
                  refine ⟨7429262671456001003327555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952841780970667335551703 7429262671456001003327555)
                  ·
                    refine ⟨11143894007184001504991333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429262671456001003327555 11143894007184001504991333)
                    ·
                      refine ⟨2089480126347000282185875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11143894007184001504991333 2089480126347000282185875)
                      ·
                        rfl

theorem cell23_4069248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_4069248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069248 prefixEnd_4069248 := by exact prefixLift 4069248
  have htrace : WordTrace (prefixWord ++ tailWord_4069248) baseStart_4069248 baseEnd_4069248 := by
    simpa [prefixWord, tailWord_4069248, baseEnd_4069248] using wordTrace_append hprefix tailTrace_4069248
  have hstable : (prefixWord ++ tailWord_4069248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069248).length < 2 ^ (prefixWord ++ tailWord_4069248).sum := by decide
  have hdescent : baseEnd_4069248 < baseStart_4069248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069262 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_4069262 : Nat := 118140960795 + 4069262 * 2 ^ 59
def prefixEnd_4069262 : Nat := 4983230072969 + 3 ^ 40 * 4069262 * 2
def baseEnd_4069262 : Nat := 696495771692054409136937

theorem tailTrace_4069262 : CollatzResearch.WordTrace tailWord_4069262 prefixEnd_4069262 696495771692054409136937 := by
  unfold tailWord_4069262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18552272272970777933119255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98945452122510815643302693 18552272272970777933119255)
  ·
    refine ⟨27828408409456166899678883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18552272272970777933119255 27828408409456166899678883)
    ·
      refine ⟨41742612614184250349518325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27828408409456166899678883 41742612614184250349518325)
      ·
        refine ⟨3913369932579773470267343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41742612614184250349518325 3913369932579773470267343)
        ·
          refine ⟨5870054898869660205401015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913369932579773470267343 5870054898869660205401015)
          ·
            refine ⟨8805082348304490308101523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870054898869660205401015 8805082348304490308101523)
            ·
              refine ⟨13207623522456735462152285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805082348304490308101523 13207623522456735462152285)
              ·
                refine ⟨4952858820921275798307107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13207623522456735462152285 4952858820921275798307107)
                ·
                  refine ⟨7429288231381913697460661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952858820921275798307107 7429288231381913697460661)
                  ·
                    refine ⟨696495771692054409136937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7429288231381913697460661 696495771692054409136937)
                    ·
                      rfl

theorem cell23_4069262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_4069262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069262 prefixEnd_4069262 := by exact prefixLift 4069262
  have htrace : WordTrace (prefixWord ++ tailWord_4069262) baseStart_4069262 baseEnd_4069262 := by
    simpa [prefixWord, tailWord_4069262, baseEnd_4069262] using wordTrace_append hprefix tailTrace_4069262
  have hstable : (prefixWord ++ tailWord_4069262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069262).length < 2 ^ (prefixWord ++ tailWord_4069262).sum := by decide
  have hdescent : baseEnd_4069262 < baseStart_4069262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069265 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 1, 1, 4]
def baseStart_4069265 : Nat := 118140960795 + 4069265 * 2 ^ 59
def prefixEnd_4069265 : Nat := 4983230072969 + 3 ^ 40 * 4069265 * 2
def baseEnd_4069265 : Nat := 2089488855518126715673297

theorem tailTrace_4069265 : CollatzResearch.WordTrace tailWord_4069265 prefixEnd_4069265 2089488855518126715673297 := by
  unfold tailWord_4069265
  simp only [CollatzResearch.WordTrace]
  refine ⟨148418287602755354977313249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98945525068503569984875499 148418287602755354977313249)
  ·
    refine ⟨111313715702066516232984937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148418287602755354977313249 111313715702066516232984937)
    ·
      refine ⟨83485286776549887174738703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111313715702066516232984937 83485286776549887174738703)
      ·
        refine ⟨125227930164824830762108055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83485286776549887174738703 125227930164824830762108055)
        ·
          refine ⟨187841895247237246143162083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125227930164824830762108055 187841895247237246143162083)
          ·
            refine ⟨281762842870855869214743125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187841895247237246143162083 281762842870855869214743125)
            ·
              refine ⟨3301908314892842217360271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 281762842870855869214743125 3301908314892842217360271)
              ·
                refine ⟨4952862472339263326040407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301908314892842217360271 4952862472339263326040407)
                ·
                  refine ⟨7429293708508894989060611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952862472339263326040407 7429293708508894989060611)
                  ·
                    refine ⟨11143940562763342483590917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429293708508894989060611 11143940562763342483590917)
                    ·
                      refine ⟨2089488855518126715673297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11143940562763342483590917 2089488855518126715673297)
                      ·
                        rfl

theorem cell23_4069265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_4069265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069265 prefixEnd_4069265 := by exact prefixLift 4069265
  have htrace : WordTrace (prefixWord ++ tailWord_4069265) baseStart_4069265 baseEnd_4069265 := by
    simpa [prefixWord, tailWord_4069265, baseEnd_4069265] using wordTrace_append hprefix tailTrace_4069265
  have hstable : (prefixWord ++ tailWord_4069265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069265).length < 2 ^ (prefixWord ++ tailWord_4069265).sum := by decide
  have hdescent : baseEnd_4069265 < baseStart_4069265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069271 : List Nat := [1, 1, 3, 3, 1, 4, 10]
def baseStart_4069271 : Nat := 118140960795 + 4069271 * 2 ^ 59
def prefixEnd_4069271 : Nat := 4983230072969 + 3 ^ 40 * 4069271 * 2
def baseEnd_4069271 : Nat := 25796196745704366570349

theorem tailTrace_4069271 : CollatzResearch.WordTrace tailWord_4069271 prefixEnd_4069271 25796196745704366570349 := by
  unfold tailWord_4069271
  simp only [CollatzResearch.WordTrace]
  refine ⟨148418506440733618002031667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98945670960489078668021111 148418506440733618002031667)
  ·
    refine ⟨222627759661100427003047501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148418506440733618002031667 222627759661100427003047501)
    ·
      refine ⟨83485409872912660126142813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222627759661100427003047501 83485409872912660126142813)
      ·
        refine ⟨31307028702342247547303555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83485409872912660126142813 31307028702342247547303555)
        ·
          refine ⟨46960543053513371320955333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31307028702342247547303555 46960543053513371320955333)
          ·
            refine ⟨8805101822533757122679125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46960543053513371320955333 8805101822533757122679125)
            ·
              refine ⟨25796196745704366570349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8805101822533757122679125 25796196745704366570349)
              ·
                rfl

theorem cell23_4069271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 10].length) (baseStart_4069271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069271 prefixEnd_4069271 := by exact prefixLift 4069271
  have htrace : WordTrace (prefixWord ++ tailWord_4069271) baseStart_4069271 baseEnd_4069271 := by
    simpa [prefixWord, tailWord_4069271, baseEnd_4069271] using wordTrace_append hprefix tailTrace_4069271
  have hstable : (prefixWord ++ tailWord_4069271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069271).length < 2 ^ (prefixWord ++ tailWord_4069271).sum := by decide
  have hdescent : baseEnd_4069271 < baseStart_4069271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069311 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_4069311 : Nat := 118140960795 + 4069311 * 2 ^ 59
def prefixEnd_4069311 : Nat := 4983230072969 + 3 ^ 40 * 4069311 * 2
def baseEnd_4069311 : Nat := 2089512475628233535698085

theorem tailTrace_4069311 : CollatzResearch.WordTrace tailWord_4069311 prefixEnd_4069311 2089512475628233535698085 := by
  unfold tailWord_4069311
  simp only [CollatzResearch.WordTrace]
  refine ⟨148419965360588704833487787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98946643573725803222325191 148419965360588704833487787)
  ·
    refine ⟨222629948040883057250231681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148419965360588704833487787 222629948040883057250231681)
    ·
      refine ⟨166972461030662292937673761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222629948040883057250231681 166972461030662292937673761)
      ·
        refine ⟨125229345772996719703255321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166972461030662292937673761 125229345772996719703255321)
        ·
          refine ⟨93922009329747539777441491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125229345772996719703255321 93922009329747539777441491)
          ·
            refine ⟨140883013994621309666162237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93922009329747539777441491 140883013994621309666162237)
            ·
              refine ⟨52831130247982991124810839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140883013994621309666162237 52831130247982991124810839)
              ·
                refine ⟨79246695371974486687216259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52831130247982991124810839 79246695371974486687216259)
                ·
                  refine ⟨118870043057961730030824389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79246695371974486687216259 118870043057961730030824389)
                  ·
                    refine ⟨22288133073367824380779573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118870043057961730030824389 22288133073367824380779573)
                    ·
                      refine ⟨2089512475628233535698085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22288133073367824380779573 2089512475628233535698085)
                      ·
                        rfl

theorem cell23_4069311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_4069311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069311 prefixEnd_4069311 := by exact prefixLift 4069311
  have htrace : WordTrace (prefixWord ++ tailWord_4069311) baseStart_4069311 baseEnd_4069311 := by
    simpa [prefixWord, tailWord_4069311, baseEnd_4069311] using wordTrace_append hprefix tailTrace_4069311
  have hstable : (prefixWord ++ tailWord_4069311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069311).length < 2 ^ (prefixWord ++ tailWord_4069311).sum := by decide
  have hdescent : baseEnd_4069311 < baseStart_4069311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069332 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4069332 : Nat := 118140960795 + 4069332 * 2 ^ 59
def prefixEnd_4069332 : Nat := 4983230072969 + 3 ^ 40 * 4069332 * 2
def baseEnd_4069332 : Nat := 2089523258721977953535489

theorem tailTrace_4069332 : CollatzResearch.WordTrace tailWord_4069332 prefixEnd_4069332 2089523258721977953535489 := by
  unfold tailWord_4069332
  simp only [CollatzResearch.WordTrace]
  refine ⟨74210365646756312710001125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98947154195675083613334833 74210365646756312710001125)
  ·
    refine ⟨13914443558766808633125211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74210365646756312710001125 13914443558766808633125211)
    ·
      refine ⟨20871665338150212949687817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13914443558766808633125211 20871665338150212949687817)
      ·
        refine ⟨15653749003612659712265863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20871665338150212949687817 15653749003612659712265863)
        ·
          refine ⟨23480623505418989568398795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15653749003612659712265863 23480623505418989568398795)
          ·
            refine ⟨35220935258128484352598193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23480623505418989568398795 35220935258128484352598193)
            ·
              refine ⟨26415701443596363264448645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35220935258128484352598193 26415701443596363264448645)
              ·
                refine ⟨4952944020674318112084121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26415701443596363264448645 4952944020674318112084121)
                ·
                  refine ⟨3714708015505738584063091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4952944020674318112084121 3714708015505738584063091)
                  ·
                    refine ⟨5572062023258607876094637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3714708015505738584063091 5572062023258607876094637)
                    ·
                      refine ⟨2089523258721977953535489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572062023258607876094637 2089523258721977953535489)
                      ·
                        rfl

theorem cell23_4069332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4069332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069332 prefixEnd_4069332 := by exact prefixLift 4069332
  have htrace : WordTrace (prefixWord ++ tailWord_4069332) baseStart_4069332 baseEnd_4069332 := by
    simpa [prefixWord, tailWord_4069332, baseEnd_4069332] using wordTrace_append hprefix tailTrace_4069332
  have hstable : (prefixWord ++ tailWord_4069332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069332).length < 2 ^ (prefixWord ++ tailWord_4069332).sum := by decide
  have hdescent : baseEnd_4069332 < baseStart_4069332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069405 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_4069405 : Nat := 118140960795 + 4069405 * 2 ^ 59
def prefixEnd_4069405 : Nat := 4983230072969 + 3 ^ 40 * 4069405 * 2
def baseEnd_4069405 : Nat := 2089560742809756167922653

theorem tailTrace_4069405 : CollatzResearch.WordTrace tailWord_4069405 prefixEnd_4069405 2089560742809756167922653 := by
  unfold tailWord_4069405
  simp only [CollatzResearch.WordTrace]
  refine ⟨148423393822248158887409669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98948929214832105924939779 148423393822248158887409669)
  ·
    refine ⟨27829386341671529791389313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148423393822248158887409669 27829386341671529791389313)
    ·
      refine ⟨20872039756253647343541985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27829386341671529791389313 20872039756253647343541985)
      ·
        refine ⟨15654029817190235507656489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20872039756253647343541985 15654029817190235507656489)
        ·
          refine ⟨11740522362892676630742367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15654029817190235507656489 11740522362892676630742367)
          ·
            refine ⟨17610783544339014946113551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740522362892676630742367 17610783544339014946113551)
            ·
              refine ⟨26416175316508522419170327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17610783544339014946113551 26416175316508522419170327)
              ·
                refine ⟨39624262974762783628755491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26416175316508522419170327 39624262974762783628755491)
                ·
                  refine ⟨59436394462144175443133237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39624262974762783628755491 59436394462144175443133237)
                  ·
                    refine ⟨5572161980826016447793741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59436394462144175443133237 5572161980826016447793741)
                    ·
                      refine ⟨2089560742809756167922653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572161980826016447793741 2089560742809756167922653)
                      ·
                        rfl

theorem cell23_4069405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_4069405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069405 prefixEnd_4069405 := by exact prefixLift 4069405
  have htrace : WordTrace (prefixWord ++ tailWord_4069405) baseStart_4069405 baseEnd_4069405 := by
    simpa [prefixWord, tailWord_4069405, baseEnd_4069405] using wordTrace_append hprefix tailTrace_4069405
  have hstable : (prefixWord ++ tailWord_4069405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069405).length < 2 ^ (prefixWord ++ tailWord_4069405).sum := by decide
  have hdescent : baseEnd_4069405 < baseStart_4069405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069425 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 2, 5]
def baseStart_4069425 : Nat := 118140960795 + 4069425 * 2 ^ 59
def prefixEnd_4069425 : Nat := 4983230072969 + 3 ^ 40 * 4069425 * 2
def baseEnd_4069425 : Nat := 696523670807615363224187

theorem tailTrace_4069425 : CollatzResearch.WordTrace tailWord_4069425 prefixEnd_4069425 696523670807615363224187 := by
  unfold tailWord_4069425
  simp only [CollatzResearch.WordTrace]
  refine ⟨148424123282175702303137729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98949415521450468202091819 148424123282175702303137729)
  ·
    refine ⟨111318092461631776727353297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148424123282175702303137729 111318092461631776727353297)
    ·
      refine ⟨83488569346223832545514973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111318092461631776727353297 83488569346223832545514973)
      ·
        refine ⟨31308213504833937204568115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83488569346223832545514973 31308213504833937204568115)
        ·
          refine ⟨46962320257250905806852173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31308213504833937204568115 46962320257250905806852173)
          ·
            refine ⟨17610870096469089677569565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46962320257250905806852173 17610870096469089677569565)
            ·
              refine ⟨6604076286175908629088587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17610870096469089677569565 6604076286175908629088587)
              ·
                refine ⟨9906114429263862943632881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6604076286175908629088587 9906114429263862943632881)
                ·
                  refine ⟨7429585821947897207724661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9906114429263862943632881 7429585821947897207724661)
                  ·
                    refine ⟨696523670807615363224187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7429585821947897207724661 696523670807615363224187)
                    ·
                      rfl

theorem cell23_4069425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_4069425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069425 prefixEnd_4069425 := by exact prefixLift 4069425
  have htrace : WordTrace (prefixWord ++ tailWord_4069425) baseStart_4069425 baseEnd_4069425 := by
    simpa [prefixWord, tailWord_4069425, baseEnd_4069425] using wordTrace_append hprefix tailTrace_4069425
  have hstable : (prefixWord ++ tailWord_4069425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069425).length < 2 ^ (prefixWord ++ tailWord_4069425).sum := by decide
  have hdescent : baseEnd_4069425 < baseStart_4069425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069562 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_4069562 : Nat := 118140960795 + 4069562 * 2 ^ 59
def prefixEnd_4069562 : Nat := 4983230072969 + 3 ^ 40 * 4069562 * 2
def baseEnd_4069562 : Nat := 696547119757504017886477

theorem tailTrace_4069562 : CollatzResearch.WordTrace tailWord_4069562 prefixEnd_4069562 696547119757504017886477 := by
  unfold tailWord_4069562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37107280020669843675218735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98952746721786249800583293 37107280020669843675218735)
  ·
    refine ⟨55660920031004765512828103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37107280020669843675218735 55660920031004765512828103)
    ·
      refine ⟨83491380046507148269242155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55660920031004765512828103 83491380046507148269242155)
      ·
        refine ⟨125237070069760722403863233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83491380046507148269242155 125237070069760722403863233)
        ·
          refine ⟨93927802552320541802897425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125237070069760722403863233 93927802552320541802897425)
          ·
            refine ⟨70445851914240406352173069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93927802552320541802897425 70445851914240406352173069)
            ·
              refine ⟨26417194467840152382064901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70445851914240406352173069 26417194467840152382064901)
              ·
                refine ⟨4953223962720028571637169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26417194467840152382064901 4953223962720028571637169)
                ·
                  refine ⟨3714917972040021428727877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953223962720028571637169 3714917972040021428727877)
                  ·
                    refine ⟨696547119757504017886477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3714917972040021428727877 696547119757504017886477)
                    ·
                      rfl

theorem cell23_4069562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_4069562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069562 prefixEnd_4069562 := by exact prefixLift 4069562
  have htrace : WordTrace (prefixWord ++ tailWord_4069562) baseStart_4069562 baseEnd_4069562 := by
    simpa [prefixWord, tailWord_4069562, baseEnd_4069562] using wordTrace_append hprefix tailTrace_4069562
  have hstable : (prefixWord ++ tailWord_4069562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069562).length < 2 ^ (prefixWord ++ tailWord_4069562).sum := by decide
  have hdescent : baseEnd_4069562 < baseStart_4069562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069565 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4069565 : Nat := 118140960795 + 4069565 * 2 ^ 59
def prefixEnd_4069565 : Nat := 4983230072969 + 3 ^ 40 * 4069565 * 2
def baseEnd_4069565 : Nat := 2089642899714475541921917

theorem tailTrace_4069565 : CollatzResearch.WordTrace tailWord_4069565 prefixEnd_4069565 2089642899714475541921917 := by
  unfold tailWord_4069565
  simp only [CollatzResearch.WordTrace]
  refine ⟨148429229501668506213234149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98952819667779004142156099 148429229501668506213234149)
  ·
    refine ⟨27830480531562844914981403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148429229501668506213234149 27830480531562844914981403)
    ·
      refine ⟨41745720797344267372472105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27830480531562844914981403 41745720797344267372472105)
      ·
        refine ⟨31309290598008200529354079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41745720797344267372472105 31309290598008200529354079)
        ·
          refine ⟨46963935897012300794031119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31309290598008200529354079 46963935897012300794031119)
          ·
            refine ⟨70445903845518451191046679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46963935897012300794031119 70445903845518451191046679)
            ·
              refine ⟨105668855768277676786570019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70445903845518451191046679 105668855768277676786570019)
              ·
                refine ⟨158503283652416515179855029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105668855768277676786570019 158503283652416515179855029)
                ·
                  refine ⟨14859682842414048298111409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158503283652416515179855029 14859682842414048298111409)
                  ·
                    refine ⟨11144762131810536223583557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14859682842414048298111409 11144762131810536223583557)
                    ·
                      refine ⟨2089642899714475541921917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11144762131810536223583557 2089642899714475541921917)
                      ·
                        rfl

theorem cell23_4069565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4069565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069565 prefixEnd_4069565 := by exact prefixLift 4069565
  have htrace : WordTrace (prefixWord ++ tailWord_4069565) baseStart_4069565 baseEnd_4069565 := by
    simpa [prefixWord, tailWord_4069565, baseEnd_4069565] using wordTrace_append hprefix tailTrace_4069565
  have hstable : (prefixWord ++ tailWord_4069565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069565).length < 2 ^ (prefixWord ++ tailWord_4069565).sum := by decide
  have hdescent : baseEnd_4069565 < baseStart_4069565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069582 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_4069582 : Nat := 118140960795 + 4069582 * 2 ^ 59
def prefixEnd_4069582 : Nat := 4983230072969 + 3 ^ 40 * 4069582 * 2
def baseEnd_4069582 : Nat := 2089651628885601975409339

theorem tailTrace_4069582 : CollatzResearch.WordTrace tailWord_4069582 prefixEnd_4069582 2089651628885601975409339 := by
  unfold tailWord_4069582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18553731192825864764575375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98953233028404612077735333 18553731192825864764575375)
  ·
    refine ⟨27830596789238797146863063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18553731192825864764575375 27830596789238797146863063)
    ·
      refine ⟨41745895183858195720294595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27830596789238797146863063 41745895183858195720294595)
      ·
        refine ⟨62618842775787293580441893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41745895183858195720294595 62618842775787293580441893)
        ·
          refine ⟨11741033020460117546332855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62618842775787293580441893 11741033020460117546332855)
          ·
            refine ⟨17611549530690176319499283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11741033020460117546332855 17611549530690176319499283)
            ·
              refine ⟨26417324296035264479248925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17611549530690176319499283 26417324296035264479248925)
              ·
                refine ⟨9906496611013224179718347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26417324296035264479248925 9906496611013224179718347)
                ·
                  refine ⟨14859744916519836269577521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9906496611013224179718347 14859744916519836269577521)
                  ·
                    refine ⟨11144808687389877202183141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14859744916519836269577521 11144808687389877202183141)
                    ·
                      refine ⟨2089651628885601975409339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11144808687389877202183141 2089651628885601975409339)
                      ·
                        rfl

theorem cell23_4069582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_4069582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069582 prefixEnd_4069582 := by exact prefixLift 4069582
  have htrace : WordTrace (prefixWord ++ tailWord_4069582) baseStart_4069582 baseEnd_4069582 := by
    simpa [prefixWord, tailWord_4069582, baseEnd_4069582] using wordTrace_append hprefix tailTrace_4069582
  have hstable : (prefixWord ++ tailWord_4069582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069582).length < 2 ^ (prefixWord ++ tailWord_4069582).sum := by decide
  have hdescent : baseEnd_4069582 < baseStart_4069582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069586 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4069586 : Nat := 118140960795 + 4069586 * 2 ^ 59
def prefixEnd_4069586 : Nat := 4983230072969 + 3 ^ 40 * 4069586 * 2
def baseEnd_4069586 : Nat := 2089653682808219959759321

theorem tailTrace_4069586 : CollatzResearch.WordTrace tailWord_4069586 prefixEnd_4069586 2089653682808219959759321 := by
  unfold tailWord_4069586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37107498858648106699937153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98953330289728284533165741 37107498858648106699937153)
  ·
    refine ⟨27830624143986080024952865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37107498858648106699937153 27830624143986080024952865)
    ·
      refine ⟨20872968107989560018714649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27830624143986080024952865 20872968107989560018714649)
      ·
        refine ⟨15654726080992170014035987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20872968107989560018714649 15654726080992170014035987)
        ·
          refine ⟨23482089121488255021053981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15654726080992170014035987 23482089121488255021053981)
          ·
            refine ⟨8805783420558095632895243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23482089121488255021053981 8805783420558095632895243)
            ·
              refine ⟨13208675130837143449342865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805783420558095632895243 13208675130837143449342865)
              ·
                refine ⟨9906506348127857587007149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13208675130837143449342865 9906506348127857587007149)
                ·
                  refine ⟨3714939880547946595127681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9906506348127857587007149 3714939880547946595127681)
                  ·
                    refine ⟨2786204910410959946345761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3714939880547946595127681 2786204910410959946345761)
                    ·
                      refine ⟨2089653682808219959759321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786204910410959946345761 2089653682808219959759321)
                      ·
                        rfl

theorem cell23_4069586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4069586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069586 prefixEnd_4069586 := by exact prefixLift 4069586
  have htrace : WordTrace (prefixWord ++ tailWord_4069586) baseStart_4069586 baseEnd_4069586 := by
    simpa [prefixWord, tailWord_4069586, baseEnd_4069586] using wordTrace_append hprefix tailTrace_4069586
  have hstable : (prefixWord ++ tailWord_4069586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069586).length < 2 ^ (prefixWord ++ tailWord_4069586).sum := by decide
  have hdescent : baseEnd_4069586 < baseStart_4069586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069592 : List Nat := [2, 1, 2, 2, 4, 2, 3, 7]
def baseStart_4069592 : Nat := 118140960795 + 4069592 * 2 ^ 59
def prefixEnd_4069592 : Nat := 4983230072969 + 3 ^ 40 * 4069592 * 2
def baseEnd_4069592 : Nat := 77394694951560997640159

theorem tailTrace_4069592 : CollatzResearch.WordTrace tailWord_4069592 prefixEnd_4069592 77394694951560997640159 := by
  unfold tailWord_4069592
  simp only [CollatzResearch.WordTrace]
  refine ⟨74215107136285344912233515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98953476181713793216311353 74215107136285344912233515)
  ·
    refine ⟨111322660704428017368350273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74215107136285344912233515 111322660704428017368350273)
    ·
      refine ⟨83491995528321013026262705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111322660704428017368350273 83491995528321013026262705)
      ·
        refine ⟨62618996646240759769697029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83491995528321013026262705 62618996646240759769697029)
        ·
          refine ⟨11741061871170142456818193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62618996646240759769697029 11741061871170142456818193)
          ·
            refine ⟨8805796403377606842613645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11741061871170142456818193 8805796403377606842613645)
            ·
              refine ⟨3302173651266602565980117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8805796403377606842613645 3302173651266602565980117)
              ·
                refine ⟨77394694951560997640159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3302173651266602565980117 77394694951560997640159)
                ·
                  rfl

theorem cell23_4069592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 7].length) (baseStart_4069592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069592 prefixEnd_4069592 := by exact prefixLift 4069592
  have htrace : WordTrace (prefixWord ++ tailWord_4069592) baseStart_4069592 baseEnd_4069592 := by
    simpa [prefixWord, tailWord_4069592, baseEnd_4069592] using wordTrace_append hprefix tailTrace_4069592
  have hstable : (prefixWord ++ tailWord_4069592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069592).length < 2 ^ (prefixWord ++ tailWord_4069592).sum := by decide
  have hdescent : baseEnd_4069592 < baseStart_4069592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069603 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4069603 : Nat := 118140960795 + 4069603 * 2 ^ 59
def prefixEnd_4069603 : Nat := 4983230072969 + 3 ^ 40 * 4069603 * 2
def baseEnd_4069603 : Nat := 2089662411979346393246743

theorem tailTrace_4069603 : CollatzResearch.WordTrace tailWord_4069603 prefixEnd_4069603 2089662411979346393246743 := by
  unfold tailWord_4069603
  simp only [CollatzResearch.WordTrace]
  refine ⟨148430615475530838703117463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98953743650353892468744975 148430615475530838703117463)
  ·
    refine ⟨222645923213296258054676195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148430615475530838703117463 222645923213296258054676195)
    ·
      refine ⟨333968884819944387082014293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222645923213296258054676195 333968884819944387082014293)
      ·
        refine ⟨3913697868983723286117355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 333968884819944387082014293 3913697868983723286117355)
        ·
          refine ⟨5870546803475584929176033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913697868983723286117355 5870546803475584929176033)
          ·
            refine ⟨4402910102606688696882025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5870546803475584929176033 4402910102606688696882025)
            ·
              refine ⟨3302182576955016522661519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402910102606688696882025 3302182576955016522661519)
              ·
                refine ⟨4953273865432524783992279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302182576955016522661519 4953273865432524783992279)
                ·
                  refine ⟨7429910798148787175988419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953273865432524783992279 7429910798148787175988419)
                  ·
                    refine ⟨11144866197223180763982629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429910798148787175988419 11144866197223180763982629)
                    ·
                      refine ⟨2089662411979346393246743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11144866197223180763982629 2089662411979346393246743)
                      ·
                        rfl

theorem cell23_4069603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4069603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069603 prefixEnd_4069603 := by exact prefixLift 4069603
  have htrace : WordTrace (prefixWord ++ tailWord_4069603) baseStart_4069603 baseEnd_4069603 := by
    simpa [prefixWord, tailWord_4069603, baseEnd_4069603] using wordTrace_append hprefix tailTrace_4069603
  have hstable : (prefixWord ++ tailWord_4069603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069603).length < 2 ^ (prefixWord ++ tailWord_4069603).sum := by decide
  have hdescent : baseEnd_4069603 < baseStart_4069603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069613 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_4069613 : Nat := 118140960795 + 4069613 * 2 ^ 59
def prefixEnd_4069613 : Nat := 4983230072969 + 3 ^ 40 * 4069613 * 2
def baseEnd_4069613 : Nat := 696555848928630451373899

theorem tailTrace_4069613 : CollatzResearch.WordTrace tailWord_4069613 prefixEnd_4069613 696555848928630451373899 := by
  unfold tailWord_4069613
  simp only [CollatzResearch.WordTrace]
  refine ⟨148430980205494610410981493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98953986803663073607320995 148430980205494610410981493)
  ·
    refine ⟨13915404394265119726029515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148430980205494610410981493 13915404394265119726029515)
    ·
      refine ⟨20873106591397679589044273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13915404394265119726029515 20873106591397679589044273)
      ·
        refine ⟨15654829943548259691783205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20873106591397679589044273 15654829943548259691783205)
        ·
          refine ⟨2935280614415298692209351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15654829943548259691783205 2935280614415298692209351)
          ·
            refine ⟨4402920921622948038314027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935280614415298692209351 4402920921622948038314027)
            ·
              refine ⟨6604381382434422057471041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402920921622948038314027 6604381382434422057471041)
              ·
                refine ⟨4953286036825816543103281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604381382434422057471041 4953286036825816543103281)
                ·
                  refine ⟨3714964527619362407327461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953286036825816543103281 3714964527619362407327461)
                  ·
                    refine ⟨696555848928630451373899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3714964527619362407327461 696555848928630451373899)
                    ·
                      rfl

theorem cell23_4069613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_4069613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069613 prefixEnd_4069613 := by exact prefixLift 4069613
  have htrace : WordTrace (prefixWord ++ tailWord_4069613) baseStart_4069613 baseEnd_4069613 := by
    simpa [prefixWord, tailWord_4069613, baseEnd_4069613] using wordTrace_append hprefix tailTrace_4069613
  have hstable : (prefixWord ++ tailWord_4069613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069613).length < 2 ^ (prefixWord ++ tailWord_4069613).sum := by decide
  have hdescent : baseEnd_4069613 < baseStart_4069613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069625 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_4069625 : Nat := 118140960795 + 4069625 * 2 ^ 59
def prefixEnd_4069625 : Nat := 4983230072969 + 3 ^ 40 * 4069625 * 2
def baseEnd_4069625 : Nat := 2089673708553745307171641

theorem tailTrace_4069625 : CollatzResearch.WordTrace tailWord_4069625 prefixEnd_4069625 2089673708553745307171641 := by
  unfold tailWord_4069625
  simp only [CollatzResearch.WordTrace]
  refine ⟨148431417881451136460418329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98954278587634090973612219 148431417881451136460418329)
  ·
    refine ⟨111323563411088352345313747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148431417881451136460418329 111323563411088352345313747)
    ·
      refine ⟨166985345116632528517970621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111323563411088352345313747 166985345116632528517970621)
      ·
        refine ⟨62619504418737198194238983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166985345116632528517970621 62619504418737198194238983)
        ·
          refine ⟨93929256628105797291358475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62619504418737198194238983 93929256628105797291358475)
          ·
            refine ⟨140893884942158695937037713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93929256628105797291358475 140893884942158695937037713)
            ·
              refine ⟨105670413706619021952778285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140893884942158695937037713 105670413706619021952778285)
              ·
                refine ⟨39626405139982133232291857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105670413706619021952778285 39626405139982133232291857)
                ·
                  refine ⟨29719803854986599924218893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39626405139982133232291857 29719803854986599924218893)
                  ·
                    refine ⟨11144926445619974971582085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29719803854986599924218893 11144926445619974971582085)
                    ·
                      refine ⟨2089673708553745307171641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11144926445619974971582085 2089673708553745307171641)
                      ·
                        rfl

theorem cell23_4069625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_4069625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069625 prefixEnd_4069625 := by exact prefixLift 4069625
  have htrace : WordTrace (prefixWord ++ tailWord_4069625) baseStart_4069625 baseEnd_4069625 := by
    simpa [prefixWord, tailWord_4069625, baseEnd_4069625] using wordTrace_append hprefix tailTrace_4069625
  have hstable : (prefixWord ++ tailWord_4069625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069625).length < 2 ^ (prefixWord ++ tailWord_4069625).sum := by decide
  have hdescent : baseEnd_4069625 < baseStart_4069625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069635 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 2, 6]
def baseStart_4069635 : Nat := 118140960795 + 4069635 * 2 ^ 59
def prefixEnd_4069635 : Nat := 4983230072969 + 3 ^ 40 * 4069635 * 2
def baseEnd_4069635 : Nat := 696559614453430089348865

theorem tailTrace_4069635 : CollatzResearch.WordTrace tailWord_4069635 prefixEnd_4069635 696559614453430089348865 := by
  unfold tailWord_4069635
  simp only [CollatzResearch.WordTrace]
  refine ⟨148431782611414908168282359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98954521740943272112188239 148431782611414908168282359)
  ·
    refine ⟨222647673917122362252423539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148431782611414908168282359 222647673917122362252423539)
    ·
      refine ⟨333971510875683543378635309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222647673917122362252423539 333971510875683543378635309)
      ·
        refine ⟨125239316578381328766988241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333971510875683543378635309 125239316578381328766988241)
        ·
          refine ⟨93929487433785996575241181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125239316578381328766988241 93929487433785996575241181)
          ·
            refine ⟨35223557787669748715715443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93929487433785996575241181 35223557787669748715715443)
            ·
              refine ⟨52835336681504623073573165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35223557787669748715715443 52835336681504623073573165)
              ·
                refine ⟨19813251255564233652589937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52835336681504623073573165 19813251255564233652589937)
                ·
                  refine ⟨14859938441673175239442453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19813251255564233652589937 14859938441673175239442453)
                  ·
                    refine ⟨696559614453430089348865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14859938441673175239442453 696559614453430089348865)
                    ·
                      rfl

theorem cell23_4069635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 6].length) (baseStart_4069635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069635 prefixEnd_4069635 := by exact prefixLift 4069635
  have htrace : WordTrace (prefixWord ++ tailWord_4069635) baseStart_4069635 baseEnd_4069635 := by
    simpa [prefixWord, tailWord_4069635, baseEnd_4069635] using wordTrace_append hprefix tailTrace_4069635
  have hstable : (prefixWord ++ tailWord_4069635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069635).length < 2 ^ (prefixWord ++ tailWord_4069635).sum := by decide
  have hdescent : baseEnd_4069635 < baseStart_4069635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069636 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4069636 : Nat := 118140960795 + 4069636 * 2 ^ 59
def prefixEnd_4069636 : Nat := 4983230072969 + 3 ^ 40 * 4069636 * 2
def baseEnd_4069636 : Nat := 2089679356840944764134091

theorem tailTrace_4069636 : CollatzResearch.WordTrace tailWord_4069636 prefixEnd_4069636 2089679356840944764134091 := by
  unfold tailWord_4069636
  simp only [CollatzResearch.WordTrace]
  refine ⟨74215909542205642669534381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98954546056274190226045841 74215909542205642669534381)
  ·
    refine ⟨27830966078327116001075393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74215909542205642669534381 27830966078327116001075393)
    ·
      refine ⟨20873224558745337000806545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27830966078327116001075393 20873224558745337000806545)
      ·
        refine ⟨15654918419059002750604909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20873224558745337000806545 15654918419059002750604909)
        ·
          refine ⟨5870594407147126031476841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15654918419059002750604909 5870594407147126031476841)
          ·
            refine ⟨4402945805360344523607631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5870594407147126031476841 4402945805360344523607631)
            ·
              refine ⟨6604418708040516785411447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402945805360344523607631 6604418708040516785411447)
              ·
                refine ⟨9906628062060775178117171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6604418708040516785411447 9906628062060775178117171)
                ·
                  refine ⟨14859942093091162767175757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9906628062060775178117171 14859942093091162767175757)
                  ·
                    refine ⟨5572478284909186037690909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14859942093091162767175757 5572478284909186037690909)
                    ·
                      refine ⟨2089679356840944764134091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572478284909186037690909 2089679356840944764134091)
                      ·
                        rfl

theorem cell23_4069636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4069636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069636 prefixEnd_4069636 := by exact prefixLift 4069636
  have htrace : WordTrace (prefixWord ++ tailWord_4069636) baseStart_4069636 baseEnd_4069636 := by
    simpa [prefixWord, tailWord_4069636, baseEnd_4069636] using wordTrace_append hprefix tailTrace_4069636
  have hstable : (prefixWord ++ tailWord_4069636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069636).length < 2 ^ (prefixWord ++ tailWord_4069636).sum := by decide
  have hdescent : baseEnd_4069636 < baseStart_4069636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069646 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_4069646 : Nat := 118140960795 + 4069646 * 2 ^ 59
def prefixEnd_4069646 : Nat := 4983230072969 + 3 ^ 40 * 4069646 * 2
def baseEnd_4069646 : Nat := 2089684491647489725009045

theorem tailTrace_4069646 : CollatzResearch.WordTrace tailWord_4069646 prefixEnd_4069646 2089684491647489725009045 := by
  unfold tailWord_4069646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18554022976796882130866599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98954789209583371364621861 18554022976796882130866599)
  ·
    refine ⟨27831034465195323196299899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18554022976796882130866599 27831034465195323196299899)
    ·
      refine ⟨41746551697792984794449849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27831034465195323196299899 41746551697792984794449849)
      ·
        refine ⟨31309913773344738595837387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41746551697792984794449849 31309913773344738595837387)
        ·
          refine ⟨46964870660017107893756081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31309913773344738595837387 46964870660017107893756081)
          ·
            refine ⟨35223652995012830920317061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46964870660017107893756081 35223652995012830920317061)
            ·
              refine ⟨6604434936564905797559449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35223652995012830920317061 6604434936564905797559449)
              ·
                refine ⟨4953326202423679348169587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604434936564905797559449 4953326202423679348169587)
                ·
                  refine ⟨7429989303635519022254381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953326202423679348169587 7429989303635519022254381)
                  ·
                    refine ⟨2786245988863319633345393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7429989303635519022254381 2786245988863319633345393)
                    ·
                      refine ⟨2089684491647489725009045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786245988863319633345393 2089684491647489725009045)
                      ·
                        rfl

theorem cell23_4069646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_4069646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069646 prefixEnd_4069646 := by exact prefixLift 4069646
  have htrace : WordTrace (prefixWord ++ tailWord_4069646) baseStart_4069646 baseEnd_4069646 := by
    simpa [prefixWord, tailWord_4069646, baseEnd_4069646] using wordTrace_append hprefix tailTrace_4069646
  have hstable : (prefixWord ++ tailWord_4069646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069646).length < 2 ^ (prefixWord ++ tailWord_4069646).sum := by decide
  have hdescent : baseEnd_4069646 < baseStart_4069646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069659 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 4, 2, 2]
def baseStart_4069659 : Nat := 118140960795 + 4069659 * 2 ^ 59
def prefixEnd_4069659 : Nat := 4983230072969 + 3 ^ 40 * 4069659 * 2
def baseEnd_4069659 : Nat := 2089691166895998174146485

theorem tailTrace_4069659 : CollatzResearch.WordTrace tailWord_4069659 prefixEnd_4069659 2089691166895998174146485 := by
  unfold tailWord_4069659
  simp only [CollatzResearch.WordTrace]
  refine ⟨148432657963327960267156031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98955105308885306844770687 148432657963327960267156031)
  ·
    refine ⟨222648986944991940400734047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148432657963327960267156031 222648986944991940400734047)
    ·
      refine ⟨333973480417487910601101071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222648986944991940400734047 333973480417487910601101071)
      ·
        refine ⟨500960220626231865901651607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333973480417487910601101071 500960220626231865901651607)
        ·
          refine ⟨751440330939347798852477411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500960220626231865901651607 751440330939347798852477411)
          ·
            refine ⟨1127160496409021698278716117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751440330939347798852477411 1127160496409021698278716117)
            ·
              refine ⟨26417824134586446053407409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1127160496409021698278716117 26417824134586446053407409)
              ·
                refine ⟨19813368100939834540055557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26417824134586446053407409 19813368100939834540055557)
                ·
                  refine ⟨3715006518926218976260417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19813368100939834540055557 3715006518926218976260417)
                  ·
                    refine ⟨2786254889194664232195313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3715006518926218976260417 2786254889194664232195313)
                    ·
                      refine ⟨2089691166895998174146485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786254889194664232195313 2089691166895998174146485)
                      ·
                        rfl

theorem cell23_4069659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 2, 2].length) (baseStart_4069659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069659 prefixEnd_4069659 := by exact prefixLift 4069659
  have htrace : WordTrace (prefixWord ++ tailWord_4069659) baseStart_4069659 baseEnd_4069659 := by
    simpa [prefixWord, tailWord_4069659, baseEnd_4069659] using wordTrace_append hprefix tailTrace_4069659
  have hstable : (prefixWord ++ tailWord_4069659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069659).length < 2 ^ (prefixWord ++ tailWord_4069659).sum := by decide
  have hdescent : baseEnd_4069659 < baseStart_4069659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069665 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 9]
def baseStart_4069665 : Nat := 118140960795 + 4069665 * 2 ^ 59
def prefixEnd_4069665 : Nat := 4983230072969 + 3 ^ 40 * 4069665 * 2
def baseEnd_4069665 : Nat := 232188249753325016741273

theorem tailTrace_4069665 : CollatzResearch.WordTrace tailWord_4069665 prefixEnd_4069665 232188249753325016741273 := by
  unfold tailWord_4069665
  simp only [CollatzResearch.WordTrace]
  refine ⟨148432876801306223291874449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98955251200870815527916299 148432876801306223291874449)
  ·
    refine ⟨111324657600979667468905837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148432876801306223291874449 111324657600979667468905837)
    ·
      refine ⟨41746746600367375300839689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111324657600979667468905837 41746746600367375300839689)
      ·
        refine ⟨31310059950275531475629767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41746746600367375300839689 31310059950275531475629767)
        ·
          refine ⟨46965089925413297213444651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31310059950275531475629767 46965089925413297213444651)
          ·
            refine ⟨70447634888119945820166977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46965089925413297213444651 70447634888119945820166977)
            ·
              refine ⟨52835726166089959365125233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70447634888119945820166977 52835726166089959365125233)
              ·
                refine ⟨39626794624567469523843925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52835726166089959365125233 39626794624567469523843925)
                ·
                  refine ⟨232188249753325016741273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39626794624567469523843925 232188249753325016741273)
                  ·
                    rfl

theorem cell23_4069665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_4069665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069665 prefixEnd_4069665 := by exact prefixLift 4069665
  have htrace : WordTrace (prefixWord ++ tailWord_4069665) baseStart_4069665 baseEnd_4069665 := by
    simpa [prefixWord, tailWord_4069665, baseEnd_4069665] using wordTrace_append hprefix tailTrace_4069665
  have hstable : (prefixWord ++ tailWord_4069665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069665).length < 2 ^ (prefixWord ++ tailWord_4069665).sum := by decide
  have hdescent : baseEnd_4069665 < baseStart_4069665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069692 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_4069692 : Nat := 118140960795 + 4069692 * 2 ^ 59
def prefixEnd_4069692 : Nat := 4983230072969 + 3 ^ 40 * 4069692 * 2
def baseEnd_4069692 : Nat := 2089708111757596545033833

theorem tailTrace_4069692 : CollatzResearch.WordTrace tailWord_4069692 prefixEnd_4069692 2089708111757596545033833 := by
  unfold tailWord_4069692
  simp only [CollatzResearch.WordTrace]
  refine ⟨74216930786104203451553665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98955907714805604602071553 74216930786104203451553665)
  ·
    refine ⟨55662698089578152588665249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74216930786104203451553665 55662698089578152588665249)
    ·
      refine ⟨41747023567183614441498937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55662698089578152588665249 41747023567183614441498937)
      ·
        refine ⟨31310267675387710831124203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41747023567183614441498937 31310267675387710831124203)
        ·
          refine ⟨46965401513081566246686305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31310267675387710831124203 46965401513081566246686305)
          ·
            refine ⟨35224051134811174685014729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46965401513081566246686305 35224051134811174685014729)
            ·
              refine ⟨26418038351108381013761047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35224051134811174685014729 26418038351108381013761047)
              ·
                refine ⟨39627057526662571520641571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26418038351108381013761047 39627057526662571520641571)
                ·
                  refine ⟨59440586289993857280962357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39627057526662571520641571 59440586289993857280962357)
                  ·
                    refine ⟨5572554964686924120090221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59440586289993857280962357 5572554964686924120090221)
                    ·
                      refine ⟨2089708111757596545033833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572554964686924120090221 2089708111757596545033833)
                      ·
                        rfl

theorem cell23_4069692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_4069692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069692 prefixEnd_4069692 := by exact prefixLift 4069692
  have htrace : WordTrace (prefixWord ++ tailWord_4069692) baseStart_4069692 baseEnd_4069692 := by
    simpa [prefixWord, tailWord_4069692, baseEnd_4069692] using wordTrace_append hprefix tailTrace_4069692
  have hstable : (prefixWord ++ tailWord_4069692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069692).length < 2 ^ (prefixWord ++ tailWord_4069692).sum := by decide
  have hdescent : baseEnd_4069692 < baseStart_4069692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069705 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_4069705 : Nat := 118140960795 + 4069705 * 2 ^ 59
def prefixEnd_4069705 : Nat := 4983230072969 + 3 ^ 40 * 4069705 * 2
def baseEnd_4069705 : Nat := 2089714787006104994171273

theorem tailTrace_4069705 : CollatzResearch.WordTrace tailWord_4069705 prefixEnd_4069705 2089714787006104994171273 := by
  unfold tailWord_4069705
  simp only [CollatzResearch.WordTrace]
  refine ⟨148434335721161310123330569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98956223814107540082220379 148434335721161310123330569)
  ·
    refine ⟨111325751790870982592497927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148434335721161310123330569 111325751790870982592497927)
    ·
      refine ⟨166988627686306473888746891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111325751790870982592497927 166988627686306473888746891)
      ·
        refine ⟨250482941529459710833120337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166988627686306473888746891 250482941529459710833120337)
        ·
          refine ⟨187862206147094783124840253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250482941529459710833120337 187862206147094783124840253)
          ·
            refine ⟨70448327305160543671815095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187862206147094783124840253 70448327305160543671815095)
            ·
              refine ⟨105672490957740815507722643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70448327305160543671815095 105672490957740815507722643)
              ·
                refine ⟨158508736436611223261583965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105672490957740815507722643 158508736436611223261583965)
                ·
                  refine ⟨59440776163729208723093987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158508736436611223261583965 59440776163729208723093987)
                  ·
                    refine ⟨89161164245593813084640981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59440776163729208723093987 89161164245593813084640981)
                    ·
                      refine ⟨2089714787006104994171273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89161164245593813084640981 2089714787006104994171273)
                      ·
                        rfl

theorem cell23_4069705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_4069705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069705 prefixEnd_4069705 := by exact prefixLift 4069705
  have htrace : WordTrace (prefixWord ++ tailWord_4069705) baseStart_4069705 baseEnd_4069705 := by
    simpa [prefixWord, tailWord_4069705, baseEnd_4069705] using wordTrace_append hprefix tailTrace_4069705
  have hstable : (prefixWord ++ tailWord_4069705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069705).length < 2 ^ (prefixWord ++ tailWord_4069705).sum := by decide
  have hdescent : baseEnd_4069705 < baseStart_4069705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069712 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_4069712 : Nat := 118140960795 + 4069712 * 2 ^ 59
def prefixEnd_4069712 : Nat := 4983230072969 + 3 ^ 40 * 4069712 * 2
def baseEnd_4069712 : Nat := 696572793790228822261247

theorem tailTrace_4069712 : CollatzResearch.WordTrace tailWord_4069712 prefixEnd_4069712 696572793790228822261247 := by
  unfold tailWord_4069712
  simp only [CollatzResearch.WordTrace]
  refine ⟨74217295516067975159417695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98956394021423966879223593 74217295516067975159417695)
  ·
    refine ⟨111325943274101962739126543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74217295516067975159417695 111325943274101962739126543)
    ·
      refine ⟨166988914911152944108689815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111325943274101962739126543 166988914911152944108689815)
      ·
        refine ⟨250483372366729416163034723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166988914911152944108689815 250483372366729416163034723)
        ·
          refine ⟨375725058550094124244552085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250483372366729416163034723 375725058550094124244552085)
          ·
            refine ⟨17612112119535662073963379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 375725058550094124244552085 17612112119535662073963379)
            ·
              refine ⟨26418168179303493110945069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17612112119535662073963379 26418168179303493110945069)
              ·
                refine ⟨9906813067238809916604401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26418168179303493110945069 9906813067238809916604401)
                ·
                  refine ⟨7430109800429107437453301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9906813067238809916604401 7430109800429107437453301)
                  ·
                    refine ⟨696572793790228822261247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7430109800429107437453301 696572793790228822261247)
                    ·
                      rfl

theorem cell23_4069712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_4069712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069712 prefixEnd_4069712 := by exact prefixLift 4069712
  have htrace : WordTrace (prefixWord ++ tailWord_4069712) baseStart_4069712 baseEnd_4069712 := by
    simpa [prefixWord, tailWord_4069712, baseEnd_4069712] using wordTrace_append hprefix tailTrace_4069712
  have hstable : (prefixWord ++ tailWord_4069712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069712).length < 2 ^ (prefixWord ++ tailWord_4069712).sum := by decide
  have hdescent : baseEnd_4069712 < baseStart_4069712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069769 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_4069769 : Nat := 118140960795 + 4069769 * 2 ^ 59
def prefixEnd_4069769 : Nat := 4983230072969 + 3 ^ 40 * 4069769 * 2
def baseEnd_4069769 : Nat := 2089747649767992743770979

theorem tailTrace_4069769 : CollatzResearch.WordTrace tailWord_4069769 prefixEnd_4069769 2089747649767992743770979 := by
  unfold tailWord_4069769
  simp only [CollatzResearch.WordTrace]
  refine ⟨148436669992929449053660361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98957779995286299369106907 148436669992929449053660361)
  ·
    refine ⟨111327502494697086790245271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148436669992929449053660361 111327502494697086790245271)
    ·
      refine ⟨166991253742045630185367907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111327502494697086790245271 166991253742045630185367907)
      ·
        refine ⟨250486880613068445278051861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166991253742045630185367907 250486880613068445278051861)
        ·
          refine ⟨11741572528737583372408681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250486880613068445278051861 11741572528737583372408681)
          ·
            refine ⟨8806179396553187529306511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11741572528737583372408681 8806179396553187529306511)
            ·
              refine ⟨13209269094829781293959767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806179396553187529306511 13209269094829781293959767)
              ·
                refine ⟨19813903642244671940939651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13209269094829781293959767 19813903642244671940939651)
                ·
                  refine ⟨29720855463367007911409477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19813903642244671940939651 29720855463367007911409477)
                  ·
                    refine ⟨5572660399381313983389277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29720855463367007911409477 5572660399381313983389277)
                    ·
                      refine ⟨2089747649767992743770979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572660399381313983389277 2089747649767992743770979)
                      ·
                        rfl

theorem cell23_4069769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_4069769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069769 prefixEnd_4069769 := by exact prefixLift 4069769
  have htrace : WordTrace (prefixWord ++ tailWord_4069769) baseStart_4069769 baseEnd_4069769 := by
    simpa [prefixWord, tailWord_4069769, baseEnd_4069769] using wordTrace_append hprefix tailTrace_4069769
  have hstable : (prefixWord ++ tailWord_4069769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069769).length < 2 ^ (prefixWord ++ tailWord_4069769).sum := by decide
  have hdescent : baseEnd_4069769 < baseStart_4069769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069789 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 8]
def baseStart_4069789 : Nat := 118140960795 + 4069789 * 2 ^ 59
def prefixEnd_4069789 : Nat := 4983230072969 + 3 ^ 40 * 4069789 * 2
def baseEnd_4069789 : Nat := 232195324375675851724543

theorem tailTrace_4069789 : CollatzResearch.WordTrace tailWord_4069789 prefixEnd_4069789 232195324375675851724543 := by
  unfold tailWord_4069789
  simp only [CollatzResearch.WordTrace]
  refine ⟨148437399452856992469388421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98958266301904661646258947 148437399452856992469388421)
  ·
    refine ⟨27832012397410686088010329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148437399452856992469388421 27832012397410686088010329)
    ·
      refine ⟨20874009298058014566007747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27832012397410686088010329 20874009298058014566007747)
      ·
        refine ⟨31311013947087021849011621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20874009298058014566007747 31311013947087021849011621)
        ·
          refine ⟨5870815115078816596689679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31311013947087021849011621 5870815115078816596689679)
          ·
            refine ⟨8806222672618224895034519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870815115078816596689679 8806222672618224895034519)
            ·
              refine ⟨13209334008927337342551779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806222672618224895034519 13209334008927337342551779)
              ·
                refine ⟨19814001013391006013827669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13209334008927337342551779 19814001013391006013827669)
                ·
                  refine ⟨232195324375675851724543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19814001013391006013827669 232195324375675851724543)
                  ·
                    rfl

theorem cell23_4069789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_4069789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069789 prefixEnd_4069789 := by exact prefixLift 4069789
  have htrace : WordTrace (prefixWord ++ tailWord_4069789) baseStart_4069789 baseEnd_4069789 := by
    simpa [prefixWord, tailWord_4069789, baseEnd_4069789] using wordTrace_append hprefix tailTrace_4069789
  have hstable : (prefixWord ++ tailWord_4069789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069789).length < 2 ^ (prefixWord ++ tailWord_4069789).sum := by decide
  have hdescent : baseEnd_4069789 < baseStart_4069789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069792 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_4069792 : Nat := 118140960795 + 4069792 * 2 ^ 59
def prefixEnd_4069792 : Nat := 4983230072969 + 3 ^ 40 * 4069792 * 2
def baseEnd_4069792 : Nat := 2089759459823046153783373

theorem tailTrace_4069792 : CollatzResearch.WordTrace tailWord_4069792 prefixEnd_4069792 2089759459823046153783373 := by
  unfold tailWord_4069792
  simp only [CollatzResearch.WordTrace]
  refine ⟨74218754435923061990873815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98958339247897415987831753 74218754435923061990873815)
  ·
    refine ⟨111328131653884592986310723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74218754435923061990873815 111328131653884592986310723)
    ·
      refine ⟨166992197480826889479466085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111328131653884592986310723 166992197480826889479466085)
      ·
        refine ⟨31311037027655041777399891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166992197480826889479466085 31311037027655041777399891)
        ·
          refine ⟨46966555541482562666099837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31311037027655041777399891 46966555541482562666099837)
          ·
            refine ⟨17612458328055960999787439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46966555541482562666099837 17612458328055960999787439)
            ·
              refine ⟨26418687492083941499681159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17612458328055960999787439 26418687492083941499681159)
              ·
                refine ⟨39628031238125912249521739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26418687492083941499681159 39628031238125912249521739)
                ·
                  refine ⟨59442046857188868374282609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39628031238125912249521739 59442046857188868374282609)
                  ·
                    refine ⟨44581535142891651280711957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59442046857188868374282609 44581535142891651280711957)
                    ·
                      refine ⟨2089759459823046153783373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44581535142891651280711957 2089759459823046153783373)
                      ·
                        rfl

theorem cell23_4069792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_4069792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069792 prefixEnd_4069792 := by exact prefixLift 4069792
  have htrace : WordTrace (prefixWord ++ tailWord_4069792) baseStart_4069792 baseEnd_4069792 := by
    simpa [prefixWord, tailWord_4069792, baseEnd_4069792] using wordTrace_append hprefix tailTrace_4069792
  have hstable : (prefixWord ++ tailWord_4069792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069792).length < 2 ^ (prefixWord ++ tailWord_4069792).sum := by decide
  have hdescent : baseEnd_4069792 < baseStart_4069792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069793 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 3, 4]
def baseStart_4069793 : Nat := 118140960795 + 4069793 * 2 ^ 59
def prefixEnd_4069793 : Nat := 4983230072969 + 3 ^ 40 * 4069793 * 2
def baseEnd_4069793 : Nat := 696586657767900216623623

theorem tailTrace_4069793 : CollatzResearch.WordTrace tailWord_4069793 prefixEnd_4069793 696586657767900216623623 := by
  unfold tailWord_4069793
  simp only [CollatzResearch.WordTrace]
  refine ⟨148437545344842501152534033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98958363563228334101689355 148437545344842501152534033)
  ·
    refine ⟨111328159008631875864400525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148437545344842501152534033 111328159008631875864400525)
    ·
      refine ⟨41748059628236953449150197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111328159008631875864400525 41748059628236953449150197)
      ·
        refine ⟨3913880590147214385857831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41748059628236953449150197 3913880590147214385857831)
        ·
          refine ⟨5870820885220821578786747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913880590147214385857831 5870820885220821578786747)
          ·
            refine ⟨8806231327831232368180121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870820885220821578786747 8806231327831232368180121)
            ·
              refine ⟨6604673495873424276135091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806231327831232368180121 6604673495873424276135091)
              ·
                refine ⟨9907010243810136414202637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6604673495873424276135091 9907010243810136414202637)
                ·
                  refine ⟨3715128841428801155325989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9907010243810136414202637 3715128841428801155325989)
                  ·
                    refine ⟨696586657767900216623623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3715128841428801155325989 696586657767900216623623)
                    ·
                      rfl

theorem cell23_4069793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_4069793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069793 prefixEnd_4069793 := by exact prefixLift 4069793
  have htrace : WordTrace (prefixWord ++ tailWord_4069793) baseStart_4069793 baseEnd_4069793 := by
    simpa [prefixWord, tailWord_4069793, baseEnd_4069793] using wordTrace_append hprefix tailTrace_4069793
  have hstable : (prefixWord ++ tailWord_4069793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069793).length < 2 ^ (prefixWord ++ tailWord_4069793).sum := by decide
  have hdescent : baseEnd_4069793 < baseStart_4069793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069833 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 1, 1, 3]
def baseStart_4069833 : Nat := 118140960795 + 4069833 * 2 ^ 59
def prefixEnd_4069833 : Nat := 4983230072969 + 3 ^ 40 * 4069833 * 2
def baseEnd_4069833 : Nat := 2089780512529880493370685

theorem tailTrace_4069833 : CollatzResearch.WordTrace tailWord_4069833 prefixEnd_4069833 2089780512529880493370685 := by
  unfold tailWord_4069833
  simp only [CollatzResearch.WordTrace]
  refine ⟨148439004264697587983990153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98959336176465058655993435 148439004264697587983990153)
  ·
    refine ⟨111329253198523190987992615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148439004264697587983990153 111329253198523190987992615)
    ·
      refine ⟨166993879797784786481988923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111329253198523190987992615 166993879797784786481988923)
      ·
        refine ⟨250490819696677179722983385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166993879797784786481988923 250490819696677179722983385)
        ·
          refine ⟨187868114772507884792237539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250490819696677179722983385 187868114772507884792237539)
          ·
            refine ⟨281802172158761827188356309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187868114772507884792237539 281802172158761827188356309)
            ·
              refine ⟨6604738409970980324727101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281802172158761827188356309 6604738409970980324727101)
              ·
                refine ⟨2476776903739117621772663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6604738409970980324727101 2476776903739117621772663)
                ·
                  refine ⟨3715165355608676432658995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476776903739117621772663 3715165355608676432658995)
                  ·
                    refine ⟨5572748033413014648988493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3715165355608676432658995 5572748033413014648988493)
                    ·
                      refine ⟨2089780512529880493370685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572748033413014648988493 2089780512529880493370685)
                      ·
                        rfl

theorem cell23_4069833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 1, 3].length) (baseStart_4069833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069833 prefixEnd_4069833 := by exact prefixLift 4069833
  have htrace : WordTrace (prefixWord ++ tailWord_4069833) baseStart_4069833 baseEnd_4069833 := by
    simpa [prefixWord, tailWord_4069833, baseEnd_4069833] using wordTrace_append hprefix tailTrace_4069833
  have hstable : (prefixWord ++ tailWord_4069833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069833).length < 2 ^ (prefixWord ++ tailWord_4069833).sum := by decide
  have hdescent : baseEnd_4069833 < baseStart_4069833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069849 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 4, 4]
def baseStart_4069849 : Nat := 118140960795 + 4069849 * 2 ^ 59
def prefixEnd_4069849 : Nat := 4983230072969 + 3 ^ 40 * 4069849 * 2
def baseEnd_4069849 : Nat := 696596242740117476923537

theorem tailTrace_4069849 : CollatzResearch.WordTrace tailWord_4069849 prefixEnd_4069849 696596242740117476923537 := by
  unfold tailWord_4069849
  simp only [CollatzResearch.WordTrace]
  refine ⟨148439587832639622716572601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98959725221759748477715067 148439587832639622716572601)
  ·
    refine ⟨111329690874479717037429451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148439587832639622716572601 111329690874479717037429451)
    ·
      refine ⟨166994536311719575556144177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111329690874479717037429451 166994536311719575556144177)
      ·
        refine ⟨125245902233789681667108133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166994536311719575556144177 125245902233789681667108133)
        ·
          refine ⟨23483606668835565312582775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125245902233789681667108133 23483606668835565312582775)
          ·
            refine ⟨35225410003253347968874163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23483606668835565312582775 35225410003253347968874163)
            ·
              refine ⟨52838115004880021953311245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35225410003253347968874163 52838115004880021953311245)
              ·
                refine ⟨19814293126830008232491717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52838115004880021953311245 19814293126830008232491717)
                ·
                  refine ⟨3715179961280626543592197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19814293126830008232491717 3715179961280626543592197)
                  ·
                    refine ⟨696596242740117476923537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3715179961280626543592197 696596242740117476923537)
                    ·
                      rfl

theorem cell23_4069849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_4069849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069849 prefixEnd_4069849 := by exact prefixLift 4069849
  have htrace : WordTrace (prefixWord ++ tailWord_4069849) baseStart_4069849 baseEnd_4069849 := by
    simpa [prefixWord, tailWord_4069849, baseEnd_4069849] using wordTrace_append hprefix tailTrace_4069849
  have hstable : (prefixWord ++ tailWord_4069849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069849).length < 2 ^ (prefixWord ++ tailWord_4069849).sum := by decide
  have hdescent : baseEnd_4069849 < baseStart_4069849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069850 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3]
def baseStart_4069850 : Nat := 118140960795 + 4069850 * 2 ^ 59
def prefixEnd_4069850 : Nat := 4983230072969 + 3 ^ 40 * 4069850 * 2
def baseEnd_4069850 : Nat := 2089789241701006926858107

theorem tailTrace_4069850 : CollatzResearch.WordTrace tailWord_4069850 prefixEnd_4069850 2089789241701006926858107 := by
  unfold tailWord_4069850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37109906076408999971839751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98959749537090666591572669 37109906076408999971839751)
  ·
    refine ⟨55664859114613499957759627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37109906076408999971839751 55664859114613499957759627)
    ·
      refine ⟨83497288671920249936639441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55664859114613499957759627 83497288671920249936639441)
      ·
        refine ⟨62622966503940187452479581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83497288671920249936639441 62622966503940187452479581)
        ·
          refine ⟨23483612438977570294679843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62622966503940187452479581 23483612438977570294679843)
          ·
            refine ⟨35225418658466355442019765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23483612438977570294679843 35225418658466355442019765)
            ·
              refine ⟨3302382999231220822689353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35225418658466355442019765 3302382999231220822689353)
              ·
                refine ⟨2476787249423415617017015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302382999231220822689353 2476787249423415617017015)
                ·
                  refine ⟨3715180874135123425525523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476787249423415617017015 3715180874135123425525523)
                  ·
                    refine ⟨5572771311202685138288285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3715180874135123425525523 5572771311202685138288285)
                    ·
                      refine ⟨2089789241701006926858107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572771311202685138288285 2089789241701006926858107)
                      ·
                        rfl

theorem cell23_4069850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_4069850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069850 prefixEnd_4069850 := by exact prefixLift 4069850
  have htrace : WordTrace (prefixWord ++ tailWord_4069850) baseStart_4069850 baseEnd_4069850 := by
    simpa [prefixWord, tailWord_4069850, baseEnd_4069850] using wordTrace_append hprefix tailTrace_4069850
  have hstable : (prefixWord ++ tailWord_4069850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069850).length < 2 ^ (prefixWord ++ tailWord_4069850).sum := by decide
  have hdescent : baseEnd_4069850 < baseStart_4069850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069901 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4069901 : Nat := 118140960795 + 4069901 * 2 ^ 59
def prefixEnd_4069901 : Nat := 4983230072969 + 3 ^ 40 * 4069901 * 2
def baseEnd_4069901 : Nat := 2089815429214386227320373

theorem tailTrace_4069901 : CollatzResearch.WordTrace tailWord_4069901 prefixEnd_4069901 2089815429214386227320373 := by
  unfold tailWord_4069901
  simp only [CollatzResearch.WordTrace]
  refine ⟨148441484428451235597465557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98960989618967490398310371 148441484428451235597465557)
  ·
    refine ⟨3479097291291825834315599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 148441484428451235597465557 3479097291291825834315599)
    ·
      refine ⟨5218645936937738751473399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479097291291825834315599 5218645936937738751473399)
      ·
        refine ⟨7827968905406608127210099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218645936937738751473399 7827968905406608127210099)
        ·
          refine ⟨11741953358109912190815149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827968905406608127210099 11741953358109912190815149)
          ·
            refine ⟨4403232509291217071555681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11741953358109912190815149 4403232509291217071555681)
            ·
              refine ⟨3302424381968412803666761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403232509291217071555681 3302424381968412803666761)
              ·
                refine ⟨2476818286476309602750071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302424381968412803666761 2476818286476309602750071)
                ·
                  refine ⟨3715227429714464404125107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476818286476309602750071 3715227429714464404125107)
                  ·
                    refine ⟨5572841144571696606187661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3715227429714464404125107 5572841144571696606187661)
                    ·
                      refine ⟨2089815429214386227320373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572841144571696606187661 2089815429214386227320373)
                      ·
                        rfl

theorem cell23_4069901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4069901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069901 prefixEnd_4069901 := by exact prefixLift 4069901
  have htrace : WordTrace (prefixWord ++ tailWord_4069901) baseStart_4069901 baseEnd_4069901 := by
    simpa [prefixWord, tailWord_4069901, baseEnd_4069901] using wordTrace_append hprefix tailTrace_4069901
  have hstable : (prefixWord ++ tailWord_4069901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069901).length < 2 ^ (prefixWord ++ tailWord_4069901).sum := by decide
  have hdescent : baseEnd_4069901 < baseStart_4069901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069923 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 3]
def baseStart_4069923 : Nat := 118140960795 + 4069923 * 2 ^ 59
def prefixEnd_4069923 : Nat := 4983230072969 + 3 ^ 40 * 4069923 * 2
def baseEnd_4069923 : Nat := 2089826725788785141245271

theorem tailTrace_4069923 : CollatzResearch.WordTrace tailWord_4069923 prefixEnd_4069923 2089826725788785141245271 := by
  unfold tailWord_4069923
  simp only [CollatzResearch.WordTrace]
  refine ⟨148442286834371533354766423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98961524556247688903177615 148442286834371533354766423)
  ·
    refine ⟨222663430251557300032149635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148442286834371533354766423 222663430251557300032149635)
    ·
      refine ⟨333995145377335950048224453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222663430251557300032149635 333995145377335950048224453)
      ·
        refine ⟨62624089758250490634042085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333995145377335950048224453 62624089758250490634042085)
        ·
          refine ⟨11742016829671966993882891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62624089758250490634042085 11742016829671966993882891)
          ·
            refine ⟨17613025244507950490824337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742016829671966993882891 17613025244507950490824337)
            ·
              refine ⟨13209768933380962868118253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17613025244507950490824337 13209768933380962868118253)
              ·
                refine ⟨4953663350017861075544345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13209768933380962868118253 4953663350017861075544345)
                ·
                  refine ⟨3715247512513395806658259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953663350017861075544345 3715247512513395806658259)
                  ·
                    refine ⟨5572871268770093709987389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3715247512513395806658259 5572871268770093709987389)
                    ·
                      refine ⟨2089826725788785141245271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5572871268770093709987389 2089826725788785141245271)
                      ·
                        rfl

theorem cell23_4069923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_4069923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069923 prefixEnd_4069923 := by exact prefixLift 4069923
  have htrace : WordTrace (prefixWord ++ tailWord_4069923) baseStart_4069923 baseEnd_4069923 := by
    simpa [prefixWord, tailWord_4069923, baseEnd_4069923] using wordTrace_append hprefix tailTrace_4069923
  have hstable : (prefixWord ++ tailWord_4069923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069923).length < 2 ^ (prefixWord ++ tailWord_4069923).sum := by decide
  have hdescent : baseEnd_4069923 < baseStart_4069923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069969 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 7]
def baseStart_4069969 : Nat := 118140960795 + 4069969 * 2 ^ 59
def prefixEnd_4069969 : Nat := 4983230072969 + 3 ^ 40 * 4069969 * 2
def baseEnd_4069969 : Nat := 232205593988765773474451

theorem tailTrace_4069969 : CollatzResearch.WordTrace tailWord_4069969 prefixEnd_4069969 232205593988765773474451 := by
  unfold tailWord_4069969
  simp only [CollatzResearch.WordTrace]
  refine ⟨148443964592204883210940961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98962643061469922140627307 148443964592204883210940961)
  ·
    refine ⟨111332973444153662408205721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148443964592204883210940961 111332973444153662408205721)
    ·
      refine ⟨83499730083115246806154291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111332973444153662408205721 83499730083115246806154291)
      ·
        refine ⟨125249595124672870209231437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83499730083115246806154291 125249595124672870209231437)
        ·
          refine ⟨46968598171752326328461789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125249595124672870209231437 46968598171752326328461789)
          ·
            refine ⟨17613224314407122373173171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46968598171752326328461789 17613224314407122373173171)
            ·
              refine ⟨26419836471610683559759757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17613224314407122373173171 26419836471610683559759757)
              ·
                refine ⟨9907438676854006334909909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26419836471610683559759757 9907438676854006334909909)
                ·
                  refine ⟨232205593988765773474451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9907438676854006334909909 232205593988765773474451)
                  ·
                    rfl

theorem cell23_4069969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_4069969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069969 prefixEnd_4069969 := by exact prefixLift 4069969
  have htrace : WordTrace (prefixWord ++ tailWord_4069969) baseStart_4069969 baseEnd_4069969 := by
    simpa [prefixWord, tailWord_4069969, baseEnd_4069969] using wordTrace_append hprefix tailTrace_4069969
  have hstable : (prefixWord ++ tailWord_4069969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069969).length < 2 ^ (prefixWord ++ tailWord_4069969).sum := by decide
  have hdescent : baseEnd_4069969 < baseStart_4069969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069999 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 1, 7]
def baseStart_4069999 : Nat := 118140960795 + 4069999 * 2 ^ 59
def prefixEnd_4069999 : Nat := 4983230072969 + 3 ^ 40 * 4069999 * 2
def baseEnd_4069999 : Nat := 696621916772842281298307

theorem tailTrace_4069999 : CollatzResearch.WordTrace tailWord_4069999 prefixEnd_4069999 696621916772842281298307 := by
  unfold tailWord_4069999
  simp only [CollatzResearch.WordTrace]
  refine ⟨148445058782096198334533051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98963372521397465556355367 148445058782096198334533051)
  ·
    refine ⟨222667588173144297501799577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148445058782096198334533051 222667588173144297501799577)
    ·
      refine ⟨167000691129858223126349683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222667588173144297501799577 167000691129858223126349683)
      ·
        refine ⟨250501036694787334689524525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167000691129858223126349683 250501036694787334689524525)
        ·
          refine ⟨93937888760545250508571697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250501036694787334689524525 93937888760545250508571697)
          ·
            refine ⟨70453416570408937881428773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93937888760545250508571697 70453416570408937881428773)
            ·
              refine ⟨13210015606951675852767895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70453416570408937881428773 13210015606951675852767895)
              ·
                refine ⟨19815023410427513779151843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13210015606951675852767895 19815023410427513779151843)
                ·
                  refine ⟨29722535115641270668727765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19815023410427513779151843 29722535115641270668727765)
                  ·
                    refine ⟨696621916772842281298307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29722535115641270668727765 696621916772842281298307)
                    ·
                      rfl

theorem cell23_4069999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_4069999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4069999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4069999 prefixEnd_4069999 := by exact prefixLift 4069999
  have htrace : WordTrace (prefixWord ++ tailWord_4069999) baseStart_4069999 baseEnd_4069999 := by
    simpa [prefixWord, tailWord_4069999, baseEnd_4069999] using wordTrace_append hprefix tailTrace_4069999
  have hstable : (prefixWord ++ tailWord_4069999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069999).length < 2 ^ (prefixWord ++ tailWord_4069999).sum := by decide
  have hdescent : baseEnd_4069999 < baseStart_4069999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070016 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_4070016 : Nat := 118140960795 + 4070016 * 2 ^ 59
def prefixEnd_4070016 : Nat := 4983230072969 + 3 ^ 40 * 4070016 * 2
def baseEnd_4070016 : Nat := 696624826496551092460781

theorem tailTrace_4070016 : CollatzResearch.WordTrace tailWord_4070016 prefixEnd_4070016 696624826496551092460781 := by
  unfold tailWord_4070016
  simp only [CollatzResearch.WordTrace]
  refine ⟨74222839411517305118950951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98963785882023073491934601 74222839411517305118950951)
  ·
    refine ⟨111334259117275957678426427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74222839411517305118950951 111334259117275957678426427)
    ·
      refine ⟨167001388675913936517639641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111334259117275957678426427 167001388675913936517639641)
      ·
        refine ⟨125251041506935452388229731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167001388675913936517639641 125251041506935452388229731)
        ·
          refine ⟨187876562260403178582344597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125251041506935452388229731 187876562260403178582344597)
          ·
            refine ⟨8806713855956398996047403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187876562260403178582344597 8806713855956398996047403)
            ·
              refine ⟨13210070783934598494071105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806713855956398996047403 13210070783934598494071105)
              ·
                refine ⟨9907553087950948870553329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13210070783934598494071105 9907553087950948870553329)
                ·
                  refine ⟨7430664815963211652914997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9907553087950948870553329 7430664815963211652914997)
                  ·
                    refine ⟨696624826496551092460781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7430664815963211652914997 696624826496551092460781)
                    ·
                      rfl

theorem cell23_4070016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_4070016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070016 prefixEnd_4070016 := by exact prefixLift 4070016
  have htrace : WordTrace (prefixWord ++ tailWord_4070016) baseStart_4070016 baseEnd_4070016 := by
    simpa [prefixWord, tailWord_4070016, baseEnd_4070016] using wordTrace_append hprefix tailTrace_4070016
  have hstable : (prefixWord ++ tailWord_4070016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070016).length < 2 ^ (prefixWord ++ tailWord_4070016).sum := by decide
  have hdescent : baseEnd_4070016 < baseStart_4070016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070020 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 5]
def baseStart_4070020 : Nat := 118140960795 + 4070020 * 2 ^ 59
def prefixEnd_4070020 : Nat := 4983230072969 + 3 ^ 40 * 4070020 * 2
def baseEnd_4070020 : Nat := 232208503712474584636925

theorem tailTrace_4070020 : CollatzResearch.WordTrace tailWord_4070020 prefixEnd_4070020 232208503712474584636925 := by
  unfold tailWord_4070020
  simp only [CollatzResearch.WordTrace]
  refine ⟨74222912357510059460523757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98963883143346745947365009 74222912357510059460523757)
  ·
    refine ⟨27833592134066272297696409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74222912357510059460523757 27833592134066272297696409)
    ·
      refine ⟨20875194100549704223272307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27833592134066272297696409 20875194100549704223272307)
      ·
        refine ⟨31312791150824556334908461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20875194100549704223272307 31312791150824556334908461)
        ·
          refine ⟨11742296681559208625590673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31312791150824556334908461 11742296681559208625590673)
          ·
            refine ⟨8806722511169406469193005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11742296681559208625590673 8806722511169406469193005)
            ·
              refine ⟨3302520941688527425947377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8806722511169406469193005 3302520941688527425947377)
              ·
                refine ⟨2476890706266395569460533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302520941688527425947377 2476890706266395569460533)
                ·
                  refine ⟨232208503712474584636925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476890706266395569460533 232208503712474584636925)
                  ·
                    rfl

theorem cell23_4070020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_4070020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070020 prefixEnd_4070020 := by exact prefixLift 4070020
  have htrace : WordTrace (prefixWord ++ tailWord_4070020) baseStart_4070020 baseEnd_4070020 := by
    simpa [prefixWord, tailWord_4070020, baseEnd_4070020] using wordTrace_append hprefix tailTrace_4070020
  have hstable : (prefixWord ++ tailWord_4070020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070020).length < 2 ^ (prefixWord ++ tailWord_4070020).sum := by decide
  have hdescent : baseEnd_4070020 < baseStart_4070020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070080 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 1, 4]
def baseStart_4070080 : Nat := 118140960795 + 4070080 * 2 ^ 59
def prefixEnd_4070080 : Nat := 4983230072969 + 3 ^ 40 * 4070080 * 2
def baseEnd_4070080 : Nat := 696635780750513675660683

theorem tailTrace_4070080 : CollatzResearch.WordTrace tailWord_4070080 prefixEnd_4070080 696635780750513675660683 := by
  unfold tailWord_4070080
  simp only [CollatzResearch.WordTrace]
  refine ⟨74224006547401374584115847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98965342063201832778821129 74224006547401374584115847)
  ·
    refine ⟨111336009821102061876173771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74224006547401374584115847 111336009821102061876173771)
    ·
      refine ⟨167004014731653092814260657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111336009821102061876173771 167004014731653092814260657)
      ·
        refine ⟨125253011048739819610695493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167004014731653092814260657 125253011048739819610695493)
        ·
          refine ⟨23484939571638716177005405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125253011048739819610695493 23484939571638716177005405)
          ·
            refine ⟨8806852339364518566377027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23484939571638716177005405 8806852339364518566377027)
            ·
              refine ⟨13210278509046777849565541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806852339364518566377027 13210278509046777849565541)
              ·
                refine ⟨2476927220446270846793539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13210278509046777849565541 2476927220446270846793539)
                ·
                  refine ⟨3715390830669406270190309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476927220446270846793539 3715390830669406270190309)
                  ·
                    refine ⟨696635780750513675660683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3715390830669406270190309 696635780750513675660683)
                    ·
                      rfl

theorem cell23_4070080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 4].length) (baseStart_4070080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070080 prefixEnd_4070080 := by exact prefixLift 4070080
  have htrace : WordTrace (prefixWord ++ tailWord_4070080) baseStart_4070080 baseEnd_4070080 := by
    simpa [prefixWord, tailWord_4070080, baseEnd_4070080] using wordTrace_append hprefix tailTrace_4070080
  have hstable : (prefixWord ++ tailWord_4070080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070080).length < 2 ^ (prefixWord ++ tailWord_4070080).sum := by decide
  have hdescent : baseEnd_4070080 < baseStart_4070080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070103 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_4070103 : Nat := 118140960795 + 4070103 * 2 ^ 59
def prefixEnd_4070103 : Nat := 4983230072969 + 3 ^ 40 * 4070103 * 2
def baseEnd_4070103 : Nat := 2089919152306594436994443

theorem tailTrace_4070103 : CollatzResearch.WordTrace tailWord_4070103 prefixEnd_4070103 2089919152306594436994443 := by
  unfold tailWord_4070103
  simp only [CollatzResearch.WordTrace]
  refine ⟨148448851973719424096318963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98965901315812949397545975 148448851973719424096318963)
  ·
    refine ⟨222673277960579136144478445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148448851973719424096318963 222673277960579136144478445)
    ·
      refine ⟨83502479235217176054179417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222673277960579136144478445 83502479235217176054179417)
      ·
        refine ⟨62626859426412882040634563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83502479235217176054179417 62626859426412882040634563)
        ·
          refine ⟨93940289139619323060951845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62626859426412882040634563 93940289139619323060951845)
          ·
            refine ⟨17613804213678623073928471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93940289139619323060951845 17613804213678623073928471)
            ·
              refine ⟨26420706320517934610892707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17613804213678623073928471 26420706320517934610892707)
              ·
                refine ⟨39631059480776901916339061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26420706320517934610892707 39631059480776901916339061)
                ·
                  refine ⟨3715411826322834554656787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39631059480776901916339061 3715411826322834554656787)
                  ·
                    refine ⟨5573117739484251831985181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3715411826322834554656787 5573117739484251831985181)
                    ·
                      refine ⟨2089919152306594436994443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5573117739484251831985181 2089919152306594436994443)
                      ·
                        rfl

theorem cell23_4070103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_4070103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070103 prefixEnd_4070103 := by exact prefixLift 4070103
  have htrace : WordTrace (prefixWord ++ tailWord_4070103) baseStart_4070103 baseEnd_4070103 := by
    simpa [prefixWord, tailWord_4070103, baseEnd_4070103] using wordTrace_append hprefix tailTrace_4070103
  have hstable : (prefixWord ++ tailWord_4070103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070103).length < 2 ^ (prefixWord ++ tailWord_4070103).sum := by decide
  have hdescent : baseEnd_4070103 < baseStart_4070103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070106 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_4070106 : Nat := 118140960795 + 4070106 * 2 ^ 59
def prefixEnd_4070106 : Nat := 4983230072969 + 3 ^ 40 * 4070106 * 2
def baseEnd_4070106 : Nat := 696640230916185975085643

theorem tailTrace_4070106 : CollatzResearch.WordTrace tailWord_4070106 prefixEnd_4070106 696640230916185975085643 := by
  unfold tailWord_4070106
  simp only [CollatzResearch.WordTrace]
  refine ⟨37112240348177138902169543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98965974261805703739118781 37112240348177138902169543)
  ·
    refine ⟨55668360522265708353254315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37112240348177138902169543 55668360522265708353254315)
    ·
      refine ⟨83502540783398562529881473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55668360522265708353254315 83502540783398562529881473)
      ·
        refine ⟨62626905587548921897411105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83502540783398562529881473 62626905587548921897411105)
        ·
          refine ⟨46970179190661691423058329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62626905587548921897411105 46970179190661691423058329)
          ·
            refine ⟨35227634392996268567293747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46970179190661691423058329 35227634392996268567293747)
            ·
              refine ⟨52841451589494402850940621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35227634392996268567293747 52841451589494402850940621)
              ·
                refine ⟨19815544346060401069102733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52841451589494402850940621 19815544346060401069102733)
                ·
                  refine ⟨7430829129772650400913525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19815544346060401069102733 7430829129772650400913525)
                  ·
                    refine ⟨696640230916185975085643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7430829129772650400913525 696640230916185975085643)
                    ·
                      rfl

theorem cell23_4070106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_4070106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070106 prefixEnd_4070106 := by exact prefixLift 4070106
  have htrace : WordTrace (prefixWord ++ tailWord_4070106) baseStart_4070106 baseEnd_4070106 := by
    simpa [prefixWord, tailWord_4070106, baseEnd_4070106] using wordTrace_append hprefix tailTrace_4070106
  have hstable : (prefixWord ++ tailWord_4070106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070106).length < 2 ^ (prefixWord ++ tailWord_4070106).sum := by decide
  have hdescent : baseEnd_4070106 < baseStart_4070106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070153 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 2, 4]
def baseStart_4070153 : Nat := 118140960795 + 4070153 * 2 ^ 59
def prefixEnd_4070153 : Nat := 4983230072969 + 3 ^ 40 * 4070153 * 2
def baseEnd_4070153 : Nat := 696648275446439747123071

theorem tailTrace_4070153 : CollatzResearch.WordTrace tailWord_4070153 prefixEnd_4070153 696648275446439747123071 := by
  unfold tailWord_4070153
  simp only [CollatzResearch.WordTrace]
  refine ⟨148450675623538282635639113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98967117082358855090426075 148450675623538282635639113)
  ·
    refine ⟨111338006717653711976729335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148450675623538282635639113 111338006717653711976729335)
    ·
      refine ⟨167007010076480567965094003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111338006717653711976729335 167007010076480567965094003)
      ·
        refine ⟨250510515114720851947641005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167007010076480567965094003 250510515114720851947641005)
        ·
          refine ⟨93941443168020319480365377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250510515114720851947641005 93941443168020319480365377)
          ·
            refine ⟨70456082376015239610274033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93941443168020319480365377 70456082376015239610274033)
            ·
              refine ⟨52842061782011429707705525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70456082376015239610274033 52842061782011429707705525)
              ·
                refine ⟨4953943292063571535097393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52842061782011429707705525 4953943292063571535097393)
                ·
                  refine ⟨3715457469047678651323045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953943292063571535097393 3715457469047678651323045)
                  ·
                    refine ⟨696648275446439747123071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3715457469047678651323045 696648275446439747123071)
                    ·
                      rfl

theorem cell23_4070153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_4070153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070153 prefixEnd_4070153 := by exact prefixLift 4070153
  have htrace : WordTrace (prefixWord ++ tailWord_4070153) baseStart_4070153 baseEnd_4070153 := by
    simpa [prefixWord, tailWord_4070153, baseEnd_4070153] using wordTrace_append hprefix tailTrace_4070153
  have hstable : (prefixWord ++ tailWord_4070153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070153).length < 2 ^ (prefixWord ++ tailWord_4070153).sum := by decide
  have hdescent : baseEnd_4070153 < baseStart_4070153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070180 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_4070180 : Nat := 118140960795 + 4070180 * 2 ^ 59
def prefixEnd_4070180 : Nat := 4983230072969 + 3 ^ 40 * 4070180 * 2
def baseEnd_4070180 : Nat := 2089958690316990635731589

theorem tailTrace_4070180 : CollatzResearch.WordTrace tailWord_4070180 prefixEnd_4070180 2089958690316990635731589 := by
  unfold tailWord_4070180
  simp only [CollatzResearch.WordTrace]
  refine ⟨74225830197220233123435997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98967773596293644164581329 74225830197220233123435997)
  ·
    refine ⟨27834686323957587421288499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74225830197220233123435997 27834686323957587421288499)
    ·
      refine ⟨41752029485936381131932749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27834686323957587421288499 41752029485936381131932749)
      ·
        refine ⟨15657011057226142924474781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41752029485936381131932749 15657011057226142924474781)
        ·
          refine ⟨5871379146459803596678043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15657011057226142924474781 5871379146459803596678043)
          ·
            refine ⟨8807068719689705395017065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871379146459803596678043 8807068719689705395017065)
            ·
              refine ⟨6605301539767279046262799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807068719689705395017065 6605301539767279046262799)
              ·
                refine ⟨9907952309650918569394199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605301539767279046262799 9907952309650918569394199)
                ·
                  refine ⟨14861928464476377854091299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9907952309650918569394199 14861928464476377854091299)
                  ·
                    refine ⟨22292892696714566781136949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14861928464476377854091299 22292892696714566781136949)
                    ·
                      refine ⟨2089958690316990635731589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22292892696714566781136949 2089958690316990635731589)
                      ·
                        rfl

theorem cell23_4070180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_4070180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070180 prefixEnd_4070180 := by exact prefixLift 4070180
  have htrace : WordTrace (prefixWord ++ tailWord_4070180) baseStart_4070180 baseEnd_4070180 := by
    simpa [prefixWord, tailWord_4070180, baseEnd_4070180] using wordTrace_append hprefix tailTrace_4070180
  have hstable : (prefixWord ++ tailWord_4070180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070180).length < 2 ^ (prefixWord ++ tailWord_4070180).sum := by decide
  have hdescent : baseEnd_4070180 < baseStart_4070180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070214 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4070214 : Nat := 118140960795 + 4070214 * 2 ^ 59
def prefixEnd_4070214 : Nat := 4983230072969 + 3 ^ 40 * 4070214 * 2
def baseEnd_4070214 : Nat := 2089976148659243502706433

theorem tailTrace_4070214 : CollatzResearch.WordTrace tailWord_4070214 prefixEnd_4070214 2089976148659243502706433 := by
  unfold tailWord_4070214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639153139884915314175303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98968600317544860035739797 4639153139884915314175303)
  ·
    refine ⟨6958729709827372971262955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4639153139884915314175303 6958729709827372971262955)
    ·
      refine ⟨10438094564741059456894433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6958729709827372971262955 10438094564741059456894433)
      ·
        refine ⟨7828570923555794592670825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10438094564741059456894433 7828570923555794592670825)
        ·
          refine ⟨5871428192666845944503119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7828570923555794592670825 5871428192666845944503119)
          ·
            refine ⟨8807142289000268916754679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871428192666845944503119 8807142289000268916754679)
            ·
              refine ⟨13210713433500403375132019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807142289000268916754679 13210713433500403375132019)
              ·
                refine ⟨19816070150250605062698029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13210713433500403375132019 19816070150250605062698029)
                ·
                  refine ⟨7431026306343976898511761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19816070150250605062698029 7431026306343976898511761)
                  ·
                    refine ⟨5573269729757982673883821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7431026306343976898511761 5573269729757982673883821)
                    ·
                      refine ⟨2089976148659243502706433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5573269729757982673883821 2089976148659243502706433)
                      ·
                        rfl

theorem cell23_4070214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4070214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070214 prefixEnd_4070214 := by exact prefixLift 4070214
  have htrace : WordTrace (prefixWord ++ tailWord_4070214) baseStart_4070214 baseEnd_4070214 := by
    simpa [prefixWord, tailWord_4070214, baseEnd_4070214] using wordTrace_append hprefix tailTrace_4070214
  have hstable : (prefixWord ++ tailWord_4070214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070214).length < 2 ^ (prefixWord ++ tailWord_4070214).sum := by decide
  have hdescent : baseEnd_4070214 < baseStart_4070214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070267 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 2, 2, 2]
def baseStart_4070267 : Nat := 118140960795 + 4070267 * 2 ^ 59
def prefixEnd_4070267 : Nat := 4983230072969 + 3 ^ 40 * 4070267 * 2
def baseEnd_4070267 : Nat := 2090003363133931795343689

theorem tailTrace_4070267 : CollatzResearch.WordTrace tailWord_4070267 prefixEnd_4070267 2090003363133931795343689 := by
  unfold tailWord_4070267
  simp only [CollatzResearch.WordTrace]
  refine ⟨148454833545125280105289055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98969889030083520070192703 148454833545125280105289055)
  ·
    refine ⟨222682250317687920157933583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148454833545125280105289055 222682250317687920157933583)
    ·
      refine ⟨334023375476531880236900375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222682250317687920157933583 334023375476531880236900375)
      ·
        refine ⟨501035063214797820355350563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334023375476531880236900375 501035063214797820355350563)
        ·
          refine ⟨751552594822196730533025845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501035063214797820355350563 751552594822196730533025845)
          ·
            refine ⟨70458055764580943487471173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 751552594822196730533025845 70458055764580943487471173)
            ·
              refine ⟨13210885455858926903900845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70458055764580943487471173 13210885455858926903900845)
              ·
                refine ⟨4954082045947097588962817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13210885455858926903900845 4954082045947097588962817)
                ·
                  refine ⟨3715561534460323191722113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4954082045947097588962817 3715561534460323191722113)
                  ·
                    refine ⟨2786671150845242393791585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3715561534460323191722113 2786671150845242393791585)
                    ·
                      refine ⟨2090003363133931795343689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786671150845242393791585 2090003363133931795343689)
                      ·
                        rfl

theorem cell23_4070267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 2, 2].length) (baseStart_4070267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070267 prefixEnd_4070267 := by exact prefixLift 4070267
  have htrace : WordTrace (prefixWord ++ tailWord_4070267) baseStart_4070267 baseEnd_4070267 := by
    simpa [prefixWord, tailWord_4070267, baseEnd_4070267] using wordTrace_append hprefix tailTrace_4070267
  have hstable : (prefixWord ++ tailWord_4070267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070267).length < 2 ^ (prefixWord ++ tailWord_4070267).sum := by decide
  have hdescent : baseEnd_4070267 < baseStart_4070267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070323 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 4]
def baseStart_4070323 : Nat := 118140960795 + 4070323 * 2 ^ 59
def prefixEnd_4070323 : Nat := 4983230072969 + 3 ^ 40 * 4070323 * 2
def baseEnd_4070323 : Nat := 2090032118050583576243431

theorem tailTrace_4070323 : CollatzResearch.WordTrace tailWord_4070323 prefixEnd_4070323 2090032118050583576243431 := by
  unfold tailWord_4070323
  simp only [CollatzResearch.WordTrace]
  refine ⟨148456876032922401669327623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98971250688614934446218415 148456876032922401669327623)
  ·
    refine ⟨222685314049383602503991435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148456876032922401669327623 222685314049383602503991435)
    ·
      refine ⟨334027971074075403755987153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222685314049383602503991435 334027971074075403755987153)
      ·
        refine ⟨250520978305556552816990365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334027971074075403755987153 250520978305556552816990365)
        ·
          refine ⟨93945366864583707306371387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250520978305556552816990365 93945366864583707306371387)
          ·
            refine ⟨140918050296875560959557081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93945366864583707306371387 140918050296875560959557081)
            ·
              refine ⟨105688537722656670719667811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140918050296875560959557081 105688537722656670719667811)
              ·
                refine ⟨158532806583985006079501717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105688537722656670719667811 158532806583985006079501717)
                ·
                  refine ⟨7431225308624297159976643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158532806583985006079501717 7431225308624297159976643)
                  ·
                    refine ⟨11146837962936445739964965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431225308624297159976643 11146837962936445739964965)
                    ·
                      refine ⟨2090032118050583576243431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11146837962936445739964965 2090032118050583576243431)
                      ·
                        rfl

theorem cell23_4070323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_4070323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070323 prefixEnd_4070323 := by exact prefixLift 4070323
  have htrace : WordTrace (prefixWord ++ tailWord_4070323) baseStart_4070323 baseEnd_4070323 := by
    simpa [prefixWord, tailWord_4070323, baseEnd_4070323] using wordTrace_append hprefix tailTrace_4070323
  have hstable : (prefixWord ++ tailWord_4070323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070323).length < 2 ^ (prefixWord ++ tailWord_4070323).sum := by decide
  have hdescent : baseEnd_4070323 < baseStart_4070323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070357 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4070357 : Nat := 118140960795 + 4070357 * 2 ^ 59
def prefixEnd_4070357 : Nat := 4983230072969 + 3 ^ 40 * 4070357 * 2
def baseEnd_4070357 : Nat := 2090049576392836443218275

theorem tailTrace_4070357 : CollatzResearch.WordTrace tailWord_4070357 prefixEnd_4070357 2090049576392836443218275 := by
  unfold tailWord_4070357
  simp only [CollatzResearch.WordTrace]
  refine ⟨148458116114799225476065325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98972077409866150317376883 148458116114799225476065325)
  ·
    refine ⟨55671793543049709553524497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148458116114799225476065325 55671793543049709553524497)
    ·
      refine ⟨41753845157287282165143373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55671793543049709553524497 41753845157287282165143373)
      ·
        refine ⟨15657691933982730811928765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41753845157287282165143373 15657691933982730811928765)
        ·
          refine ⟨5871634475243524054473287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15657691933982730811928765 5871634475243524054473287)
          ·
            refine ⟨8807451712865286081709931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871634475243524054473287 8807451712865286081709931)
            ·
              refine ⟨13211177569297929122564897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807451712865286081709931 13211177569297929122564897)
              ·
                refine ⟨9908383176973446841923673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13211177569297929122564897 9908383176973446841923673)
                ·
                  refine ⟨7431287382730085131442755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9908383176973446841923673 7431287382730085131442755)
                  ·
                    refine ⟨11146931074095127697164133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431287382730085131442755 11146931074095127697164133)
                    ·
                      refine ⟨2090049576392836443218275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11146931074095127697164133 2090049576392836443218275)
                      ·
                        rfl

theorem cell23_4070357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4070357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070357 prefixEnd_4070357 := by exact prefixLift 4070357
  have htrace : WordTrace (prefixWord ++ tailWord_4070357) baseStart_4070357 baseEnd_4070357 := by
    simpa [prefixWord, tailWord_4070357, baseEnd_4070357] using wordTrace_append hprefix tailTrace_4070357
  have hstable : (prefixWord ++ tailWord_4070357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070357).length < 2 ^ (prefixWord ++ tailWord_4070357).sum := by decide
  have hdescent : baseEnd_4070357 < baseStart_4070357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070360 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_4070360 : Nat := 118140960795 + 4070360 * 2 ^ 59
def prefixEnd_4070360 : Nat := 4983230072969 + 3 ^ 40 * 4070360 * 2
def baseEnd_4070360 : Nat := 2090051116834799931480761

theorem tailTrace_4070360 : CollatzResearch.WordTrace tailWord_4070360 prefixEnd_4070360 2090051116834799931480761 := by
  unfold tailWord_4070360
  simp only [CollatzResearch.WordTrace]
  refine ⟨74229112766894178494212267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98972150355858904658949689 74229112766894178494212267)
  ·
    refine ⟨111343669150341267741318401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74229112766894178494212267 111343669150341267741318401)
    ·
      refine ⟨83507751862755950805988801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111343669150341267741318401 83507751862755950805988801)
      ·
        refine ⟨62630813897066963104491601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83507751862755950805988801 62630813897066963104491601)
        ·
          refine ⟨46973110422800222328368701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62630813897066963104491601 46973110422800222328368701)
          ·
            refine ⟨17614916408550083373138263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46973110422800222328368701 17614916408550083373138263)
            ·
              refine ⟨26422374612825125059707395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17614916408550083373138263 26422374612825125059707395)
              ·
                refine ⟨39633561919237687589561093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26422374612825125059707395 39633561919237687589561093)
                ·
                  refine ⟨7431292859857066423042705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39633561919237687589561093 7431292859857066423042705)
                  ·
                    refine ⟨5573469644892799817282029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7431292859857066423042705 5573469644892799817282029)
                    ·
                      refine ⟨2090051116834799931480761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5573469644892799817282029 2090051116834799931480761)
                      ·
                        rfl

theorem cell23_4070360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_4070360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070360 prefixEnd_4070360 := by exact prefixLift 4070360
  have htrace : WordTrace (prefixWord ++ tailWord_4070360) baseStart_4070360 baseEnd_4070360 := by
    simpa [prefixWord, tailWord_4070360, baseEnd_4070360] using wordTrace_append hprefix tailTrace_4070360
  have hstable : (prefixWord ++ tailWord_4070360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070360).length < 2 ^ (prefixWord ++ tailWord_4070360).sum := by decide
  have hdescent : baseEnd_4070360 < baseStart_4070360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070388 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4070388 : Nat := 118140960795 + 4070388 * 2 ^ 59
def prefixEnd_4070388 : Nat := 4983230072969 + 3 ^ 40 * 4070388 * 2
def baseEnd_4070388 : Nat := 696688498097708607310211

theorem tailTrace_4070388 : CollatzResearch.WordTrace tailWord_4070388 prefixEnd_4070388 696688498097708607310211 := by
  unfold tailWord_4070388
  simp only [CollatzResearch.WordTrace]
  refine ⟨74229623388843458885221909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98972831185124611846962545 74229623388843458885221909)
  ·
    refine ⟨3479513596352037135244777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74229623388843458885221909 3479513596352037135244777)
    ·
      refine ⟨2609635197264027851433583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479513596352037135244777 2609635197264027851433583)
      ·
        refine ⟨3914452795896041777150375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609635197264027851433583 3914452795896041777150375)
        ·
          refine ⟨5871679193844062665725563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914452795896041777150375 5871679193844062665725563)
          ·
            refine ⟨8807518790766093998588345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871679193844062665725563 8807518790766093998588345)
            ·
              refine ⟨6605639093074570498941259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807518790766093998588345 6605639093074570498941259)
              ·
                refine ⟨9908458639611855748411889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605639093074570498941259 9908458639611855748411889)
                ·
                  refine ⟨7431343979708891811308917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9908458639611855748411889 7431343979708891811308917)
                  ·
                    refine ⟨696688498097708607310211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7431343979708891811308917 696688498097708607310211)
                    ·
                      rfl

theorem cell23_4070388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4070388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070388 prefixEnd_4070388 := by exact prefixLift 4070388
  have htrace : WordTrace (prefixWord ++ tailWord_4070388) baseStart_4070388 baseEnd_4070388 := by
    simpa [prefixWord, tailWord_4070388, baseEnd_4070388] using wordTrace_append hprefix tailTrace_4070388
  have hstable : (prefixWord ++ tailWord_4070388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070388).length < 2 ^ (prefixWord ++ tailWord_4070388).sum := by decide
  have hdescent : baseEnd_4070388 < baseStart_4070388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070400 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 5, 5, 2]
def baseStart_4070400 : Nat := 118140960795 + 4070400 * 2 ^ 59
def prefixEnd_4070400 : Nat := 4983230072969 + 3 ^ 40 * 4070400 * 2
def baseEnd_4070400 : Nat := 2090071656060979774980577

theorem tailTrace_4070400 : CollatzResearch.WordTrace tailWord_4070400 prefixEnd_4070400 2090071656060979774980577 := by
  unfold tailWord_4070400
  simp only [CollatzResearch.WordTrace]
  refine ⟨74229842226821721909940327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98973122969095629213253769 74229842226821721909940327)
  ·
    refine ⟨111344763340232582864910491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74229842226821721909940327 111344763340232582864910491)
    ·
      refine ⟨167017145010348874297365737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111344763340232582864910491 167017145010348874297365737)
      ·
        refine ⟨125262858757761655723024303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167017145010348874297365737 125262858757761655723024303)
        ·
          refine ⟨187894288136642483584536455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125262858757761655723024303 187894288136642483584536455)
          ·
            refine ⟨281841432204963725376804683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187894288136642483584536455 281841432204963725376804683)
            ·
              refine ⟨422762148307445588065207025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281841432204963725376804683 422762148307445588065207025)
              ·
                refine ⟨317071611230584191048905269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422762148307445588065207025 317071611230584191048905269)
                ·
                  refine ⟨29725463552867267910834869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317071611230584191048905269 29725463552867267910834869)
                  ·
                    refine ⟨2786762208081306366640769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29725463552867267910834869 2786762208081306366640769)
                    ·
                      refine ⟨2090071656060979774980577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786762208081306366640769 2090071656060979774980577)
                      ·
                        rfl

theorem cell23_4070400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_4070400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070400 prefixEnd_4070400 := by exact prefixLift 4070400
  have htrace : WordTrace (prefixWord ++ tailWord_4070400) baseStart_4070400 baseEnd_4070400 := by
    simpa [prefixWord, tailWord_4070400, baseEnd_4070400] using wordTrace_append hprefix tailTrace_4070400
  have hstable : (prefixWord ++ tailWord_4070400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070400).length < 2 ^ (prefixWord ++ tailWord_4070400).sum := by decide
  have hdescent : baseEnd_4070400 < baseStart_4070400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070467 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 3]
def baseStart_4070467 : Nat := 118140960795 + 4070467 * 2 ^ 59
def prefixEnd_4070467 : Nat := 4983230072969 + 3 ^ 40 * 4070467 * 2
def baseEnd_4070467 : Nat := 2090106059264831012842769

theorem tailTrace_4070467 : CollatzResearch.WordTrace tailWord_4070467 prefixEnd_4070467 2090106059264831012842769 := by
  unfold tailWord_4070467
  simp only [CollatzResearch.WordTrace]
  refine ⟨148462128144400714262569655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98974752096267142841713103 148462128144400714262569655)
  ·
    refine ⟨222693192216601071393854483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148462128144400714262569655 222693192216601071393854483)
    ·
      refine ⟨334039788324901607090781725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222693192216601071393854483 334039788324901607090781725)
      ·
        refine ⟨125264920621838102659043147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334039788324901607090781725 125264920621838102659043147)
        ·
          refine ⟨187897380932757153988564721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125264920621838102659043147 187897380932757153988564721)
          ·
            refine ⟨140923035699567865491423541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187897380932757153988564721 140923035699567865491423541)
            ·
              refine ⟨13211534596834487389820957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140923035699567865491423541 13211534596834487389820957)
              ·
                refine ⟨4954325473812932771182859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13211534596834487389820957 4954325473812932771182859)
                ·
                  refine ⟨7431488210719399156774289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954325473812932771182859 7431488210719399156774289)
                  ·
                    refine ⟨5573616158039549367580717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7431488210719399156774289 5573616158039549367580717)
                    ·
                      refine ⟨2090106059264831012842769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5573616158039549367580717 2090106059264831012842769)
                      ·
                        rfl

theorem cell23_4070467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_4070467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070467 prefixEnd_4070467 := by exact prefixLift 4070467
  have htrace : WordTrace (prefixWord ++ tailWord_4070467) baseStart_4070467 baseEnd_4070467 := by
    simpa [prefixWord, tailWord_4070467, baseEnd_4070467] using wordTrace_append hprefix tailTrace_4070467
  have hstable : (prefixWord ++ tailWord_4070467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070467).length < 2 ^ (prefixWord ++ tailWord_4070467).sum := by decide
  have hdescent : baseEnd_4070467 < baseStart_4070467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070480 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_4070480 : Nat := 118140960795 + 4070480 * 2 ^ 59
def prefixEnd_4070480 : Nat := 4983230072969 + 3 ^ 40 * 4070480 * 2
def baseEnd_4070480 : Nat := 2090112734513339461980209

theorem tailTrace_4070480 : CollatzResearch.WordTrace tailWord_4070480 prefixEnd_4070480 2090112734513339461980209 := by
  unfold tailWord_4070480
  simp only [CollatzResearch.WordTrace]
  refine ⟨74231301146676808741396447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98975068195569078321861929 74231301146676808741396447)
  ·
    refine ⟨111346951720015213112094671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74231301146676808741396447 111346951720015213112094671)
    ·
      refine ⟨167020427580022819668142007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111346951720015213112094671 167020427580022819668142007)
      ·
        refine ⟨250530641370034229502213011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167020427580022819668142007 250530641370034229502213011)
        ·
          refine ⟨375795962055051344253319517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250530641370034229502213011 375795962055051344253319517)
          ·
            refine ⟨140923485770644254094994819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375795962055051344253319517 140923485770644254094994819)
            ·
              refine ⟨211385228655966381142492229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140923485770644254094994819 211385228655966381142492229)
              ·
                refine ⟨39634730372993696464217293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211385228655966381142492229 39634730372993696464217293)
                ·
                  refine ⟨14863023889872636174081485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39634730372993696464217293 14863023889872636174081485)
                  ·
                    refine ⟨5573633958702238565280557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14863023889872636174081485 5573633958702238565280557)
                    ·
                      refine ⟨2090112734513339461980209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5573633958702238565280557 2090112734513339461980209)
                      ·
                        rfl

theorem cell23_4070480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_4070480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070480 prefixEnd_4070480 := by exact prefixLift 4070480
  have htrace : WordTrace (prefixWord ++ tailWord_4070480) baseStart_4070480 baseEnd_4070480 := by
    simpa [prefixWord, tailWord_4070480, baseEnd_4070480] using wordTrace_append hprefix tailTrace_4070480
  have hstable : (prefixWord ++ tailWord_4070480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070480).length < 2 ^ (prefixWord ++ tailWord_4070480).sum := by decide
  have hdescent : baseEnd_4070480 < baseStart_4070480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070481 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 1, 2, 2]
def baseStart_4070481 : Nat := 118140960795 + 4070481 * 2 ^ 59
def prefixEnd_4070481 : Nat := 4983230072969 + 3 ^ 40 * 4070481 * 2
def baseEnd_4070481 : Nat := 2090113247993993958067705

theorem tailTrace_4070481 : CollatzResearch.WordTrace tailWord_4070481 prefixEnd_4070481 2090113247993993958067705 := by
  unfold tailWord_4070481
  simp only [CollatzResearch.WordTrace]
  refine ⟨148462638766349994653579297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98975092510899996435719531 148462638766349994653579297)
  ·
    refine ⟨111346979074762495990184473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148462638766349994653579297 111346979074762495990184473)
    ·
      refine ⟨83510234306071871992638355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111346979074762495990184473 83510234306071871992638355)
      ·
        refine ⟨125265351459107807988957533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83510234306071871992638355 125265351459107807988957533)
        ·
          refine ⟨46974506797165427995859075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125265351459107807988957533 46974506797165427995859075)
          ·
            refine ⟨70461760195748141993788613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46974506797165427995859075 70461760195748141993788613)
            ·
              refine ⟨13211580036702776623835365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70461760195748141993788613 13211580036702776623835365)
              ·
                refine ⟨2477171256881770616969131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13211580036702776623835365 2477171256881770616969131)
                ·
                  refine ⟨3715756885322655925453697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477171256881770616969131 3715756885322655925453697)
                  ·
                    refine ⟨2786817663991991944090273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3715756885322655925453697 2786817663991991944090273)
                    ·
                      refine ⟨2090113247993993958067705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786817663991991944090273 2090113247993993958067705)
                      ·
                        rfl

theorem cell23_4070481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_4070481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070481 prefixEnd_4070481 := by exact prefixLift 4070481
  have htrace : WordTrace (prefixWord ++ tailWord_4070481) baseStart_4070481 baseEnd_4070481 := by
    simpa [prefixWord, tailWord_4070481, baseEnd_4070481] using wordTrace_append hprefix tailTrace_4070481
  have hstable : (prefixWord ++ tailWord_4070481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070481).length < 2 ^ (prefixWord ++ tailWord_4070481).sum := by decide
  have hdescent : baseEnd_4070481 < baseStart_4070481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070497 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_4070497 : Nat := 118140960795 + 4070497 * 2 ^ 59
def prefixEnd_4070497 : Nat := 4983230072969 + 3 ^ 40 * 4070497 * 2
def baseEnd_4070497 : Nat := 2090121463684465895467631

theorem tailTrace_4070497 : CollatzResearch.WordTrace tailWord_4070497 prefixEnd_4070497 2090121463684465895467631 := by
  unfold tailWord_4070497
  simp only [CollatzResearch.WordTrace]
  refine ⟨148463222334292029386161745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98975481556194686257441163 148463222334292029386161745)
  ·
    refine ⟨111347416750719022039621309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148463222334292029386161745 111347416750719022039621309)
    ·
      refine ⟨41755281281519633264857991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111347416750719022039621309 41755281281519633264857991)
      ·
        refine ⟨62632921922279449897286987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41755281281519633264857991 62632921922279449897286987)
        ·
          refine ⟨93949382883419174845930481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62632921922279449897286987 93949382883419174845930481)
          ·
            refine ⟨70462037162564381134447861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93949382883419174845930481 70462037162564381134447861)
            ·
              refine ⟨6605815983990410731354487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70462037162564381134447861 6605815983990410731354487)
              ·
                refine ⟨9908723975985616097031731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605815983990410731354487 9908723975985616097031731)
                ·
                  refine ⟨14863085963978424145547597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908723975985616097031731 14863085963978424145547597)
                  ·
                    refine ⟨5573657236491909054580349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14863085963978424145547597 5573657236491909054580349)
                    ·
                      refine ⟨2090121463684465895467631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5573657236491909054580349 2090121463684465895467631)
                      ·
                        rfl

theorem cell23_4070497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_4070497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070497 prefixEnd_4070497 := by exact prefixLift 4070497
  have htrace : WordTrace (prefixWord ++ tailWord_4070497) baseStart_4070497 baseEnd_4070497 := by
    simpa [prefixWord, tailWord_4070497, baseEnd_4070497] using wordTrace_append hprefix tailTrace_4070497
  have hstable : (prefixWord ++ tailWord_4070497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070497).length < 2 ^ (prefixWord ++ tailWord_4070497).sum := by decide
  have hdescent : baseEnd_4070497 < baseStart_4070497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070524 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_4070524 : Nat := 118140960795 + 4070524 * 2 ^ 59
def prefixEnd_4070524 : Nat := 4983230072969 + 3 ^ 40 * 4070524 * 2
def baseEnd_4070524 : Nat := 2090135327662137289830007

theorem tailTrace_4070524 : CollatzResearch.WordTrace tailWord_4070524 prefixEnd_4070524 2090135327662137289830007 := by
  unfold tailWord_4070524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74232103552597106498697313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98976138070129475331596417 74232103552597106498697313)
  ·
    refine ⟨55674077664447829874022985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74232103552597106498697313 55674077664447829874022985)
    ·
      refine ⟨41755558248335872405517239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55674077664447829874022985 41755558248335872405517239)
      ·
        refine ⟨62633337372503808608275859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41755558248335872405517239 62633337372503808608275859)
        ·
          refine ⟨93950006058755712912413789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62633337372503808608275859 93950006058755712912413789)
          ·
            refine ⟨35231252272033392342155171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93950006058755712912413789 35231252272033392342155171)
            ·
              refine ⟨52846878408050088513232757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35231252272033392342155171 52846878408050088513232757)
              ·
                refine ⟨4954394850754695798115571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52846878408050088513232757 4954394850754695798115571)
                ·
                  refine ⟨7431592276132043697173357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954394850754695798115571 7431592276132043697173357)
                  ·
                    refine ⟨2786847103549516386440009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7431592276132043697173357 2786847103549516386440009)
                    ·
                      refine ⟨2090135327662137289830007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786847103549516386440009 2090135327662137289830007)
                      ·
                        rfl

theorem cell23_4070524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_4070524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070524 prefixEnd_4070524 := by exact prefixLift 4070524
  have htrace : WordTrace (prefixWord ++ tailWord_4070524) baseStart_4070524 baseEnd_4070524 := by
    simpa [prefixWord, tailWord_4070524, baseEnd_4070524] using wordTrace_append hprefix tailTrace_4070524
  have hstable : (prefixWord ++ tailWord_4070524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070524).length < 2 ^ (prefixWord ++ tailWord_4070524).sum := by decide
  have hdescent : baseEnd_4070524 < baseStart_4070524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070558 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_4070558 : Nat := 118140960795 + 4070558 * 2 ^ 59
def prefixEnd_4070558 : Nat := 4983230072969 + 3 ^ 40 * 4070558 * 2
def baseEnd_4070558 : Nat := 2090152786004390156804851

theorem tailTrace_4070558 : CollatzResearch.WordTrace tailWord_4070558 prefixEnd_4070558 2090152786004390156804851 := by
  unfold tailWord_4070558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18558180898383879600516541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98976964791380691202754885 18558180898383879600516541)
  ·
    refine ⟨6959317836893954850193703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18558180898383879600516541 6959317836893954850193703)
    ·
      refine ⟨10438976755340932275290555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6959317836893954850193703 10438976755340932275290555)
      ·
        refine ⟨15658465133011398412935833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10438976755340932275290555 15658465133011398412935833)
        ·
          refine ⟨11743848849758548809701875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15658465133011398412935833 11743848849758548809701875)
          ·
            refine ⟨17615773274637823214552813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11743848849758548809701875 17615773274637823214552813)
            ·
              refine ⟨6605914977989183705457305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17615773274637823214552813 6605914977989183705457305)
              ·
                refine ⟨4954436233491887779092979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6605914977989183705457305 4954436233491887779092979)
                ·
                  refine ⟨7431654350237831668639469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954436233491887779092979 7431654350237831668639469)
                  ·
                    refine ⟨2786870381339186875739801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7431654350237831668639469 2786870381339186875739801)
                    ·
                      refine ⟨2090152786004390156804851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786870381339186875739801 2090152786004390156804851)
                      ·
                        rfl

theorem cell23_4070558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_4070558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070558 prefixEnd_4070558 := by exact prefixLift 4070558
  have htrace : WordTrace (prefixWord ++ tailWord_4070558) baseStart_4070558 baseEnd_4070558 := by
    simpa [prefixWord, tailWord_4070558, baseEnd_4070558] using wordTrace_append hprefix tailTrace_4070558
  have hstable : (prefixWord ++ tailWord_4070558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070558).length < 2 ^ (prefixWord ++ tailWord_4070558).sum := by decide
  have hdescent : baseEnd_4070558 < baseStart_4070558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070560 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 9]
def baseStart_4070560 : Nat := 118140960795 + 4070560 * 2 ^ 59
def prefixEnd_4070560 : Nat := 4983230072969 + 3 ^ 40 * 4070560 * 2
def baseEnd_4070560 : Nat := 232239312551744349886649

theorem tailTrace_4070560 : CollatzResearch.WordTrace tailWord_4070560 prefixEnd_4070560 232239312551744349886649 := by
  unfold tailWord_4070560
  simp only [CollatzResearch.WordTrace]
  refine ⟨74232760066531895572852567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98977013422042527430470089 74232760066531895572852567)
  ·
    refine ⟨111349140099797843359278851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74232760066531895572852567 111349140099797843359278851)
    ·
      refine ⟨167023710149696765038918277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111349140099797843359278851 167023710149696765038918277)
      ·
        refine ⟨31316945653068143444797177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167023710149696765038918277 31316945653068143444797177)
        ·
          refine ⟨23487709239801107583597883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31316945653068143444797177 23487709239801107583597883)
          ·
            refine ⟨35231563859701661375396825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23487709239801107583597883 35231563859701661375396825)
            ·
              refine ⟨26423672894776246031547619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35231563859701661375396825 26423672894776246031547619)
              ·
                refine ⟨39635509342164369047321429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26423672894776246031547619 39635509342164369047321429)
                ·
                  refine ⟨232239312551744349886649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39635509342164369047321429 232239312551744349886649)
                  ·
                    rfl

theorem cell23_4070560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_4070560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070560 prefixEnd_4070560 := by exact prefixLift 4070560
  have htrace : WordTrace (prefixWord ++ tailWord_4070560) baseStart_4070560 baseEnd_4070560 := by
    simpa [prefixWord, tailWord_4070560, baseEnd_4070560] using wordTrace_append hprefix tailTrace_4070560
  have hstable : (prefixWord ++ tailWord_4070560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070560).length < 2 ^ (prefixWord ++ tailWord_4070560).sum := by decide
  have hdescent : baseEnd_4070560 < baseStart_4070560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070588 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_4070588 : Nat := 118140960795 + 4070588 * 2 ^ 59
def prefixEnd_4070588 : Nat := 4983230072969 + 3 ^ 40 * 4070588 * 2
def baseEnd_4070588 : Nat := 2090168190424025039429713

theorem tailTrace_4070588 : CollatzResearch.WordTrace tailWord_4070588 prefixEnd_4070588 2090168190424025039429713 := by
  unfold tailWord_4070588
  simp only [CollatzResearch.WordTrace]
  refine ⟨74233270688481175963862209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98977694251308234618482945 74233270688481175963862209)
  ·
    refine ⟨55674953016360881972896657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74233270688481175963862209 55674953016360881972896657)
    ·
      refine ⟨41756214762270661479672493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55674953016360881972896657 41756214762270661479672493)
      ·
        refine ⟨15658580535851498054877185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41756214762270661479672493 15658580535851498054877185)
        ·
          refine ⟨11743935401888623541157889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15658580535851498054877185 11743935401888623541157889)
          ·
            refine ⟨8807951551416467655868417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11743935401888623541157889 8807951551416467655868417)
            ·
              refine ⟨6605963663562350741901313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807951551416467655868417 6605963663562350741901313)
              ·
                refine ⟨4954472747671763056425985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6605963663562350741901313 4954472747671763056425985)
                ·
                  refine ⟨3715854560753822292319489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4954472747671763056425985 3715854560753822292319489)
                  ·
                    refine ⟨2786890920565366719239617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3715854560753822292319489 2786890920565366719239617)
                    ·
                      refine ⟨2090168190424025039429713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786890920565366719239617 2090168190424025039429713)
                      ·
                        rfl

theorem cell23_4070588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_4070588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070588 prefixEnd_4070588 := by exact prefixLift 4070588
  have htrace : WordTrace (prefixWord ++ tailWord_4070588) baseStart_4070588 baseEnd_4070588 := by
    simpa [prefixWord, tailWord_4070588, baseEnd_4070588] using wordTrace_append hprefix tailTrace_4070588
  have hstable : (prefixWord ++ tailWord_4070588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070588).length < 2 ^ (prefixWord ++ tailWord_4070588).sum := by decide
  have hdescent : baseEnd_4070588 < baseStart_4070588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070598 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4070598 : Nat := 118140960795 + 4070598 * 2 ^ 59
def prefixEnd_4070598 : Nat := 4983230072969 + 3 ^ 40 * 4070598 * 2
def baseEnd_4070598 : Nat := 696724441743523333434889

theorem tailTrace_4070598 : CollatzResearch.WordTrace tailWord_4070598 prefixEnd_4070598 696724441743523333434889 := by
  unfold tailWord_4070598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639590815841441363612139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98977937404617415757058965 4639590815841441363612139)
  ·
    refine ⟨6959386223762162045418209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4639590815841441363612139 6959386223762162045418209)
    ·
      refine ⟨5219539667821621534063657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6959386223762162045418209 5219539667821621534063657)
      ·
        refine ⟨3914654750866216150547743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5219539667821621534063657 3914654750866216150547743)
        ·
          refine ⟨5871982126299324225821615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914654750866216150547743 5871982126299324225821615)
          ·
            refine ⟨8807973189448986338732423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871982126299324225821615 8807973189448986338732423)
            ·
              refine ⟨13211959784173479508098635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807973189448986338732423 13211959784173479508098635)
              ·
                refine ⟨19817939676260219262147953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13211959784173479508098635 19817939676260219262147953)
                ·
                  refine ⟨14863454757195164446610965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19817939676260219262147953 14863454757195164446610965)
                  ·
                    refine ⟨696724441743523333434889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14863454757195164446610965 696724441743523333434889)
                    ·
                      rfl

theorem cell23_4070598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4070598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070598 prefixEnd_4070598 := by exact prefixLift 4070598
  have htrace : WordTrace (prefixWord ++ tailWord_4070598) baseStart_4070598 baseEnd_4070598 := by
    simpa [prefixWord, tailWord_4070598, baseEnd_4070598] using wordTrace_append hprefix tailTrace_4070598
  have hstable : (prefixWord ++ tailWord_4070598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070598).length < 2 ^ (prefixWord ++ tailWord_4070598).sum := by decide
  have hdescent : baseEnd_4070598 < baseStart_4070598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070605 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4070605 : Nat := 118140960795 + 4070605 * 2 ^ 59
def prefixEnd_4070605 : Nat := 4983230072969 + 3 ^ 40 * 4070605 * 2
def baseEnd_4070605 : Nat := 2090176919595151472917135

theorem tailTrace_4070605 : CollatzResearch.WordTrace tailWord_4070605 prefixEnd_4070605 2090176919595151472917135 := by
  unfold tailWord_4070605
  simp only [CollatzResearch.WordTrace]
  refine ⟨148467161417900763831093269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98978107611933842554062179 148467161417900763831093269)
  ·
    refine ⟨6959398191464098304582497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148467161417900763831093269 6959398191464098304582497)
    ·
      refine ⟨5219548643598073728436873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6959398191464098304582497 5219548643598073728436873)
      ·
        refine ⟨3914661482698555296327655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5219548643598073728436873 3914661482698555296327655)
        ·
          refine ⟨5871992224047832944491483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914661482698555296327655 5871992224047832944491483)
          ·
            refine ⟨8807988336071749416737225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871992224047832944491483 8807988336071749416737225)
            ·
              refine ⟨6605991252053812062552919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807988336071749416737225 6605991252053812062552919)
              ·
                refine ⟨9908986878080718093829379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605991252053812062552919 9908986878080718093829379)
                ·
                  refine ⟨14863480317121077140744069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908986878080718093829379 14863480317121077140744069)
                  ·
                    refine ⟨2786902559460201963889513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14863480317121077140744069 2786902559460201963889513)
                    ·
                      refine ⟨2090176919595151472917135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2786902559460201963889513 2090176919595151472917135)
                      ·
                        rfl

theorem cell23_4070605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4070605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070605 prefixEnd_4070605 := by exact prefixLift 4070605
  have htrace : WordTrace (prefixWord ++ tailWord_4070605) baseStart_4070605 baseEnd_4070605 := by
    simpa [prefixWord, tailWord_4070605, baseEnd_4070605] using wordTrace_append hprefix tailTrace_4070605
  have hstable : (prefixWord ++ tailWord_4070605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070605).length < 2 ^ (prefixWord ++ tailWord_4070605).sum := by decide
  have hdescent : baseEnd_4070605 < baseStart_4070605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070624 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 2, 5]
def baseStart_4070624 : Nat := 118140960795 + 4070624 * 2 ^ 59
def prefixEnd_4070624 : Nat := 4983230072969 + 3 ^ 40 * 4070624 * 2
def baseEnd_4070624 : Nat := 696728891909195632859849

theorem tailTrace_4070624 : CollatzResearch.WordTrace tailWord_4070624 prefixEnd_4070624 696728891909195632859849 := by
  unfold tailWord_4070624
  simp only [CollatzResearch.WordTrace]
  refine ⟨74233927202415965038017463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98978569603221286717356617 74233927202415965038017463)
  ·
    refine ⟨111350890803623947557026195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74233927202415965038017463 111350890803623947557026195)
    ·
      refine ⟨167026336205435921335539293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111350890803623947557026195 167026336205435921335539293)
      ·
        refine ⟨62634876077038470500827235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167026336205435921335539293 62634876077038470500827235)
        ·
          refine ⟨93952314115557705751240853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62634876077038470500827235 93952314115557705751240853)
          ·
            refine ⟨4404014724166767457089415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93952314115557705751240853 4404014724166767457089415)
            ·
              refine ⟨6606022086250151185634123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404014724166767457089415 6606022086250151185634123)
              ·
                refine ⟨9909033129375226778451185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606022086250151185634123 9909033129375226778451185)
                ·
                  refine ⟨7431774847031420083838389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9909033129375226778451185 7431774847031420083838389)
                  ·
                    refine ⟨696728891909195632859849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7431774847031420083838389 696728891909195632859849)
                    ·
                      rfl

theorem cell23_4070624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_4070624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070624 prefixEnd_4070624 := by exact prefixLift 4070624
  have htrace : WordTrace (prefixWord ++ tailWord_4070624) baseStart_4070624 baseEnd_4070624 := by
    simpa [prefixWord, tailWord_4070624, baseEnd_4070624] using wordTrace_append hprefix tailTrace_4070624
  have hstable : (prefixWord ++ tailWord_4070624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070624).length < 2 ^ (prefixWord ++ tailWord_4070624).sum := by decide
  have hdescent : baseEnd_4070624 < baseStart_4070624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070677 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_4070677 : Nat := 118140960795 + 4070677 * 2 ^ 59
def prefixEnd_4070677 : Nat := 4983230072969 + 3 ^ 40 * 4070677 * 2
def baseEnd_4070677 : Nat := 2090213890202275191216803

theorem tailTrace_4070677 : CollatzResearch.WordTrace tailWord_4070677 prefixEnd_4070677 2090213890202275191216803 := by
  unfold tailWord_4070677
  simp only [CollatzResearch.WordTrace]
  refine ⟨148469787473639920127714285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98979858315759946751809523 148469787473639920127714285)
  ·
    refine ⟨55676170302614970047892857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148469787473639920127714285 55676170302614970047892857)
    ·
      refine ⟨41757127726961227535919643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55676170302614970047892857 41757127726961227535919643)
      ·
        refine ⟨62635691590441841303879465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41757127726961227535919643 62635691590441841303879465)
        ·
          refine ⟨46976768692831380977909599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62635691590441841303879465 46976768692831380977909599)
          ·
            refine ⟨70465153039247071466864399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46976768692831380977909599 70465153039247071466864399)
            ·
              refine ⟨105697729558870607200296599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70465153039247071466864399 105697729558870607200296599)
              ·
                refine ⟨158546594338305910800444899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105697729558870607200296599 158546594338305910800444899)
                ·
                  refine ⟨237819891507458866200667349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158546594338305910800444899 237819891507458866200667349)
                  ·
                    refine ⟨5573903707206067176578141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 237819891507458866200667349 5573903707206067176578141)
                    ·
                      refine ⟨2090213890202275191216803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5573903707206067176578141 2090213890202275191216803)
                      ·
                        rfl

theorem cell23_4070677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_4070677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070677 prefixEnd_4070677 := by exact prefixLift 4070677
  have htrace : WordTrace (prefixWord ++ tailWord_4070677) baseStart_4070677 baseEnd_4070677 := by
    simpa [prefixWord, tailWord_4070677, baseEnd_4070677] using wordTrace_append hprefix tailTrace_4070677
  have hstable : (prefixWord ++ tailWord_4070677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070677).length < 2 ^ (prefixWord ++ tailWord_4070677).sum := by decide
  have hdescent : baseEnd_4070677 < baseStart_4070677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070734 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_4070734 : Nat := 118140960795 + 4070734 * 2 ^ 59
def prefixEnd_4070734 : Nat := 4983230072969 + 3 ^ 40 * 4070734 * 2
def baseEnd_4070734 : Nat := 2090243158599581468204041

theorem tailTrace_4070734 : CollatzResearch.WordTrace tailWord_4070734 prefixEnd_4070734 2090243158599581468204041 := by
  unfold tailWord_4070734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18558983304304177357817407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98981244289622279241692837 18558983304304177357817407)
  ·
    refine ⟨27838474956456266036726111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18558983304304177357817407 27838474956456266036726111)
    ·
      refine ⟨41757712434684399055089167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27838474956456266036726111 41757712434684399055089167)
      ·
        refine ⟨62636568652026598582633751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41757712434684399055089167 62636568652026598582633751)
        ·
          refine ⟨93954852978039897873950627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62636568652026598582633751 93954852978039897873950627)
          ·
            refine ⟨140932279467059846810925941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93954852978039897873950627 140932279467059846810925941)
            ·
              refine ⟨13212401200036860638524307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140932279467059846810925941 13212401200036860638524307)
              ·
                refine ⟨19818601800055290957786461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212401200036860638524307 19818601800055290957786461)
                ·
                  refine ⟨7431975675020734109169923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19818601800055290957786461 7431975675020734109169923)
                  ·
                    refine ⟨11147963512531101163754885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431975675020734109169923 11147963512531101163754885)
                    ·
                      refine ⟨2090243158599581468204041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11147963512531101163754885 2090243158599581468204041)
                      ·
                        rfl

theorem cell23_4070734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_4070734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070734 prefixEnd_4070734 := by exact prefixLift 4070734
  have htrace : WordTrace (prefixWord ++ tailWord_4070734) baseStart_4070734 baseEnd_4070734 := by
    simpa [prefixWord, tailWord_4070734, baseEnd_4070734] using wordTrace_append hprefix tailTrace_4070734
  have hstable : (prefixWord ++ tailWord_4070734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070734).length < 2 ^ (prefixWord ++ tailWord_4070734).sum := by decide
  have hdescent : baseEnd_4070734 < baseStart_4070734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070777 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_4070777 : Nat := 118140960795 + 4070777 * 2 ^ 59
def prefixEnd_4070777 : Nat := 4983230072969 + 3 ^ 40 * 4070777 * 2
def baseEnd_4070777 : Nat := 2090265238267724799966343

theorem tailTrace_4070777 : CollatzResearch.WordTrace tailWord_4070777 prefixEnd_4070777 2090265238267724799966343 := by
  unfold tailWord_4070777
  simp only [CollatzResearch.WordTrace]
  refine ⟨148473434773277637206354585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98982289848851758137569723 148473434773277637206354585)
  ·
    refine ⟨111355076079958227904765939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148473434773277637206354585 111355076079958227904765939)
    ·
      refine ⟨167032614119937341857148909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111355076079958227904765939 167032614119937341857148909)
      ·
        refine ⟨62637230294976503196430841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167032614119937341857148909 62637230294976503196430841)
        ·
          refine ⟨46977922721232377397323131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62637230294976503196430841 46977922721232377397323131)
          ·
            refine ⟨70466884081848566095984697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46977922721232377397323131 70466884081848566095984697)
            ·
              refine ⟨52850163061386424571988523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70466884081848566095984697 52850163061386424571988523)
              ·
                refine ⟨79275244592079636857982785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52850163061386424571988523 79275244592079636857982785)
                ·
                  refine ⟨59456433444059727643487089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79275244592079636857982785 59456433444059727643487089)
                  ·
                    refine ⟨44592325083044795732615317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59456433444059727643487089 44592325083044795732615317)
                    ·
                      refine ⟨2090265238267724799966343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44592325083044795732615317 2090265238267724799966343)
                      ·
                        rfl

theorem cell23_4070777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_4070777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070777 prefixEnd_4070777 := by exact prefixLift 4070777
  have htrace : WordTrace (prefixWord ++ tailWord_4070777) baseStart_4070777 baseEnd_4070777 := by
    simpa [prefixWord, tailWord_4070777, baseEnd_4070777] using wordTrace_append hprefix tailTrace_4070777
  have hstable : (prefixWord ++ tailWord_4070777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070777).length < 2 ^ (prefixWord ++ tailWord_4070777).sum := by decide
  have hdescent : baseEnd_4070777 < baseStart_4070777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070785 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4070785 : Nat := 118140960795 + 4070785 * 2 ^ 59
def prefixEnd_4070785 : Nat := 4983230072969 + 3 ^ 40 * 4070785 * 2
def baseEnd_4070785 : Nat := 2090269346112960768666307

theorem tailTrace_4070785 : CollatzResearch.WordTrace tailWord_4070785 prefixEnd_4070785 2090269346112960768666307 := by
  unfold tailWord_4070785
  simp only [CollatzResearch.WordTrace]
  refine ⟨148473726557248654572645809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98982484371499103048430539 148473726557248654572645809)
  ·
    refine ⟨111355294917936490929484357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148473726557248654572645809 111355294917936490929484357)
    ·
      refine ⟨20879117797113092049278317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111355294917936490929484357 20879117797113092049278317)
      ·
        refine ⟨7829669173917409518479369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20879117797113092049278317 7829669173917409518479369)
        ·
          refine ⟨5872251880438057138859527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7829669173917409518479369 5872251880438057138859527)
          ·
            refine ⟨8808377820657085708289291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872251880438057138859527 8808377820657085708289291)
            ·
              refine ⟨13212566730985628562433937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808377820657085708289291 13212566730985628562433937)
              ·
                refine ⟨9909425048239221421825453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13212566730985628562433937 9909425048239221421825453)
                ·
                  refine ⟨3716034393089708033184545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9909425048239221421825453 3716034393089708033184545)
                  ·
                    refine ⟨2787025794817281024888409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716034393089708033184545 2787025794817281024888409)
                    ·
                      refine ⟨2090269346112960768666307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787025794817281024888409 2090269346112960768666307)
                      ·
                        rfl

theorem cell23_4070785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4070785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070785 prefixEnd_4070785 := by exact prefixLift 4070785
  have htrace : WordTrace (prefixWord ++ tailWord_4070785) baseStart_4070785 baseEnd_4070785 := by
    simpa [prefixWord, tailWord_4070785, baseEnd_4070785] using wordTrace_append hprefix tailTrace_4070785
  have hstable : (prefixWord ++ tailWord_4070785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070785).length < 2 ^ (prefixWord ++ tailWord_4070785).sum := by decide
  have hdescent : baseEnd_4070785 < baseStart_4070785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070802 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4070802 : Nat := 118140960795 + 4070802 * 2 ^ 59
def prefixEnd_4070802 : Nat := 4983230072969 + 3 ^ 40 * 4070802 * 2
def baseEnd_4070802 : Nat := 2090278075284087202153729

theorem tailTrace_4070802 : CollatzResearch.WordTrace tailWord_4070802 prefixEnd_4070802 2090278075284087202153729 := by
  unfold tailWord_4070802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37118586649546766619003665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98982897732124710984009773 37118586649546766619003665)
  ·
    refine ⟨27838939987160074964252749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37118586649546766619003665 27838939987160074964252749)
    ·
      refine ⟨10439602495185028111594781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27838939987160074964252749 10439602495185028111594781)
      ·
        refine ⟨3914850935694385541848043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10439602495185028111594781 3914850935694385541848043)
        ·
          refine ⟨5872276403541578312772065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914850935694385541848043 5872276403541578312772065)
          ·
            refine ⟨4404207302656183734579049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5872276403541578312772065 4404207302656183734579049)
            ·
              refine ⟨3303155476992137800934287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404207302656183734579049 3303155476992137800934287)
              ·
                refine ⟨4954733215488206701401431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303155476992137800934287 4954733215488206701401431)
                ·
                  refine ⟨7432099823232310052102147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954733215488206701401431 7432099823232310052102147)
                  ·
                    refine ⟨11148149734848465078153221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7432099823232310052102147 11148149734848465078153221)
                    ·
                      refine ⟨2090278075284087202153729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11148149734848465078153221 2090278075284087202153729)
                      ·
                        rfl

theorem cell23_4070802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4070802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070802 prefixEnd_4070802 := by exact prefixLift 4070802
  have htrace : WordTrace (prefixWord ++ tailWord_4070802) baseStart_4070802 baseEnd_4070802 := by
    simpa [prefixWord, tailWord_4070802, baseEnd_4070802] using wordTrace_append hprefix tailTrace_4070802
  have hstable : (prefixWord ++ tailWord_4070802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070802).length < 2 ^ (prefixWord ++ tailWord_4070802).sum := by decide
  have hdescent : baseEnd_4070802 < baseStart_4070802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070812 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_4070812 : Nat := 118140960795 + 4070812 * 2 ^ 59
def prefixEnd_4070812 : Nat := 4983230072969 + 3 ^ 40 * 4070812 * 2
def baseEnd_4070812 : Nat := 696761070030210721009561

theorem tailTrace_4070812 : CollatzResearch.WordTrace tailWord_4070812 prefixEnd_4070812 696761070030210721009561 := by
  unfold tailWord_4070812
  simp only [CollatzResearch.WordTrace]
  refine ⟨74237355664075419091939345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98983140885433892122585793 74237355664075419091939345)
  ·
    refine ⟨55678016748056564318954509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74237355664075419091939345 55678016748056564318954509)
    ·
      refine ⟨20879256280521211619607941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55678016748056564318954509 20879256280521211619607941)
      ·
        refine ⟨3914860552597727178676489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20879256280521211619607941 3914860552597727178676489)
        ·
          refine ⟨2936145414448295384007367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3914860552597727178676489 2936145414448295384007367)
          ·
            refine ⟨4404218121672443076011051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936145414448295384007367 4404218121672443076011051)
            ·
              refine ⟨6606327182508664614016577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404218121672443076011051 6606327182508664614016577)
              ·
                refine ⟨4954745386881498460512433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606327182508664614016577 4954745386881498460512433)
                ·
                  refine ⟨3716059040161123845384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4954745386881498460512433 3716059040161123845384325)
                  ·
                    refine ⟨696761070030210721009561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716059040161123845384325 696761070030210721009561)
                    ·
                      rfl

theorem cell23_4070812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_4070812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070812 prefixEnd_4070812 := by exact prefixLift 4070812
  have htrace : WordTrace (prefixWord ++ tailWord_4070812) baseStart_4070812 baseEnd_4070812 := by
    simpa [prefixWord, tailWord_4070812, baseEnd_4070812] using wordTrace_append hprefix tailTrace_4070812
  have hstable : (prefixWord ++ tailWord_4070812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070812).length < 2 ^ (prefixWord ++ tailWord_4070812).sum := by decide
  have hdescent : baseEnd_4070812 < baseStart_4070812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070818 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_4070818 : Nat := 118140960795 + 4070818 * 2 ^ 59
def prefixEnd_4070818 : Nat := 4983230072969 + 3 ^ 40 * 4070818 * 2
def baseEnd_4070818 : Nat := 2090286290974559139553655

theorem tailTrace_4070818 : CollatzResearch.WordTrace tailWord_4070818 prefixEnd_4070818 2090286290974559139553655 := by
  unfold tailWord_4070818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37118732541532275302149277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98983286777419400805731405 37118732541532275302149277)
  ·
    refine ⟨13919524703074603238305979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37118732541532275302149277 13919524703074603238305979)
    ·
      refine ⟨20879287054611904857458969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919524703074603238305979 20879287054611904857458969)
      ·
        refine ⟨15659465290958928643094227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20879287054611904857458969 15659465290958928643094227)
        ·
          refine ⟨23489197936438392964641341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15659465290958928643094227 23489197936438392964641341)
          ·
            refine ⟨8808449226164397361740503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23489197936438392964641341 8808449226164397361740503)
            ·
              refine ⟨13212673839246596042610755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808449226164397361740503 13212673839246596042610755)
              ·
                refine ⟨19819010758869894063916133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212673839246596042610755 19819010758869894063916133)
                ·
                  refine ⟨3716064517288105136984275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19819010758869894063916133 3716064517288105136984275)
                  ·
                    refine ⟨5574096775932157705476413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3716064517288105136984275 5574096775932157705476413)
                    ·
                      refine ⟨2090286290974559139553655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574096775932157705476413 2090286290974559139553655)
                      ·
                        rfl

theorem cell23_4070818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_4070818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070818 prefixEnd_4070818 := by exact prefixLift 4070818
  have htrace : WordTrace (prefixWord ++ tailWord_4070818) baseStart_4070818 baseEnd_4070818 := by
    simpa [prefixWord, tailWord_4070818, baseEnd_4070818] using wordTrace_append hprefix tailTrace_4070818
  have hstable : (prefixWord ++ tailWord_4070818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070818).length < 2 ^ (prefixWord ++ tailWord_4070818).sum := by decide
  have hdescent : baseEnd_4070818 < baseStart_4070818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070858 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_4070858 : Nat := 118140960795 + 4070858 * 2 ^ 59
def prefixEnd_4070858 : Nat := 4983230072969 + 3 ^ 40 * 4070858 * 2
def baseEnd_4070858 : Nat := 2090306830200738983053471

theorem tailTrace_4070858 : CollatzResearch.WordTrace tailWord_4070858 prefixEnd_4070858 2090306830200738983053471 := by
  unfold tailWord_4070858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37119097271496047010013307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98984259390656125360035485 37119097271496047010013307)
  ·
    refine ⟨55678645907244070515019961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37119097271496047010013307 55678645907244070515019961)
    ·
      refine ⟨41758984430433052886264971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55678645907244070515019961 41758984430433052886264971)
      ·
        refine ⟨62638476645649579329397457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41758984430433052886264971 62638476645649579329397457)
        ·
          refine ⟨46978857484237184497048093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62638476645649579329397457 46978857484237184497048093)
          ·
            refine ⟨17617071556588944186393035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46978857484237184497048093 17617071556588944186393035)
            ·
              refine ⟨26425607334883416279589553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17617071556588944186393035 26425607334883416279589553)
              ·
                refine ⟨19819205501162562209692165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26425607334883416279589553 19819205501162562209692165)
                ·
                  refine ⟨3716101031467980414317281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19819205501162562209692165 3716101031467980414317281)
                  ·
                    refine ⟨2787075773600985310737961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716101031467980414317281 2787075773600985310737961)
                    ·
                      refine ⟨2090306830200738983053471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787075773600985310737961 2090306830200738983053471)
                      ·
                        rfl

theorem cell23_4070858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_4070858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070858 prefixEnd_4070858 := by exact prefixLift 4070858
  have htrace : WordTrace (prefixWord ++ tailWord_4070858) baseStart_4070858 baseEnd_4070858 := by
    simpa [prefixWord, tailWord_4070858, baseEnd_4070858] using wordTrace_append hprefix tailTrace_4070858
  have hstable : (prefixWord ++ tailWord_4070858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070858).length < 2 ^ (prefixWord ++ tailWord_4070858).sum := by decide
  have hdescent : baseEnd_4070858 < baseStart_4070858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070881 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 7]
def baseStart_4070881 : Nat := 118140960795 + 4070881 * 2 ^ 59
def prefixEnd_4070881 : Nat := 4983230072969 + 3 ^ 40 * 4070881 * 2
def baseEnd_4070881 : Nat := 232257626695088043673985

theorem tailTrace_4070881 : CollatzResearch.WordTrace tailWord_4070881 prefixEnd_4070881 232257626695088043673985 := by
  unfold tailWord_4070881
  simp only [CollatzResearch.WordTrace]
  refine ⟨148477227964900862968140497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98984818643267241978760331 148477227964900862968140497)
  ·
    refine ⟨111357920973675647226105373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148477227964900862968140497 111357920973675647226105373)
    ·
      refine ⟨41759220365128367709789515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111357920973675647226105373 41759220365128367709789515)
      ·
        refine ⟨62638830547692551564684273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41759220365128367709789515 62638830547692551564684273)
        ·
          refine ⟨46979122910769413673513205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62638830547692551564684273 46979122910769413673513205)
          ·
            refine ⟨4404292772884632531891863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46979122910769413673513205 4404292772884632531891863)
            ·
              refine ⟨6606439159326948797837795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404292772884632531891863 6606439159326948797837795)
              ·
                refine ⟨9909658738990423196756693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606439159326948797837795 9909658738990423196756693)
                ·
                  refine ⟨232257626695088043673985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9909658738990423196756693 232257626695088043673985)
                  ·
                    rfl

theorem cell23_4070881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 7].length) (baseStart_4070881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070881 prefixEnd_4070881 := by exact prefixLift 4070881
  have htrace : WordTrace (prefixWord ++ tailWord_4070881) baseStart_4070881 baseEnd_4070881 := by
    simpa [prefixWord, tailWord_4070881, baseEnd_4070881] using wordTrace_append hprefix tailTrace_4070881
  have hstable : (prefixWord ++ tailWord_4070881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070881).length < 2 ^ (prefixWord ++ tailWord_4070881).sum := by decide
  have hdescent : baseEnd_4070881 < baseStart_4070881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070931 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 4]
def baseStart_4070931 : Nat := 118140960795 + 4070931 * 2 ^ 59
def prefixEnd_4070931 : Nat := 4983230072969 + 3 ^ 40 * 4070931 * 2
def baseEnd_4070931 : Nat := 2090344314288517197440635

theorem tailTrace_4070931 : CollatzResearch.WordTrace tailWord_4070931 prefixEnd_4070931 2090344314288517197440635 := by
  unfold tailWord_4070931
  simp only [CollatzResearch.WordTrace]
  refine ⟨148479051614719721507460647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98986034409813147671640431 148479051614719721507460647)
  ·
    refine ⟨222718577422079582261190971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148479051614719721507460647 222718577422079582261190971)
    ·
      refine ⟨334077866133119373391786457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222718577422079582261190971 334077866133119373391786457)
      ·
        refine ⟨250558399599839530043839843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334077866133119373391786457 250558399599839530043839843)
        ·
          refine ⟨375837599399759295065759765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250558399599839530043839843 375837599399759295065759765)
          ·
            refine ⟨17617387471863716956207489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 375837599399759295065759765 17617387471863716956207489)
            ·
              refine ⟨13213040603897787717155617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17617387471863716956207489 13213040603897787717155617)
              ·
                refine ⟨9909780452923340787866713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13213040603897787717155617 9909780452923340787866713)
                ·
                  refine ⟨7432335339692505590900035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9909780452923340787866713 7432335339692505590900035)
                  ·
                    refine ⟨11148503009538758386350053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7432335339692505590900035 11148503009538758386350053)
                    ·
                      refine ⟨2090344314288517197440635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11148503009538758386350053 2090344314288517197440635)
                      ·
                        rfl

theorem cell23_4070931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_4070931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070931 prefixEnd_4070931 := by exact prefixLift 4070931
  have htrace : WordTrace (prefixWord ++ tailWord_4070931) baseStart_4070931 baseEnd_4070931 := by
    simpa [prefixWord, tailWord_4070931, baseEnd_4070931] using wordTrace_append hprefix tailTrace_4070931
  have hstable : (prefixWord ++ tailWord_4070931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070931).length < 2 ^ (prefixWord ++ tailWord_4070931).sum := by decide
  have hdescent : baseEnd_4070931 < baseStart_4070931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070958 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4070958 : Nat := 118140960795 + 4070958 * 2 ^ 59
def prefixEnd_4070958 : Nat := 4983230072969 + 3 ^ 40 * 4070958 * 2
def baseEnd_4070958 : Nat := 696786059422062863934337

theorem tailTrace_4070958 : CollatzResearch.WordTrace tailWord_4070958 prefixEnd_4070958 696786059422062863934337 := by
  unfold tailWord_4070958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560004548202738139836691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98986690923747936745795685 18560004548202738139836691)
  ·
    refine ⟨27840006822304107209755037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18560004548202738139836691 27840006822304107209755037)
    ·
      refine ⟨10440002558364040203658139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27840006822304107209755037 10440002558364040203658139)
      ·
        refine ⟨15660003837546060305487209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10440002558364040203658139 15660003837546060305487209)
        ·
          refine ⟨11745002878159545229115407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15660003837546060305487209 11745002878159545229115407)
          ·
            refine ⟨17617504317239317843673111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11745002878159545229115407 17617504317239317843673111)
            ·
              refine ⟨26426256475858976765509667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17617504317239317843673111 26426256475858976765509667)
              ·
                refine ⟨39639384713788465148264501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26426256475858976765509667 39639384713788465148264501)
                ·
                  refine ⟨3716192316917668607649797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39639384713788465148264501 3716192316917668607649797)
                  ·
                    refine ⟨696786059422062863934337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716192316917668607649797 696786059422062863934337)
                    ·
                      rfl

theorem cell23_4070958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4070958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070958 prefixEnd_4070958 := by exact prefixLift 4070958
  have htrace : WordTrace (prefixWord ++ tailWord_4070958) baseStart_4070958 baseEnd_4070958 := by
    simpa [prefixWord, tailWord_4070958, baseEnd_4070958] using wordTrace_append hprefix tailTrace_4070958
  have hstable : (prefixWord ++ tailWord_4070958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070958).length < 2 ^ (prefixWord ++ tailWord_4070958).sum := by decide
  have hdescent : baseEnd_4070958 < baseStart_4070958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070968 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_4070968 : Nat := 118140960795 + 4070968 * 2 ^ 59
def prefixEnd_4070968 : Nat := 4983230072969 + 3 ^ 40 * 4070968 * 2
def baseEnd_4070968 : Nat := 2090363313072733552677965

theorem tailTrace_4070968 : CollatzResearch.WordTrace tailWord_4070968 prefixEnd_4070968 2090363313072733552677965 := by
  unfold tailWord_4070968
  simp only [CollatzResearch.WordTrace]
  refine ⟨74240200557792838413278779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98986934077057117884371705 74240200557792838413278779)
  ·
    refine ⟨111360300836689257619918169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74240200557792838413278779 111360300836689257619918169)
    ·
      refine ⟨83520225627516943214938627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111360300836689257619918169 83520225627516943214938627)
      ·
        refine ⟨125280338441275414822407941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83520225627516943214938627 125280338441275414822407941)
        ·
          refine ⟨23490063457739140279201489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125280338441275414822407941 23490063457739140279201489)
          ·
            refine ⟨17617547593304355209401117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23490063457739140279201489 17617547593304355209401117)
            ·
              refine ⟨6606580347489133203525419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17617547593304355209401117 6606580347489133203525419)
              ·
                refine ⟨9909870521233699805288129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606580347489133203525419 9909870521233699805288129)
                ·
                  refine ⟨7432402890925274853966097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9909870521233699805288129 7432402890925274853966097)
                  ·
                    refine ⟨5574302168193956140474573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7432402890925274853966097 5574302168193956140474573)
                    ·
                      refine ⟨2090363313072733552677965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574302168193956140474573 2090363313072733552677965)
                      ·
                        rfl

theorem cell23_4070968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_4070968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070968 prefixEnd_4070968 := by exact prefixLift 4070968
  have htrace : WordTrace (prefixWord ++ tailWord_4070968) baseStart_4070968 baseEnd_4070968 := by
    simpa [prefixWord, tailWord_4070968, baseEnd_4070968] using wordTrace_append hprefix tailTrace_4070968
  have hstable : (prefixWord ++ tailWord_4070968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070968).length < 2 ^ (prefixWord ++ tailWord_4070968).sum := by decide
  have hdescent : baseEnd_4070968 < baseStart_4070968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070975 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 1, 4]
def baseStart_4070975 : Nat := 118140960795 + 4070975 * 2 ^ 59
def prefixEnd_4070975 : Nat := 4983230072969 + 3 ^ 40 * 4070975 * 2
def baseEnd_4070975 : Nat := 696788969145771675096811

theorem tailTrace_4070975 : CollatzResearch.WordTrace tailWord_4070975 prefixEnd_4070975 696788969145771675096811 := by
  unfold tailWord_4070975
  simp only [CollatzResearch.WordTrace]
  refine ⟨148480656426560317022062379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98987104284373544681374919 148480656426560317022062379)
  ·
    refine ⟨222720984639840475533093569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148480656426560317022062379 222720984639840475533093569)
    ·
      refine ⟨167040738479880356649820177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222720984639840475533093569 167040738479880356649820177)
      ·
        refine ⟨125280553859910267487365133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167040738479880356649820177 125280553859910267487365133)
        ·
          refine ⟨46980207697466350307761925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125280553859910267487365133 46980207697466350307761925)
          ·
            refine ⟨8808788943274940682705361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46980207697466350307761925 8808788943274940682705361)
            ·
              refine ⟨6606591707456205512029021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8808788943274940682705361 6606591707456205512029021)
              ·
                refine ⟨2477471890296077067010883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6606591707456205512029021 2477471890296077067010883)
                ·
                  refine ⟨3716207835444115600516325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477471890296077067010883 3716207835444115600516325)
                  ·
                    refine ⟨696788969145771675096811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716207835444115600516325 696788969145771675096811)
                    ·
                      rfl

theorem cell23_4070975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 4].length) (baseStart_4070975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070975 prefixEnd_4070975 := by exact prefixLift 4070975
  have htrace : WordTrace (prefixWord ++ tailWord_4070975) baseStart_4070975 baseEnd_4070975 := by
    simpa [prefixWord, tailWord_4070975, baseEnd_4070975] using wordTrace_append hprefix tailTrace_4070975
  have hstable : (prefixWord ++ tailWord_4070975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070975).length < 2 ^ (prefixWord ++ tailWord_4070975).sum := by decide
  have hdescent : baseEnd_4070975 < baseStart_4070975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070988 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 6]
def baseStart_4070988 : Nat := 118140960795 + 4070988 * 2 ^ 59
def prefixEnd_4070988 : Nat := 4983230072969 + 3 ^ 40 * 4070988 * 2
def baseEnd_4070988 : Nat := 232263731409535941603097

theorem tailTrace_4070988 : CollatzResearch.WordTrace tailWord_4070988 prefixEnd_4070988 232263731409535941603097 := by
  unfold tailWord_4070988
  simp only [CollatzResearch.WordTrace]
  refine ⟨74240565287756610121142809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98987420383675480161523745 74240565287756610121142809)
  ·
    refine ⟨55680423965817457590857107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74240565287756610121142809 55680423965817457590857107)
    ·
      refine ⟨83520635948726186386285661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55680423965817457590857107 83520635948726186386285661)
      ·
        refine ⟨31320238480772319894857123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83520635948726186386285661 31320238480772319894857123)
        ·
          refine ⟨46980357721158479842285685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31320238480772319894857123 46980357721158479842285685)
          ·
            refine ⟨4404408536358607485214283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46980357721158479842285685 4404408536358607485214283)
            ·
              refine ⟨6606612804537911227821425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404408536358607485214283 6606612804537911227821425)
              ·
                refine ⟨4954959603403433420866069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606612804537911227821425 4954959603403433420866069)
                ·
                  refine ⟨232263731409535941603097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4954959603403433420866069 232263731409535941603097)
                  ·
                    rfl

theorem cell23_4070988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_4070988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4070988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4070988 prefixEnd_4070988 := by exact prefixLift 4070988
  have htrace : WordTrace (prefixWord ++ tailWord_4070988) baseStart_4070988 baseEnd_4070988 := by
    simpa [prefixWord, tailWord_4070988, baseEnd_4070988] using wordTrace_append hprefix tailTrace_4070988
  have hstable : (prefixWord ++ tailWord_4070988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070988).length < 2 ^ (prefixWord ++ tailWord_4070988).sum := by decide
  have hdescent : baseEnd_4070988 < baseStart_4070988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071018 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_4071018 : Nat := 118140960795 + 4071018 * 2 ^ 59
def prefixEnd_4071018 : Nat := 4983230072969 + 3 ^ 40 * 4071018 * 2
def baseEnd_4071018 : Nat := 696796329035152785684245

theorem tailTrace_4071018 : CollatzResearch.WordTrace tailWord_4071018 prefixEnd_4071018 696796329035152785684245 := by
  unfold tailWord_4071018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37120556191351133841469427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98988149843603023577251805 37120556191351133841469427)
  ·
    refine ⟨55680834287026700762204141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37120556191351133841469427 55680834287026700762204141)
    ·
      refine ⟨20880312857635012785826553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55680834287026700762204141 20880312857635012785826553)
      ·
        refine ⟨15660234643226259589369915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20880312857635012785826553 15660234643226259589369915)
        ·
          refine ⟨23490351964839389384054873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660234643226259589369915 23490351964839389384054873)
          ·
            refine ⟨17617763973629542038041155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23490351964839389384054873 17617763973629542038041155)
            ·
              refine ⟨26426645960444313057061733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17617763973629542038041155 26426645960444313057061733)
              ·
                refine ⟨4954996117583308698199075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26426645960444313057061733 4954996117583308698199075)
                ·
                  refine ⟨7432494176374963047298613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954996117583308698199075 7432494176374963047298613)
                  ·
                    refine ⟨696796329035152785684245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7432494176374963047298613 696796329035152785684245)
                    ·
                      rfl

theorem cell23_4071018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_4071018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071018 prefixEnd_4071018 := by exact prefixLift 4071018
  have htrace : WordTrace (prefixWord ++ tailWord_4071018) baseStart_4071018 baseEnd_4071018 := by
    simpa [prefixWord, tailWord_4071018, baseEnd_4071018] using wordTrace_append hprefix tailTrace_4071018
  have hstable : (prefixWord ++ tailWord_4071018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071018).length < 2 ^ (prefixWord ++ tailWord_4071018).sum := by decide
  have hdescent : baseEnd_4071018 < baseStart_4071018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071088 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 6, 1, 3]
def baseStart_4071088 : Nat := 118140960795 + 4071088 * 2 ^ 59
def prefixEnd_4071088 : Nat := 4983230072969 + 3 ^ 40 * 4071088 * 2
def baseEnd_4071088 : Nat := 2090424930751273083177413

theorem tailTrace_4071088 : CollatzResearch.WordTrace tailWord_4071088 prefixEnd_4071088 2090424930751273083177413 := by
  unfold tailWord_4071088
  simp only [CollatzResearch.WordTrace]
  refine ⟨74242388937575468660462959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98989851916767291547283945 74242388937575468660462959)
  ·
    refine ⟨111363583406363202990694439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74242388937575468660462959 111363583406363202990694439)
    ·
      refine ⟨167045375109544804486041659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111363583406363202990694439 167045375109544804486041659)
      ·
        refine ⟨250568062664317206729062489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167045375109544804486041659 250568062664317206729062489)
        ·
          refine ⟨187926046998237905046796867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250568062664317206729062489 187926046998237905046796867)
          ·
            refine ⟨281889070497356857570195301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187926046998237905046796867 281889070497356857570195301)
            ·
              refine ⟨52854200718254410794411619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281889070497356857570195301 52854200718254410794411619)
              ·
                refine ⟨79281301077381616191617429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52854200718254410794411619 79281301077381616191617429)
                ·
                  refine ⟨3716310988002263258982067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79281301077381616191617429 3716310988002263258982067)
                  ·
                    refine ⟨5574466482003394888473101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3716310988002263258982067 5574466482003394888473101)
                    ·
                      refine ⟨2090424930751273083177413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574466482003394888473101 2090424930751273083177413)
                      ·
                        rfl

theorem cell23_4071088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_4071088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071088 prefixEnd_4071088 := by exact prefixLift 4071088
  have htrace : WordTrace (prefixWord ++ tailWord_4071088) baseStart_4071088 baseEnd_4071088 := by
    simpa [prefixWord, tailWord_4071088, baseEnd_4071088] using wordTrace_append hprefix tailTrace_4071088
  have hstable : (prefixWord ++ tailWord_4071088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071088).length < 2 ^ (prefixWord ++ tailWord_4071088).sum := by decide
  have hdescent : baseEnd_4071088 < baseStart_4071088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071111 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_4071111 : Nat := 118140960795 + 4071111 * 2 ^ 59
def prefixEnd_4071111 : Nat := 4983230072969 + 3 ^ 40 * 4071111 * 2
def baseEnd_4071111 : Nat := 2090436740806326493189807

theorem tailTrace_4071111 : CollatzResearch.WordTrace tailWord_4071111 prefixEnd_4071111 2090436740806326493189807 := by
  unfold tailWord_4071111
  simp only [CollatzResearch.WordTrace]
  refine ⟨148485616754067612249013187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98990411169378408166008791 148485616754067612249013187)
  ·
    refine ⟨222728425131101418373519781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148485616754067612249013187 222728425131101418373519781)
    ·
      refine ⟨41761579712081515945034959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222728425131101418373519781 41761579712081515945034959)
      ·
        refine ⟨62642369568122273917552439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41761579712081515945034959 62642369568122273917552439)
        ·
          refine ⟨93963554352183410876328659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62642369568122273917552439 93963554352183410876328659)
          ·
            refine ⟨140945331528275116314492989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93963554352183410876328659 140945331528275116314492989)
            ·
              refine ⟨52854499323103168617934871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140945331528275116314492989 52854499323103168617934871)
              ·
                refine ⟨79281748984654752926902307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52854499323103168617934871 79281748984654752926902307)
                ·
                  refine ⟨118922623476982129390353461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79281748984654752926902307 118922623476982129390353461)
                  ·
                    refine ⟨11148995950967074630345637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118922623476982129390353461 11148995950967074630345637)
                    ·
                      refine ⟨2090436740806326493189807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11148995950967074630345637 2090436740806326493189807)
                      ·
                        rfl

theorem cell23_4071111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_4071111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071111 prefixEnd_4071111 := by exact prefixLift 4071111
  have htrace : WordTrace (prefixWord ++ tailWord_4071111) baseStart_4071111 baseEnd_4071111 := by
    simpa [prefixWord, tailWord_4071111, baseEnd_4071111] using wordTrace_append hprefix tailTrace_4071111
  have hstable : (prefixWord ++ tailWord_4071111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071111).length < 2 ^ (prefixWord ++ tailWord_4071111).sum := by decide
  have hdescent : baseEnd_4071111 < baseStart_4071111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071121 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_4071121 : Nat := 118140960795 + 4071121 * 2 ^ 59
def prefixEnd_4071121 : Nat := 4983230072969 + 3 ^ 40 * 4071121 * 2
def baseEnd_4071121 : Nat := 696813958537623818021587

theorem tailTrace_4071121 : CollatzResearch.WordTrace tailWord_4071121 prefixEnd_4071121 696813958537623818021587 := by
  unfold tailWord_4071121
  simp only [CollatzResearch.WordTrace]
  refine ⟨148485981484031383956877217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98990654322687589304584811 148485981484031383956877217)
  ·
    refine ⟨111364486113023537967657913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148485981484031383956877217 111364486113023537967657913)
    ·
      refine ⟨83523364584767653475743435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111364486113023537967657913 83523364584767653475743435)
      ·
        refine ⟨125285046877151480213615153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83523364584767653475743435 125285046877151480213615153)
        ·
          refine ⟨93963785157863610160211365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125285046877151480213615153 93963785157863610160211365)
          ·
            refine ⟨17618209717099426905039631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93963785157863610160211365 17618209717099426905039631)
            ·
              refine ⟨26427314575649140357559447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17618209717099426905039631 26427314575649140357559447)
              ·
                refine ⟨39640971863473710536339171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26427314575649140357559447 39640971863473710536339171)
                ·
                  refine ⟨59461457795210565804508757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39640971863473710536339171 59461457795210565804508757)
                  ·
                    refine ⟨696813958537623818021587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59461457795210565804508757 696813958537623818021587)
                    ·
                      rfl

theorem cell23_4071121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_4071121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071121 prefixEnd_4071121 := by exact prefixLift 4071121
  have htrace : WordTrace (prefixWord ++ tailWord_4071121) baseStart_4071121 baseEnd_4071121 := by
    simpa [prefixWord, tailWord_4071121, baseEnd_4071121] using wordTrace_append hprefix tailTrace_4071121
  have hstable : (prefixWord ++ tailWord_4071121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071121).length < 2 ^ (prefixWord ++ tailWord_4071121).sum := by decide
  have hdescent : baseEnd_4071121 < baseStart_4071121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071122 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4071122 : Nat := 118140960795 + 4071122 * 2 ^ 59
def prefixEnd_4071122 : Nat := 4983230072969 + 3 ^ 40 * 4071122 * 2
def baseEnd_4071122 : Nat := 2090442389093525950152257

theorem tailTrace_4071122 : CollatzResearch.WordTrace tailWord_4071122 prefixEnd_4071122 2090442389093525950152257 := by
  unfold tailWord_4071122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37121504489256940281915905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98990678638018507418442413 37121504489256940281915905)
  ·
    refine ⟨27841128366942705211436929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37121504489256940281915905 27841128366942705211436929)
    ·
      refine ⟨20880846275207028908577697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27841128366942705211436929 20880846275207028908577697)
      ·
        refine ⟨15660634706405271681433273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20880846275207028908577697 15660634706405271681433273)
        ·
          refine ⟨11745476029803953761074955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15660634706405271681433273 11745476029803953761074955)
          ·
            refine ⟨17618214044705930641612433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11745476029803953761074955 17618214044705930641612433)
            ·
              refine ⟨13213660533529447981209325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17618214044705930641612433 13213660533529447981209325)
              ·
                refine ⟨4955122700073542992953497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13213660533529447981209325 4955122700073542992953497)
                ·
                  refine ⟨3716342025055157244715123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955122700073542992953497 3716342025055157244715123)
                  ·
                    refine ⟨5574513037582735867072685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3716342025055157244715123 5574513037582735867072685)
                    ·
                      refine ⟨2090442389093525950152257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574513037582735867072685 2090442389093525950152257)
                      ·
                        rfl

theorem cell23_4071122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4071122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071122 prefixEnd_4071122 := by exact prefixLift 4071122
  have htrace : WordTrace (prefixWord ++ tailWord_4071122) baseStart_4071122 baseEnd_4071122 := by
    simpa [prefixWord, tailWord_4071122, baseEnd_4071122] using wordTrace_append hprefix tailTrace_4071122
  have hstable : (prefixWord ++ tailWord_4071122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071122).length < 2 ^ (prefixWord ++ tailWord_4071122).sum := by decide
  have hdescent : baseEnd_4071122 < baseStart_4071122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071145 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 4, 2, 2]
def baseStart_4071145 : Nat := 118140960795 + 4071145 * 2 ^ 59
def prefixEnd_4071145 : Nat := 4983230072969 + 3 ^ 40 * 4071145 * 2
def baseEnd_4071145 : Nat := 2090454199148579360164651

theorem tailTrace_4071145 : CollatzResearch.WordTrace tailWord_4071145 prefixEnd_4071145 2090454199148579360164651 := by
  unfold tailWord_4071145
  simp only [CollatzResearch.WordTrace]
  refine ⟨148486856835944436055750889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98991237890629624037167259 148486856835944436055750889)
  ·
    refine ⟨111365142626958327041813167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148486856835944436055750889 111365142626958327041813167)
    ·
      refine ⟨167047713940437490562719751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111365142626958327041813167 167047713940437490562719751)
      ·
        refine ⟨250571570910656235844079627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167047713940437490562719751 250571570910656235844079627)
        ·
          refine ⟨375857356365984353766119441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250571570910656235844079627 375857356365984353766119441)
          ·
            refine ⟨281893017274488265324589581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375857356365984353766119441 281893017274488265324589581)
            ·
              refine ⟨105709881477933099496721093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281893017274488265324589581 105709881477933099496721093)
              ·
                refine ⟨19820602777112456155635205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105709881477933099496721093 19820602777112456155635205)
                ·
                  refine ⟨3716363020708585529181601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19820602777112456155635205 3716363020708585529181601)
                  ·
                    refine ⟨2787272265531439146886201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716363020708585529181601 2787272265531439146886201)
                    ·
                      refine ⟨2090454199148579360164651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787272265531439146886201 2090454199148579360164651)
                      ·
                        rfl

theorem cell23_4071145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 2, 2].length) (baseStart_4071145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071145 prefixEnd_4071145 := by exact prefixLift 4071145
  have htrace : WordTrace (prefixWord ++ tailWord_4071145) baseStart_4071145 baseEnd_4071145 := by
    simpa [prefixWord, tailWord_4071145, baseEnd_4071145] using wordTrace_append hprefix tailTrace_4071145
  have hstable : (prefixWord ++ tailWord_4071145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071145).length < 2 ^ (prefixWord ++ tailWord_4071145).sum := by decide
  have hdescent : baseEnd_4071145 < baseStart_4071145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071149 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4071149 : Nat := 118140960795 + 4071149 * 2 ^ 59
def prefixEnd_4071149 : Nat := 4983230072969 + 3 ^ 40 * 4071149 * 2
def baseEnd_4071149 : Nat := 2090456253071197344514633

theorem tailTrace_4071149 : CollatzResearch.WordTrace tailWord_4071149 prefixEnd_4071149 2090456253071197344514633 := by
  unfold tailWord_4071149
  simp only [CollatzResearch.WordTrace]
  refine ⟨148487002727929944738896501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98991335151953296492597667 148487002727929944738896501)
  ·
    refine ⟨13920656505743432319271547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148487002727929944738896501 13920656505743432319271547)
    ·
      refine ⟨20880984758615148478907321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13920656505743432319271547 20880984758615148478907321)
      ·
        refine ⟨15660738568961361359180491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20880984758615148478907321 15660738568961361359180491)
        ·
          refine ⟨23491107853442042038770737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660738568961361359180491 23491107853442042038770737)
          ·
            refine ⟨17618330890081531529078053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23491107853442042038770737 17618330890081531529078053)
            ·
              refine ⟨3303437041890287161702135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17618330890081531529078053 3303437041890287161702135)
              ·
                refine ⟨4955155562835430742553203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303437041890287161702135 4955155562835430742553203)
                ·
                  refine ⟨7432733344253146113829805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955155562835430742553203 7432733344253146113829805)
                  ·
                    refine ⟨2787275004094929792686177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7432733344253146113829805 2787275004094929792686177)
                    ·
                      refine ⟨2090456253071197344514633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787275004094929792686177 2090456253071197344514633)
                      ·
                        rfl

theorem cell23_4071149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4071149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071149 prefixEnd_4071149 := by exact prefixLift 4071149
  have htrace : WordTrace (prefixWord ++ tailWord_4071149) baseStart_4071149 baseEnd_4071149 := by
    simpa [prefixWord, tailWord_4071149, baseEnd_4071149] using wordTrace_append hprefix tailTrace_4071149
  have hstable : (prefixWord ++ tailWord_4071149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071149).length < 2 ^ (prefixWord ++ tailWord_4071149).sum := by decide
  have hdescent : baseEnd_4071149 < baseStart_4071149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071151 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 9]
def baseStart_4071151 : Nat := 118140960795 + 4071151 * 2 ^ 59
def prefixEnd_4071151 : Nat := 4983230072969 + 3 ^ 40 * 4071151 * 2
def baseEnd_4071151 : Nat := 232273031114722926298847

theorem tailTrace_4071151 : CollatzResearch.WordTrace tailWord_4071151 prefixEnd_4071151 232273031114722926298847 := by
  unfold tailWord_4071151
  simp only [CollatzResearch.WordTrace]
  refine ⟨148487075673922699080469307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98991383782615132720312871 148487075673922699080469307)
  ·
    refine ⟨222730613510884048620703961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148487075673922699080469307 222730613510884048620703961)
    ·
      refine ⟨167047960133163036465527971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222730613510884048620703961 167047960133163036465527971)
      ·
        refine ⟨250571940199744554698291957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167047960133163036465527971 250571940199744554698291957)
        ·
          refine ⟨23491119393726052002964871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250571940199744554698291957 23491119393726052002964871)
          ·
            refine ⟨35236679090589078004447307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23491119393726052002964871 35236679090589078004447307)
            ·
              refine ⟨52855018635883617006670961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35236679090589078004447307 52855018635883617006670961)
              ·
                refine ⟨39641263976912712755003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52855018635883617006670961 39641263976912712755003221)
                ·
                  refine ⟨232273031114722926298847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39641263976912712755003221 232273031114722926298847)
                  ·
                    rfl

theorem cell23_4071151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 9].length) (baseStart_4071151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071151 prefixEnd_4071151 := by exact prefixLift 4071151
  have htrace : WordTrace (prefixWord ++ tailWord_4071151) baseStart_4071151 baseEnd_4071151 := by
    simpa [prefixWord, tailWord_4071151, baseEnd_4071151] using wordTrace_append hprefix tailTrace_4071151
  have hstable : (prefixWord ++ tailWord_4071151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071151).length < 2 ^ (prefixWord ++ tailWord_4071151).sum := by decide
  have hdescent : baseEnd_4071151 < baseStart_4071151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071156 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4071156 : Nat := 118140960795 + 4071156 * 2 ^ 59
def prefixEnd_4071156 : Nat := 4983230072969 + 3 ^ 40 * 4071156 * 2
def baseEnd_4071156 : Nat := 2090459847435778817127101

theorem tailTrace_4071156 : CollatzResearch.WordTrace tailWord_4071156 prefixEnd_4071156 2090459847435778817127101 := by
  unfold tailWord_4071156
  simp only [CollatzResearch.WordTrace]
  refine ⟨74243629019452292467200661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98991505359269723289600881 74243629019452292467200661)
  ·
    refine ⟨3480170110286826209400031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74243629019452292467200661 3480170110286826209400031)
    ·
      refine ⟨5220255165430239314100047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480170110286826209400031 5220255165430239314100047)
      ·
        refine ⟨7830382748145358971150071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220255165430239314100047 7830382748145358971150071)
        ·
          refine ⟨11745574122218038456725107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830382748145358971150071 11745574122218038456725107)
          ·
            refine ⟨17618361183327057685087661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11745574122218038456725107 17618361183327057685087661)
            ·
              refine ⟨6606885443747646631907873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17618361183327057685087661 6606885443747646631907873)
              ·
                refine ⟨4955164082810734973930905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606885443747646631907873 4955164082810734973930905)
                ·
                  refine ⟨3716373062108051230448179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955164082810734973930905 3716373062108051230448179)
                  ·
                    refine ⟨5574559593162076845672269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3716373062108051230448179 5574559593162076845672269)
                    ·
                      refine ⟨2090459847435778817127101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574559593162076845672269 2090459847435778817127101)
                      ·
                        rfl

theorem cell23_4071156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4071156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071156 prefixEnd_4071156 := by exact prefixLift 4071156
  have htrace : WordTrace (prefixWord ++ tailWord_4071156) baseStart_4071156 baseEnd_4071156 := by
    simpa [prefixWord, tailWord_4071156, baseEnd_4071156] using wordTrace_append hprefix tailTrace_4071156
  have hstable : (prefixWord ++ tailWord_4071156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071156).length < 2 ^ (prefixWord ++ tailWord_4071156).sum := by decide
  have hdescent : baseEnd_4071156 < baseStart_4071156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071211 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 8]
def baseStart_4071211 : Nat := 118140960795 + 4071211 * 2 ^ 59
def prefixEnd_4071211 : Nat := 4983230072969 + 3 ^ 40 * 4071211 * 2
def baseEnd_4071211 : Nat := 696829362957258700646449

theorem tailTrace_4071211 : CollatzResearch.WordTrace tailWord_4071211 prefixEnd_4071211 696829362957258700646449 := by
  unfold tailWord_4071211
  simp only [CollatzResearch.WordTrace]
  refine ⟨148489264053705329327653487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98992842702470219551768991 148489264053705329327653487)
  ·
    refine ⟨222733896080557993991480231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148489264053705329327653487 222733896080557993991480231)
    ·
      refine ⟨334100844120836990987220347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222733896080557993991480231 334100844120836990987220347)
      ·
        refine ⟨501151266181255486480830521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334100844120836990987220347 501151266181255486480830521)
        ·
          refine ⟨375863449635941614860622891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501151266181255486480830521 375863449635941614860622891)
          ·
            refine ⟨563795174453912422290934337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375863449635941614860622891 563795174453912422290934337)
            ·
              refine ⟨422846380840434316718200753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563795174453912422290934337 422846380840434316718200753)
              ·
                refine ⟨317134785630325737538650565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422846380840434316718200753 317134785630325737538650565)
                ·
                  refine ⟨59462772305686075788496981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317134785630325737538650565 59462772305686075788496981)
                  ·
                    refine ⟨696829362957258700646449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59462772305686075788496981 696829362957258700646449)
                    ·
                      rfl

theorem cell23_4071211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_4071211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071211 prefixEnd_4071211 := by exact prefixLift 4071211
  have htrace : WordTrace (prefixWord ++ tailWord_4071211) baseStart_4071211 baseEnd_4071211 := by
    simpa [prefixWord, tailWord_4071211, baseEnd_4071211] using wordTrace_append hprefix tailTrace_4071211
  have hstable : (prefixWord ++ tailWord_4071211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071211).length < 2 ^ (prefixWord ++ tailWord_4071211).sum := by decide
  have hdescent : baseEnd_4071211 < baseStart_4071211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071252 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_4071252 : Nat := 118140960795 + 4071252 * 2 ^ 59
def prefixEnd_4071252 : Nat := 4983230072969 + 3 ^ 40 * 4071252 * 2
def baseEnd_4071252 : Nat := 2090509141578610441526659

theorem tailTrace_4071252 : CollatzResearch.WordTrace tailWord_4071252 prefixEnd_4071252 2090509141578610441526659 := by
  unfold tailWord_4071252
  simp only [CollatzResearch.WordTrace]
  refine ⟨74245379723278396664948005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98993839631037862219930673 74245379723278396664948005)
  ·
    refine ⟨13921008698114699374677751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74245379723278396664948005 13921008698114699374677751)
    ·
      refine ⟨20881513047172049062016627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921008698114699374677751 20881513047172049062016627)
      ·
        refine ⟨31322269570758073593024941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20881513047172049062016627 31322269570758073593024941)
        ·
          refine ⟨11745851089034277597384353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31322269570758073593024941 11745851089034277597384353)
          ·
            refine ⟨8809388316775708198038265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11745851089034277597384353 8809388316775708198038265)
            ·
              refine ⟨6607041237581781148528699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8809388316775708198038265 6607041237581781148528699)
              ·
                refine ⟨9910561856372671722793049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607041237581781148528699 9910561856372671722793049)
                ·
                  refine ⟨7432921392279503792094787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9910561856372671722793049 7432921392279503792094787)
                  ·
                    refine ⟨11149382088419255688142181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7432921392279503792094787 11149382088419255688142181)
                    ·
                      refine ⟨2090509141578610441526659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11149382088419255688142181 2090509141578610441526659)
                      ·
                        rfl

theorem cell23_4071252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_4071252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071252 prefixEnd_4071252 := by exact prefixLift 4071252
  have htrace : WordTrace (prefixWord ++ tailWord_4071252) baseStart_4071252 baseEnd_4071252 := by
    simpa [prefixWord, tailWord_4071252, baseEnd_4071252] using wordTrace_append hprefix tailTrace_4071252
  have hstable : (prefixWord ++ tailWord_4071252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071252).length < 2 ^ (prefixWord ++ tailWord_4071252).sum := by decide
  have hdescent : baseEnd_4071252 < baseStart_4071252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071295 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 1, 5, 2]
def baseStart_4071295 : Nat := 118140960795 + 4071295 * 2 ^ 59
def prefixEnd_4071295 : Nat := 4983230072969 + 3 ^ 40 * 4071295 * 2
def baseEnd_4071295 : Nat := 2090531221246753773288961

theorem tailTrace_4071295 : CollatzResearch.WordTrace tailWord_4071295 prefixEnd_4071295 2090531221246753773288961 := by
  unfold tailWord_4071295
  simp only [CollatzResearch.WordTrace]
  refine ⟨148492327785401011673711339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98994885190267341115807559 148492327785401011673711339)
  ·
    refine ⟨222738491678101517510567009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148492327785401011673711339 222738491678101517510567009)
    ·
      refine ⟨167053868758576138132925257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222738491678101517510567009 167053868758576138132925257)
      ·
        refine ⟨125290401568932103599693943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167053868758576138132925257 125290401568932103599693943)
        ·
          refine ⟨187935602353398155399540915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125290401568932103599693943 187935602353398155399540915)
          ·
            refine ⟨281903403530097233099311373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187935602353398155399540915 281903403530097233099311373)
            ·
              refine ⟨105713776323786462412241765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281903403530097233099311373 105713776323786462412241765)
              ·
                refine ⟨19821333060709961702295331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105713776323786462412241765 19821333060709961702295331)
                ·
                  refine ⟨29731999591064942553442997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19821333060709961702295331 29731999591064942553442997)
                  ·
                    refine ⟨2787374961662338364385281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29731999591064942553442997 2787374961662338364385281)
                    ·
                      refine ⟨2090531221246753773288961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787374961662338364385281 2090531221246753773288961)
                      ·
                        rfl

theorem cell23_4071295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_4071295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071295 prefixEnd_4071295 := by exact prefixLift 4071295
  have htrace : WordTrace (prefixWord ++ tailWord_4071295) baseStart_4071295 baseEnd_4071295 := by
    simpa [prefixWord, tailWord_4071295, baseEnd_4071295] using wordTrace_append hprefix tailTrace_4071295
  have hstable : (prefixWord ++ tailWord_4071295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071295).length < 2 ^ (prefixWord ++ tailWord_4071295).sum := by decide
  have hdescent : baseEnd_4071295 < baseStart_4071295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071305 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 1, 5]
def baseStart_4071305 : Nat := 118140960795 + 4071305 * 2 ^ 59
def prefixEnd_4071305 : Nat := 4983230072969 + 3 ^ 40 * 4071305 * 2
def baseEnd_4071305 : Nat := 696845452017766244721305

theorem tailTrace_4071305 : CollatzResearch.WordTrace tailWord_4071305 prefixEnd_4071305 696845452017766244721305 := by
  unfold tailWord_4071305
  simp only [CollatzResearch.WordTrace]
  refine ⟨148492692515364783381575369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98995128343576522254383579 148492692515364783381575369)
  ·
    refine ⟨111369519386523587536181527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148492692515364783381575369 111369519386523587536181527)
    ·
      refine ⟨167054279079785381304272291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111369519386523587536181527 167054279079785381304272291)
      ·
        refine ⟨250581418619678071956408437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167054279079785381304272291 250581418619678071956408437)
        ·
          refine ⟨23492007995594819245913291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250581418619678071956408437 23492007995594819245913291)
          ·
            refine ⟨35238011993392228868869937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23492007995594819245913291 35238011993392228868869937)
            ·
              refine ⟨26428508995044171651652453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35238011993392228868869937 26428508995044171651652453)
              ·
                refine ⟨4955345436570782184684835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26428508995044171651652453 4955345436570782184684835)
                ·
                  refine ⟨7433018154856173277027253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955345436570782184684835 7433018154856173277027253)
                  ·
                    refine ⟨696845452017766244721305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7433018154856173277027253 696845452017766244721305)
                    ·
                      rfl

theorem cell23_4071305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_4071305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071305 prefixEnd_4071305 := by exact prefixLift 4071305
  have htrace : WordTrace (prefixWord ++ tailWord_4071305) baseStart_4071305 baseEnd_4071305 := by
    simpa [prefixWord, tailWord_4071305, baseEnd_4071305] using wordTrace_append hprefix tailTrace_4071305
  have hstable : (prefixWord ++ tailWord_4071305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071305).length < 2 ^ (prefixWord ++ tailWord_4071305).sum := by decide
  have hdescent : baseEnd_4071305 < baseStart_4071305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071306 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4071306 : Nat := 118140960795 + 4071306 * 2 ^ 59
def prefixEnd_4071306 : Nat := 4983230072969 + 3 ^ 40 * 4071306 * 2
def baseEnd_4071306 : Nat := 2090536869533953230251411

theorem tailTrace_4071306 : CollatzResearch.WordTrace tailWord_4071306 prefixEnd_4071306 2090536869533953230251411 := by
  unfold tailWord_4071306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37123182247090290138090443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98995152658907440368241181 37123182247090290138090443)
  ·
    refine ⟨55684773370635435207135665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37123182247090290138090443 55684773370635435207135665)
    ·
      refine ⟨41763580027976576405351749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55684773370635435207135665 41763580027976576405351749)
      ·
        refine ⟨7830671255245608076003453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41763580027976576405351749 7830671255245608076003453)
        ·
          refine ⟨2936501720717103028501295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7830671255245608076003453 2936501720717103028501295)
          ·
            refine ⟨4404752581075654542751943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936501720717103028501295 4404752581075654542751943)
            ·
              refine ⟨6607128871613481814127915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404752581075654542751943 6607128871613481814127915)
              ·
                refine ⟨9910693307420222721191873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607128871613481814127915 9910693307420222721191873)
                ·
                  refine ⟨7433019980565167040893905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9910693307420222721191873 7433019980565167040893905)
                  ·
                    refine ⟨5574764985423875280670429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433019980565167040893905 5574764985423875280670429)
                    ·
                      refine ⟨2090536869533953230251411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574764985423875280670429 2090536869533953230251411)
                      ·
                        rfl

theorem cell23_4071306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4071306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071306 prefixEnd_4071306 := by exact prefixLift 4071306
  have htrace : WordTrace (prefixWord ++ tailWord_4071306) baseStart_4071306 baseEnd_4071306 := by
    simpa [prefixWord, tailWord_4071306, baseEnd_4071306] using wordTrace_append hprefix tailTrace_4071306
  have hstable : (prefixWord ++ tailWord_4071306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071306).length < 2 ^ (prefixWord ++ tailWord_4071306).sum := by decide
  have hdescent : baseEnd_4071306 < baseStart_4071306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071319 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 1, 1, 3]
def baseStart_4071319 : Nat := 118140960795 + 4071319 * 2 ^ 59
def prefixEnd_4071319 : Nat := 4983230072969 + 3 ^ 40 * 4071319 * 2
def baseEnd_4071319 : Nat := 2090543544782461679388851

theorem tailTrace_4071319 : CollatzResearch.WordTrace tailWord_4071319 prefixEnd_4071319 2090543544782461679388851 := by
  unfold tailWord_4071319
  simp only [CollatzResearch.WordTrace]
  refine ⟨148493203137314063772585011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98995468758209375848390007 148493203137314063772585011)
  ·
    refine ⟨222739804705971095658877517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148493203137314063772585011 222739804705971095658877517)
    ·
      refine ⟨83527426764739160872079069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222739804705971095658877517 83527426764739160872079069)
      ·
        refine ⟨31322785036777185327029651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83527426764739160872079069 31322785036777185327029651)
        ·
          refine ⟨46984177555165777990544477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31322785036777185327029651 46984177555165777990544477)
          ·
            refine ⟨17619066583187166746454179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46984177555165777990544477 17619066583187166746454179)
            ·
              refine ⟨26428599874780750119681269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619066583187166746454179 26428599874780750119681269)
              ·
                refine ⟨2477681238260695323720119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26428599874780750119681269 2477681238260695323720119)
                ·
                  refine ⟨3716521857391042985580179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477681238260695323720119 3716521857391042985580179)
                  ·
                    refine ⟨5574782786086564478370269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3716521857391042985580179 5574782786086564478370269)
                    ·
                      refine ⟨2090543544782461679388851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574782786086564478370269 2090543544782461679388851)
                      ·
                        rfl

theorem cell23_4071319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_4071319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071319 prefixEnd_4071319 := by exact prefixLift 4071319
  have htrace : WordTrace (prefixWord ++ tailWord_4071319) baseStart_4071319 baseEnd_4071319 := by
    simpa [prefixWord, tailWord_4071319, baseEnd_4071319] using wordTrace_append hprefix tailTrace_4071319
  have hstable : (prefixWord ++ tailWord_4071319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071319).length < 2 ^ (prefixWord ++ tailWord_4071319).sum := by decide
  have hdescent : baseEnd_4071319 < baseStart_4071319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071322 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_4071322 : Nat := 118140960795 + 4071322 * 2 ^ 59
def prefixEnd_4071322 : Nat := 4983230072969 + 3 ^ 40 * 4071322 * 2
def baseEnd_4071322 : Nat := 696848361741475055883779

theorem tailTrace_4071322 : CollatzResearch.WordTrace tailWord_4071322 prefixEnd_4071322 696848361741475055883779 := by
  unfold tailWord_4071322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37123328139075798821236055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98995541704202130189962813 37123328139075798821236055)
  ·
    refine ⟨55684992208613698231854083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37123328139075798821236055 55684992208613698231854083)
    ·
      refine ⟨83527488312920547347781125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55684992208613698231854083 83527488312920547347781125)
      ·
        refine ⟨15661404058672602627708961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83527488312920547347781125 15661404058672602627708961)
        ·
          refine ⟨11746053044004451970781721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15661404058672602627708961 11746053044004451970781721)
          ·
            refine ⟨8809539783003338978086291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11746053044004451970781721 8809539783003338978086291)
            ·
              refine ⟨13214309674505008467129437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809539783003338978086291 13214309674505008467129437)
              ·
                refine ⟨4955366127939378175173539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13214309674505008467129437 4955366127939378175173539)
                ·
                  refine ⟨7433049191909067262760309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955366127939378175173539 7433049191909067262760309)
                  ·
                    refine ⟨696848361741475055883779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7433049191909067262760309 696848361741475055883779)
                    ·
                      rfl

theorem cell23_4071322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_4071322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071322 prefixEnd_4071322 := by exact prefixLift 4071322
  have htrace : WordTrace (prefixWord ++ tailWord_4071322) baseStart_4071322 baseEnd_4071322 := by
    simpa [prefixWord, tailWord_4071322, baseEnd_4071322] using wordTrace_append hprefix tailTrace_4071322
  have hstable : (prefixWord ++ tailWord_4071322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071322).length < 2 ^ (prefixWord ++ tailWord_4071322).sum := by decide
  have hdescent : baseEnd_4071322 < baseStart_4071322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071326 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_4071326 : Nat := 118140960795 + 4071326 * 2 ^ 59
def prefixEnd_4071326 : Nat := 4983230072969 + 3 ^ 40 * 4071326 * 2
def baseEnd_4071326 : Nat := 232283015460782572444591

theorem tailTrace_4071326 : CollatzResearch.WordTrace tailWord_4071326 prefixEnd_4071326 232283015460782572444591 := by
  unfold tailWord_4071326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18561682306036087996011229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98995638965525802645393221 18561682306036087996011229)
  ·
    refine ⟨6960630864763532998504211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18561682306036087996011229 6960630864763532998504211)
    ·
      refine ⟨10440946297145299497756317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6960630864763532998504211 10440946297145299497756317)
      ·
        refine ⟨3915354861429487311658619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10440946297145299497756317 3915354861429487311658619)
        ·
          refine ⟨5873032292144230967487929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915354861429487311658619 5873032292144230967487929)
          ·
            refine ⟨4404774219108173225615947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5873032292144230967487929 4404774219108173225615947)
            ·
              refine ⟨6607161328662259838423921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404774219108173225615947 6607161328662259838423921)
              ·
                refine ⟨4955370996496694878817941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607161328662259838423921 4955370996496694878817941)
                ·
                  refine ⟨232283015460782572444591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4955370996496694878817941 232283015460782572444591)
                  ·
                    rfl

theorem cell23_4071326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_4071326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071326 prefixEnd_4071326 := by exact prefixLift 4071326
  have htrace : WordTrace (prefixWord ++ tailWord_4071326) baseStart_4071326 baseEnd_4071326 := by
    simpa [prefixWord, tailWord_4071326, baseEnd_4071326] using wordTrace_append hprefix tailTrace_4071326
  have hstable : (prefixWord ++ tailWord_4071326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071326).length < 2 ^ (prefixWord ++ tailWord_4071326).sum := by decide
  have hdescent : baseEnd_4071326 < baseStart_4071326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071345 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4071345 : Nat := 118140960795 + 4071345 * 2 ^ 59
def prefixEnd_4071345 : Nat := 4983230072969 + 3 ^ 40 * 4071345 * 2
def baseEnd_4071345 : Nat := 2090556895279478577663731

theorem tailTrace_4071345 : CollatzResearch.WordTrace tailWord_4071345 prefixEnd_4071345 2090556895279478577663731 := by
  unfold tailWord_4071345
  simp only [CollatzResearch.WordTrace]
  refine ⟨148494151435219870213031489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98996100956813246808687659 148494151435219870213031489)
  ·
    refine ⟨111370613576414902659773617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148494151435219870213031489 111370613576414902659773617)
    ·
      refine ⟨83527960182311176994830213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111370613576414902659773617 83527960182311176994830213)
      ·
        refine ⟨15661492534183345686530665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83527960182311176994830213 15661492534183345686530665)
        ·
          refine ⟨11746119400637509264897999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15661492534183345686530665 11746119400637509264897999)
          ·
            refine ⟨17619179100956263897346999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746119400637509264897999 17619179100956263897346999)
            ·
              refine ⟨26428768651434395846020499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619179100956263897346999 26428768651434395846020499)
              ·
                refine ⟨39643152977151593769030749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26428768651434395846020499 39643152977151593769030749)
                ·
                  refine ⟨14866182366431847663386531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39643152977151593769030749 14866182366431847663386531)
                  ·
                    refine ⟨22299273549647771495079797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14866182366431847663386531 22299273549647771495079797)
                    ·
                      refine ⟨2090556895279478577663731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22299273549647771495079797 2090556895279478577663731)
                      ·
                        rfl

theorem cell23_4071345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4071345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071345 prefixEnd_4071345 := by exact prefixLift 4071345
  have htrace : WordTrace (prefixWord ++ tailWord_4071345) baseStart_4071345 baseEnd_4071345 := by
    simpa [prefixWord, tailWord_4071345, baseEnd_4071345] using wordTrace_append hprefix tailTrace_4071345
  have hstable : (prefixWord ++ tailWord_4071345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071345).length < 2 ^ (prefixWord ++ tailWord_4071345).sum := by decide
  have hdescent : baseEnd_4071345 < baseStart_4071345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071375 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_4071375 : Nat := 118140960795 + 4071375 * 2 ^ 59
def prefixEnd_4071375 : Nat := 4983230072969 + 3 ^ 40 * 4071375 * 2
def baseEnd_4071375 : Nat := 2090572299699113460288593

theorem tailTrace_4071375 : CollatzResearch.WordTrace tailWord_4071375 prefixEnd_4071375 2090572299699113460288593 := by
  unfold tailWord_4071375
  simp only [CollatzResearch.WordTrace]
  refine ⟨148495245625111185336623579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98996830416740790224415719 148495245625111185336623579)
  ·
    refine ⟨222742868437666778004935369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148495245625111185336623579 222742868437666778004935369)
    ·
      refine ⟨167057151328250083503701527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222742868437666778004935369 167057151328250083503701527)
      ·
        refine ⟨250585726992375125255552291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167057151328250083503701527 250585726992375125255552291)
        ·
          refine ⟨375878590488562687883328437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250585726992375125255552291 375878590488562687883328437)
          ·
            refine ⟨35238617858302751989062041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375878590488562687883328437 35238617858302751989062041)
            ·
              refine ⟨26428963393727063991796531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35238617858302751989062041 26428963393727063991796531)
              ·
                refine ⟨39643445090590595987694797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26428963393727063991796531 39643445090590595987694797)
                ·
                  refine ⟨14866291908971473495385549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39643445090590595987694797 14866291908971473495385549)
                  ·
                    refine ⟨5574859465864302560769581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14866291908971473495385549 5574859465864302560769581)
                    ·
                      refine ⟨2090572299699113460288593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574859465864302560769581 2090572299699113460288593)
                      ·
                        rfl

theorem cell23_4071375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_4071375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071375 prefixEnd_4071375 := by exact prefixLift 4071375
  have htrace : WordTrace (prefixWord ++ tailWord_4071375) baseStart_4071375 baseEnd_4071375 := by
    simpa [prefixWord, tailWord_4071375, baseEnd_4071375] using wordTrace_append hprefix tailTrace_4071375
  have hstable : (prefixWord ++ tailWord_4071375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071375).length < 2 ^ (prefixWord ++ tailWord_4071375).sum := by decide
  have hdescent : baseEnd_4071375 < baseStart_4071375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071376 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 1, 2, 2]
def baseStart_4071376 : Nat := 118140960795 + 4071376 * 2 ^ 59
def prefixEnd_4071376 : Nat := 4983230072969 + 3 ^ 40 * 4071376 * 2
def baseEnd_4071376 : Nat := 2090572813179767956376089

theorem tailTrace_4071376 : CollatzResearch.WordTrace tailWord_4071376 prefixEnd_4071376 2090572813179767956376089 := by
  unfold tailWord_4071376
  simp only [CollatzResearch.WordTrace]
  refine ⟨74247641049053781253704991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98996854732071708338273321 74247641049053781253704991)
  ·
    refine ⟨111371461573580671880557487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74247641049053781253704991 111371461573580671880557487)
    ·
      refine ⟨167057192360371007820836231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111371461573580671880557487 167057192360371007820836231)
      ·
        refine ⟨250585788540556511731254347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167057192360371007820836231 250585788540556511731254347)
        ·
          refine ⟨375878682810834767596881521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250585788540556511731254347 375878682810834767596881521)
          ·
            refine ⟨281909012108126075697661141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375878682810834767596881521 281909012108126075697661141)
            ·
              refine ⟨6607242471284204899163933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281909012108126075697661141 6607242471284204899163933)
              ·
                refine ⟨2477715926731576837186475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6607242471284204899163933 2477715926731576837186475)
                ·
                  refine ⟨3716573890097365255779713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477715926731576837186475 3716573890097365255779713)
                  ·
                    refine ⟨2787430417573023941834785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716573890097365255779713 2787430417573023941834785)
                    ·
                      refine ⟨2090572813179767956376089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787430417573023941834785 2090572813179767956376089)
                      ·
                        rfl

theorem cell23_4071376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 2, 2].length) (baseStart_4071376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071376 prefixEnd_4071376 := by exact prefixLift 4071376
  have htrace : WordTrace (prefixWord ++ tailWord_4071376) baseStart_4071376 baseEnd_4071376 := by
    simpa [prefixWord, tailWord_4071376, baseEnd_4071376] using wordTrace_append hprefix tailTrace_4071376
  have hstable : (prefixWord ++ tailWord_4071376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071376).length < 2 ^ (prefixWord ++ tailWord_4071376).sum := by decide
  have hdescent : baseEnd_4071376 < baseStart_4071376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071419 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 1, 3, 2]
def baseStart_4071419 : Nat := 118140960795 + 4071419 * 2 ^ 59
def prefixEnd_4071419 : Nat := 4983230072969 + 3 ^ 40 * 4071419 * 2
def baseEnd_4071419 : Nat := 2090594892847911288138391

theorem tailTrace_4071419 : CollatzResearch.WordTrace tailWord_4071419 prefixEnd_4071419 2090594892847911288138391 := by
  unfold tailWord_4071419
  simp only [CollatzResearch.WordTrace]
  refine ⟨148496850436951780851225311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98997900291301187234150207 148496850436951780851225311)
  ·
    refine ⟨222745275655427671276837967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148496850436951780851225311 222745275655427671276837967)
    ·
      refine ⟨334117913483141506915256951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222745275655427671276837967 334117913483141506915256951)
      ·
        refine ⟨501176870224712260372885427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334117913483141506915256951 501176870224712260372885427)
        ·
          refine ⟨751765305337068390559328141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501176870224712260372885427 751765305337068390559328141)
          ·
            refine ⟨281911989501400646459748053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751765305337068390559328141 281911989501400646459748053)
            ·
              refine ⟨6607312253939077651400345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281911989501400646459748053 6607312253939077651400345)
              ·
                refine ⟨4955484190454308238550259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607312253939077651400345 4955484190454308238550259)
                ·
                  refine ⟨7433226285681462357825389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955484190454308238550259 7433226285681462357825389)
                  ·
                    refine ⟨2787459857130548384184521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7433226285681462357825389 2787459857130548384184521)
                    ·
                      refine ⟨2090594892847911288138391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787459857130548384184521 2090594892847911288138391)
                      ·
                        rfl

theorem cell23_4071419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 3, 2].length) (baseStart_4071419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071419 prefixEnd_4071419 := by exact prefixLift 4071419
  have htrace : WordTrace (prefixWord ++ tailWord_4071419) baseStart_4071419 baseEnd_4071419 := by
    simpa [prefixWord, tailWord_4071419, baseEnd_4071419] using wordTrace_append hprefix tailTrace_4071419
  have hstable : (prefixWord ++ tailWord_4071419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071419).length < 2 ^ (prefixWord ++ tailWord_4071419).sum := by decide
  have hdescent : baseEnd_4071419 < baseStart_4071419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071430 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4071430 : Nat := 118140960795 + 4071430 * 2 ^ 59
def prefixEnd_4071430 : Nat := 4983230072969 + 3 ^ 40 * 4071430 * 2
def baseEnd_4071430 : Nat := 2090600541135110745100841

theorem tailTrace_4071430 : CollatzResearch.WordTrace tailWord_4071430 prefixEnd_4071430 2090600541135110745100841 := by
  unfold tailWord_4071430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640539113747247804058617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98998167759941286486583829 4640539113747247804058617)
  ·
    refine ⟨3480404335310435853043963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4640539113747247804058617 3480404335310435853043963)
    ·
      refine ⟨5220606502965653779565945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480404335310435853043963 5220606502965653779565945)
      ·
        refine ⟨3915454877224240334674459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5220606502965653779565945 3915454877224240334674459)
        ·
          refine ⟨5873182315836360502011689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915454877224240334674459 5873182315836360502011689)
          ·
            refine ⟨4404886736877270376508767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5873182315836360502011689 4404886736877270376508767)
            ·
              refine ⟨6607330105315905564763151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404886736877270376508767 6607330105315905564763151)
              ·
                refine ⟨9910995157973858347144727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607330105315905564763151 9910995157973858347144727)
                ·
                  refine ⟨14866492736960787520717091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910995157973858347144727 14866492736960787520717091)
                  ·
                    refine ⟨22299739105441181281075637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14866492736960787520717091 22299739105441181281075637)
                    ·
                      refine ⟨2090600541135110745100841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22299739105441181281075637 2090600541135110745100841)
                      ·
                        rfl

theorem cell23_4071430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4071430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071430 prefixEnd_4071430 := by exact prefixLift 4071430
  have htrace : WordTrace (prefixWord ++ tailWord_4071430) baseStart_4071430 baseEnd_4071430 := by
    simpa [prefixWord, tailWord_4071430, baseEnd_4071430] using wordTrace_append hprefix tailTrace_4071430
  have hstable : (prefixWord ++ tailWord_4071430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071430).length < 2 ^ (prefixWord ++ tailWord_4071430).sum := by decide
  have hdescent : baseEnd_4071430 < baseStart_4071430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071435 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5]
def baseStart_4071435 : Nat := 118140960795 + 4071435 * 2 ^ 59
def prefixEnd_4071435 : Nat := 4983230072969 + 3 ^ 40 * 4071435 * 2
def baseEnd_4071435 : Nat := 2090603108538383225538317

theorem tailTrace_4071435 : CollatzResearch.WordTrace tailWord_4071435 prefixEnd_4071435 2090603108538383225538317 := by
  unfold tailWord_4071435
  simp only [CollatzResearch.WordTrace]
  refine ⟨148497434004893815583807759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98998289336595877055871839 148497434004893815583807759)
  ·
    refine ⟨222746151007340723375711639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148497434004893815583807759 222746151007340723375711639)
    ·
      refine ⟨334119226511011085063567459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222746151007340723375711639 334119226511011085063567459)
      ·
        refine ⟨501178839766516627595351189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334119226511011085063567459 501178839766516627595351189)
        ·
          refine ⟨23492758114055466918532087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501178839766516627595351189 23492758114055466918532087)
          ·
            refine ⟨35239137171083200377798131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23492758114055466918532087 35239137171083200377798131)
            ·
              refine ⟨52858705756624800566697197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35239137171083200377798131 52858705756624800566697197)
              ·
                refine ⟨19822014658734300212511449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52858705756624800566697197 19822014658734300212511449)
                ·
                  refine ⟨14866510994050725159383587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19822014658734300212511449 14866510994050725159383587)
                  ·
                    refine ⟨22299766491076087739075381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14866510994050725159383587 22299766491076087739075381)
                    ·
                      refine ⟨2090603108538383225538317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22299766491076087739075381 2090603108538383225538317)
                      ·
                        rfl

theorem cell23_4071435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_4071435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071435 prefixEnd_4071435 := by exact prefixLift 4071435
  have htrace : WordTrace (prefixWord ++ tailWord_4071435) baseStart_4071435 baseEnd_4071435 := by
    simpa [prefixWord, tailWord_4071435, baseEnd_4071435] using wordTrace_append hprefix tailTrace_4071435
  have hstable : (prefixWord ++ tailWord_4071435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071435).length < 2 ^ (prefixWord ++ tailWord_4071435).sum := by decide
  have hdescent : baseEnd_4071435 < baseStart_4071435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071436 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 1, 3, 2]
def baseStart_4071436 : Nat := 118140960795 + 4071436 * 2 ^ 59
def prefixEnd_4071436 : Nat := 4983230072969 + 3 ^ 40 * 4071436 * 2
def baseEnd_4071436 : Nat := 2090603622019037721625813

theorem tailTrace_4071436 : CollatzResearch.WordTrace tailWord_4071436 prefixEnd_4071436 2090603622019037721625813 := by
  unfold tailWord_4071436
  simp only [CollatzResearch.WordTrace]
  refine ⟨74248735238945096377297081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98998313651926795169729441 74248735238945096377297081)
  ·
    refine ⟨55686551429208822282972811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74248735238945096377297081 55686551429208822282972811)
    ·
      refine ⟨83529827143813233424459217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55686551429208822282972811 83529827143813233424459217)
      ·
        refine ⟨62647370357859925068344413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83529827143813233424459217 62647370357859925068344413)
        ·
          refine ⟨23492763884197471900629155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62647370357859925068344413 23492763884197471900629155)
          ·
            refine ⟨35239145826296207850943733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23492763884197471900629155 35239145826296207850943733)
            ·
              refine ⟨3303669921215269486025975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35239145826296207850943733 3303669921215269486025975)
              ·
                refine ⟨4955504881822904229038963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303669921215269486025975 4955504881822904229038963)
                ·
                  refine ⟨7433257322734356343558445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955504881822904229038963 7433257322734356343558445)
                  ·
                    refine ⟨2787471496025383628834417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7433257322734356343558445 2787471496025383628834417)
                    ·
                      refine ⟨2090603622019037721625813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787471496025383628834417 2090603622019037721625813)
                      ·
                        rfl

theorem cell23_4071436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_4071436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071436 prefixEnd_4071436 := by exact prefixLift 4071436
  have htrace : WordTrace (prefixWord ++ tailWord_4071436) baseStart_4071436 baseEnd_4071436 := by
    simpa [prefixWord, tailWord_4071436, baseEnd_4071436] using wordTrace_append hprefix tailTrace_4071436
  have hstable : (prefixWord ++ tailWord_4071436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071436).length < 2 ^ (prefixWord ++ tailWord_4071436).sum := by decide
  have hdescent : baseEnd_4071436 < baseStart_4071436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071444 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4071444 : Nat := 118140960795 + 4071444 * 2 ^ 59
def prefixEnd_4071444 : Nat := 4983230072969 + 3 ^ 40 * 4071444 * 2
def baseEnd_4071444 : Nat := 2090607729864273690325777

theorem tailTrace_4071444 : CollatzResearch.WordTrace tailWord_4071444 prefixEnd_4071444 2090607729864273690325777 := by
  unfold tailWord_4071444
  simp only [CollatzResearch.WordTrace]
  refine ⟨74248881130930605060442693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98998508174574140080590257 74248881130930605060442693)
  ·
    refine ⟨13921665212049488448833005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74248881130930605060442693 13921665212049488448833005)
    ·
      refine ⟨5220624454518558168312377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13921665212049488448833005 5220624454518558168312377)
      ·
        refine ⟨3915468340888918626234283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5220624454518558168312377 3915468340888918626234283)
        ·
          refine ⟨5873202511333377939351425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915468340888918626234283 5873202511333377939351425)
          ·
            refine ⟨4404901883500033454513569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5873202511333377939351425 4404901883500033454513569)
            ·
              refine ⟨3303676412625025090885177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404901883500033454513569 3303676412625025090885177)
              ·
                refine ⟨2477757309468768818163883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303676412625025090885177 2477757309468768818163883)
                ·
                  refine ⟨3716635964203153227245825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477757309468768818163883 3716635964203153227245825)
                  ·
                    refine ⟨2787476973152364920434369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716635964203153227245825 2787476973152364920434369)
                    ·
                      refine ⟨2090607729864273690325777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787476973152364920434369 2090607729864273690325777)
                      ·
                        rfl

theorem cell23_4071444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4071444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071444 prefixEnd_4071444 := by exact prefixLift 4071444
  have htrace : WordTrace (prefixWord ++ tailWord_4071444) baseStart_4071444 baseEnd_4071444 := by
    simpa [prefixWord, tailWord_4071444, baseEnd_4071444] using wordTrace_append hprefix tailTrace_4071444
  have hstable : (prefixWord ++ tailWord_4071444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071444).length < 2 ^ (prefixWord ++ tailWord_4071444).sum := by decide
  have hdescent : baseEnd_4071444 < baseStart_4071444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071452 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_4071452 : Nat := 118140960795 + 4071452 * 2 ^ 59
def prefixEnd_4071452 : Nat := 4983230072969 + 3 ^ 40 * 4071452 * 2
def baseEnd_4071452 : Nat := 2090611837709509659025739

theorem tailTrace_4071452 : CollatzResearch.WordTrace tailWord_4071452 prefixEnd_4071452 2090611837709509659025739 := by
  unfold tailWord_4071452
  simp only [CollatzResearch.WordTrace]
  refine ⟨74249027022916113743588305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98998702697221484991451073 74249027022916113743588305)
  ·
    refine ⟨55686770267187085307691229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74249027022916113743588305 55686770267187085307691229)
    ·
      refine ⟨20882538850195156990384211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55686770267187085307691229 20882538850195156990384211)
      ·
        refine ⟨31323808275292735485576317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20882538850195156990384211 31323808275292735485576317)
        ·
          refine ⟨11746428103234775807091119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31323808275292735485576317 11746428103234775807091119)
          ·
            refine ⟨17619642154852163710636679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746428103234775807091119 17619642154852163710636679)
            ·
              refine ⟨26429463232278245565955019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619642154852163710636679 26429463232278245565955019)
              ·
                refine ⟨39644194848417368348932529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26429463232278245565955019 39644194848417368348932529)
                ·
                  refine ⟨29733146136313026261699397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39644194848417368348932529 29733146136313026261699397)
                  ·
                    refine ⟨5574964900558692424068637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29733146136313026261699397 5574964900558692424068637)
                    ·
                      refine ⟨2090611837709509659025739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5574964900558692424068637 2090611837709509659025739)
                      ·
                        rfl

theorem cell23_4071452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_4071452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071452 prefixEnd_4071452 := by exact prefixLift 4071452
  have htrace : WordTrace (prefixWord ++ tailWord_4071452) baseStart_4071452 baseEnd_4071452 := by
    simpa [prefixWord, tailWord_4071452, baseEnd_4071452] using wordTrace_append hprefix tailTrace_4071452
  have hstable : (prefixWord ++ tailWord_4071452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071452).length < 2 ^ (prefixWord ++ tailWord_4071452).sum := by decide
  have hdescent : baseEnd_4071452 < baseStart_4071452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071455 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 7]
def baseStart_4071455 : Nat := 118140960795 + 4071455 * 2 ^ 59
def prefixEnd_4071455 : Nat := 4983230072969 + 3 ^ 40 * 4071455 * 2
def baseEnd_4071455 : Nat := 232290375350163683032025

theorem tailTrace_4071455 : CollatzResearch.WordTrace tailWord_4071455 prefixEnd_4071455 232290375350163683032025 := by
  unfold tailWord_4071455
  simp only [CollatzResearch.WordTrace]
  refine ⟨148498163464821358999535819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98998775643214239333023879 148498163464821358999535819)
  ·
    refine ⟨222747245197232038499303729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148498163464821358999535819 222747245197232038499303729)
    ·
      refine ⟨167060433897924028874477797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222747245197232038499303729 167060433897924028874477797)
      ·
        refine ⟨31323831355860755413964587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167060433897924028874477797 31323831355860755413964587)
        ·
          refine ⟨46985747033791133120946881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31323831355860755413964587 46985747033791133120946881)
          ·
            refine ⟨35239310275343349840710161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46985747033791133120946881 35239310275343349840710161)
            ·
              refine ⟨26429482706507512380532621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35239310275343349840710161 26429482706507512380532621)
              ·
                refine ⟨9911056014940317142699733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26429482706507512380532621 9911056014940317142699733)
                ·
                  refine ⟨232290375350163683032025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9911056014940317142699733 232290375350163683032025)
                  ·
                    rfl

theorem cell23_4071455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 7].length) (baseStart_4071455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071455 prefixEnd_4071455 := by exact prefixLift 4071455
  have htrace : WordTrace (prefixWord ++ tailWord_4071455) baseStart_4071455 baseEnd_4071455 := by
    simpa [prefixWord, tailWord_4071455, baseEnd_4071455] using wordTrace_append hprefix tailTrace_4071455
  have hstable : (prefixWord ++ tailWord_4071455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071455).length < 2 ^ (prefixWord ++ tailWord_4071455).sum := by decide
  have hdescent : baseEnd_4071455 < baseStart_4071455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071466 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_4071466 : Nat := 118140960795 + 4071466 * 2 ^ 59
def prefixEnd_4071466 : Nat := 4983230072969 + 3 ^ 40 * 4071466 * 2
def baseEnd_4071466 : Nat := 2090619026438672604250675

theorem tailTrace_4071466 : CollatzResearch.WordTrace tailWord_4071466 prefixEnd_4071466 2090619026438672604250675 := by
  unfold tailWord_4071466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124641166945376969546563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98999043111854338585457501 37124641166945376969546563)
  ·
    refine ⟨55686961750418065454319845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37124641166945376969546563 55686961750418065454319845)
    ·
      refine ⟨10441305328203387272684971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55686961750418065454319845 10441305328203387272684971)
      ·
        refine ⟨15661957992305080909027457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10441305328203387272684971 15661957992305080909027457)
        ·
          refine ⟨11746468494228810681770593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15661957992305080909027457 11746468494228810681770593)
          ·
            refine ⟨8809851370671608011327945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11746468494228810681770593 8809851370671608011327945)
            ·
              refine ⟨6607388528003706008495959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8809851370671608011327945 6607388528003706008495959)
              ·
                refine ⟨9911082792005559012743939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607388528003706008495959 9911082792005559012743939)
                ·
                  refine ⟨14866624188008338519115909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9911082792005559012743939 14866624188008338519115909)
                  ·
                    refine ⟨2787492035251563472334233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14866624188008338519115909 2787492035251563472334233)
                    ·
                      refine ⟨2090619026438672604250675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787492035251563472334233 2090619026438672604250675)
                      ·
                        rfl

theorem cell23_4071466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_4071466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071466 prefixEnd_4071466 := by exact prefixLift 4071466
  have htrace : WordTrace (prefixWord ++ tailWord_4071466) baseStart_4071466 baseEnd_4071466 := by
    simpa [prefixWord, tailWord_4071466, baseEnd_4071466] using wordTrace_append hprefix tailTrace_4071466
  have hstable : (prefixWord ++ tailWord_4071466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071466).length < 2 ^ (prefixWord ++ tailWord_4071466).sum := by decide
  have hdescent : baseEnd_4071466 < baseStart_4071466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071489 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 5]
def baseStart_4071489 : Nat := 118140960795 + 4071489 * 2 ^ 59
def prefixEnd_4071489 : Nat := 4983230072969 + 3 ^ 40 * 4071489 * 2
def baseEnd_4071489 : Nat := 232292315165969557140341

theorem tailTrace_4071489 : CollatzResearch.WordTrace tailWord_4071489 prefixEnd_4071489 232292315165969557140341 := by
  unfold tailWord_4071489
  simp only [CollatzResearch.WordTrace]
  refine ⟨148499403546698182806273521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98999602364465455204182347 148499403546698182806273521)
  ·
    refine ⟨111374552660023637104705141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148499403546698182806273521 111374552660023637104705141)
    ·
      refine ⟨10441364311877215978566107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111374552660023637104705141 10441364311877215978566107)
      ·
        refine ⟨15662046467815823967849161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10441364311877215978566107 15662046467815823967849161)
        ·
          refine ⟨11746534850861867975886871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15662046467815823967849161 11746534850861867975886871)
          ·
            refine ⟨17619802276292801963830307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746534850861867975886871 17619802276292801963830307)
            ·
              refine ⟨26429703414439202945745461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619802276292801963830307 26429703414439202945745461)
              ·
                refine ⟨2477784695103675276163637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26429703414439202945745461 2477784695103675276163637)
                ·
                  refine ⟨232292315165969557140341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2477784695103675276163637 232292315165969557140341)
                  ·
                    rfl

theorem cell23_4071489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 5].length) (baseStart_4071489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071489 prefixEnd_4071489 := by exact prefixLift 4071489
  have htrace : WordTrace (prefixWord ++ tailWord_4071489) baseStart_4071489 baseEnd_4071489 := by
    simpa [prefixWord, tailWord_4071489, baseEnd_4071489] using wordTrace_append hprefix tailTrace_4071489
  have hstable : (prefixWord ++ tailWord_4071489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071489).length < 2 ^ (prefixWord ++ tailWord_4071489).sum := by decide
  have hdescent : baseEnd_4071489 < baseStart_4071489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071562 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_4071562 : Nat := 118140960795 + 4071562 * 2 ^ 59
def prefixEnd_4071562 : Nat := 4983230072969 + 3 ^ 40 * 4071562 * 2
def baseEnd_4071562 : Nat := 232296480064611580961137

theorem tailTrace_4071562 : CollatzResearch.WordTrace tailWord_4071562 prefixEnd_4071562 232296480064611580961137 := by
  unfold tailWord_4071562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37125516518858429068420235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99001377383622477515787293 37125516518858429068420235)
  ·
    refine ⟨55688274778287643602630353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37125516518858429068420235 55688274778287643602630353)
    ·
      refine ⟨41766206083715732701972765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55688274778287643602630353 41766206083715732701972765)
      ·
        refine ⟨15662327281393399763239787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41766206083715732701972765 15662327281393399763239787)
        ·
          refine ⟨23493490922090099644859681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15662327281393399763239787 23493490922090099644859681)
          ·
            refine ⟨17620118191567574733644761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23493490922090099644859681 17620118191567574733644761)
            ·
              refine ⟨13215088643675681050233571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17620118191567574733644761 13215088643675681050233571)
              ·
                refine ⟨19822632965513521575350357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215088643675681050233571 19822632965513521575350357)
                ·
                  refine ⟨232296480064611580961137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19822632965513521575350357 232296480064611580961137)
                  ·
                    rfl

theorem cell23_4071562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_4071562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071562 prefixEnd_4071562 := by exact prefixLift 4071562
  have htrace : WordTrace (prefixWord ++ tailWord_4071562) baseStart_4071562 baseEnd_4071562 := by
    simpa [prefixWord, tailWord_4071562, baseEnd_4071562] using wordTrace_append hprefix tailTrace_4071562
  have hstable : (prefixWord ++ tailWord_4071562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071562).length < 2 ^ (prefixWord ++ tailWord_4071562).sum := by decide
  have hdescent : baseEnd_4071562 < baseStart_4071562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071589 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_4071589 : Nat := 118140960795 + 4071589 * 2 ^ 59
def prefixEnd_4071589 : Nat := 4983230072969 + 3 ^ 40 * 4071589 * 2
def baseEnd_4071589 : Nat := 2090682184559175623012609

theorem tailTrace_4071589 : CollatzResearch.WordTrace tailWord_4071589 prefixEnd_4071589 2090682184559175623012609 := by
  unfold tailWord_4071589
  simp only [CollatzResearch.WordTrace]
  refine ⟨148503050846335899884913821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99002033897557266589942547 148503050846335899884913821)
  ·
    refine ⟨55688644067375962456842683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148503050846335899884913821 55688644067375962456842683)
    ·
      refine ⟨83532966101063943685264025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55688644067375962456842683 83532966101063943685264025)
      ·
        refine ⟨62649724575797957763948019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83532966101063943685264025 62649724575797957763948019)
        ·
          refine ⟨93974586863696936645922029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62649724575797957763948019 93974586863696936645922029)
          ·
            refine ⟨35240470073886351242220761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93974586863696936645922029 35240470073886351242220761)
            ·
              refine ⟨26430352555414763431665571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35240470073886351242220761 26430352555414763431665571)
              ·
                refine ⟨39645528833122145147498357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26430352555414763431665571 39645528833122145147498357)
                ·
                  refine ⟨3716768328105201107577971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39645528833122145147498357 3716768328105201107577971)
                  ·
                    refine ⟨5575152492157801661366957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3716768328105201107577971 5575152492157801661366957)
                    ·
                      refine ⟨2090682184559175623012609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5575152492157801661366957 2090682184559175623012609)
                      ·
                        rfl

theorem cell23_4071589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_4071589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071589 prefixEnd_4071589 := by exact prefixLift 4071589
  have htrace : WordTrace (prefixWord ++ tailWord_4071589) baseStart_4071589 baseEnd_4071589 := by
    simpa [prefixWord, tailWord_4071589, baseEnd_4071589] using wordTrace_append hprefix tailTrace_4071589
  have hstable : (prefixWord ++ tailWord_4071589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071589).length < 2 ^ (prefixWord ++ tailWord_4071589).sum := by decide
  have hdescent : baseEnd_4071589 < baseStart_4071589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071616 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 2, 3, 2]
def baseStart_4071616 : Nat := 118140960795 + 4071616 * 2 ^ 59
def prefixEnd_4071616 : Nat := 4983230072969 + 3 ^ 40 * 4071616 * 2
def baseEnd_4071616 : Nat := 2090696048536847017374985

theorem tailTrace_4071616 : CollatzResearch.WordTrace tailWord_4071616 prefixEnd_4071616 2090696048536847017374985 := by
  unfold tailWord_4071616
  simp only [CollatzResearch.WordTrace]
  refine ⟨74252017808619041748073351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99002690411492055664097801 74252017808619041748073351)
  ·
    refine ⟨111378026712928562622110027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74252017808619041748073351 111378026712928562622110027)
    ·
      refine ⟨167067040069392843933165041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111378026712928562622110027 167067040069392843933165041)
      ·
        refine ⟨125300280052044632949873781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167067040069392843933165041 125300280052044632949873781)
        ·
          refine ⟨11746901254879184339050667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125300280052044632949873781 11746901254879184339050667)
          ·
            refine ⟨17620351882318776508576001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746901254879184339050667 17620351882318776508576001)
            ·
              refine ⟨13215263911739082381432001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17620351882318776508576001 13215263911739082381432001)
              ·
                refine ⟨9911447933804311786074001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13215263911739082381432001 9911447933804311786074001)
                ·
                  refine ⟨7433585950353233839555501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9911447933804311786074001 7433585950353233839555501)
                  ·
                    refine ⟨2787594731382462689833313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7433585950353233839555501 2787594731382462689833313)
                    ·
                      refine ⟨2090696048536847017374985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787594731382462689833313 2090696048536847017374985)
                      ·
                        rfl

theorem cell23_4071616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_4071616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071616 prefixEnd_4071616 := by exact prefixLift 4071616
  have htrace : WordTrace (prefixWord ++ tailWord_4071616) baseStart_4071616 baseEnd_4071616 := by
    simpa [prefixWord, tailWord_4071616, baseEnd_4071616] using wordTrace_append hprefix tailTrace_4071616
  have hstable : (prefixWord ++ tailWord_4071616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071616).length < 2 ^ (prefixWord ++ tailWord_4071616).sum := by decide
  have hdescent : baseEnd_4071616 < baseStart_4071616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071617 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4071617 : Nat := 118140960795 + 4071617 * 2 ^ 59
def prefixEnd_4071617 : Nat := 4983230072969 + 3 ^ 40 * 4071617 * 2
def baseEnd_4071617 : Nat := 696898854005833837820827

theorem tailTrace_4071617 : CollatzResearch.WordTrace tailWord_4071617 prefixEnd_4071617 696898854005833837820827 := by
  unfold tailWord_4071617
  simp only [CollatzResearch.WordTrace]
  refine ⟨148504072090234460666933105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99002714726822973777955403 148504072090234460666933105)
  ·
    refine ⟨111378054067675845500199829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148504072090234460666933105 111378054067675845500199829)
    ·
      refine ⟨5220846284422305257821867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111378054067675845500199829 5220846284422305257821867)
      ·
        refine ⟨7831269426633457886732801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220846284422305257821867 7831269426633457886732801)
        ·
          refine ⟨5873452069975093415049601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7831269426633457886732801 5873452069975093415049601)
          ·
            refine ⟨4405089052481320061287201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5873452069975093415049601 4405089052481320061287201)
            ·
              refine ⟨3303816789360990045965401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405089052481320061287201 3303816789360990045965401)
              ·
                refine ⟨2477862592020742534474051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303816789360990045965401 2477862592020742534474051)
                ·
                  refine ⟨3716793888031113801711077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477862592020742534474051 3716793888031113801711077)
                  ·
                    refine ⟨696898854005833837820827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716793888031113801711077 696898854005833837820827)
                    ·
                      rfl

theorem cell23_4071617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4071617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071617 prefixEnd_4071617 := by exact prefixLift 4071617
  have htrace : WordTrace (prefixWord ++ tailWord_4071617) baseStart_4071617 baseEnd_4071617 := by
    simpa [prefixWord, tailWord_4071617, baseEnd_4071617] using wordTrace_append hprefix tailTrace_4071617
  have hstable : (prefixWord ++ tailWord_4071617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071617).length < 2 ^ (prefixWord ++ tailWord_4071617).sum := by decide
  have hdescent : baseEnd_4071617 < baseStart_4071617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071642 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_4071642 : Nat := 118140960795 + 4071642 * 2 ^ 59
def prefixEnd_4071642 : Nat := 4983230072969 + 3 ^ 40 * 4071642 * 2
def baseEnd_4071642 : Nat := 2090709399033863915649865

theorem tailTrace_4071642 : CollatzResearch.WordTrace tailWord_4071642 prefixEnd_4071642 2090709399033863915649865 := by
  unfold tailWord_4071642
  simp only [CollatzResearch.WordTrace]
  refine ⟨37126245978785972484148295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99003322610095926624395453 37126245978785972484148295)
  ·
    refine ⟨55689368968178958726222443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37126245978785972484148295 55689368968178958726222443)
    ·
      refine ⟨83534053452268438089333665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55689368968178958726222443 83534053452268438089333665)
      ·
        refine ⟨62650540089201328567000249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83534053452268438089333665 62650540089201328567000249)
        ·
          refine ⟨46987905066900996425250187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62650540089201328567000249 46987905066900996425250187)
          ·
            refine ⟨70481857600351494637875281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46987905066900996425250187 70481857600351494637875281)
            ·
              refine ⟨52861393200263620978406461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70481857600351494637875281 52861393200263620978406461)
              ·
                refine ⟨19823022450098857866902423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52861393200263620978406461 19823022450098857866902423)
                ·
                  refine ⟨29734533675148286800353635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19823022450098857866902423 29734533675148286800353635)
                  ·
                    refine ⟨44601800512722430200530453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29734533675148286800353635 44601800512722430200530453)
                    ·
                      refine ⟨2090709399033863915649865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44601800512722430200530453 2090709399033863915649865)
                      ·
                        rfl

theorem cell23_4071642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_4071642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071642 prefixEnd_4071642 := by exact prefixLift 4071642
  have htrace : WordTrace (prefixWord ++ tailWord_4071642) baseStart_4071642 baseEnd_4071642 := by
    simpa [prefixWord, tailWord_4071642, baseEnd_4071642] using wordTrace_append hprefix tailTrace_4071642
  have hstable : (prefixWord ++ tailWord_4071642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071642).length < 2 ^ (prefixWord ++ tailWord_4071642).sum := by decide
  have hdescent : baseEnd_4071642 < baseStart_4071642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071649 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_4071649 : Nat := 118140960795 + 4071649 * 2 ^ 59
def prefixEnd_4071649 : Nat := 4983230072969 + 3 ^ 40 * 4071649 * 2
def baseEnd_4071649 : Nat := 2090712993398445388262333

theorem tailTrace_4071649 : CollatzResearch.WordTrace tailWord_4071649 prefixEnd_4071649 2090712993398445388262333 := by
  unfold tailWord_4071649
  simp only [CollatzResearch.WordTrace]
  refine ⟨148505239226118530132098001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99003492817412353421398667 148505239226118530132098001)
  ·
    refine ⟨111378929419588897599073501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148505239226118530132098001 111378929419588897599073501)
    ·
      refine ⟨41767098532345836599652563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111378929419588897599073501 41767098532345836599652563)
      ·
        refine ⟨62650647798518754899478845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41767098532345836599652563 62650647798518754899478845)
        ·
          refine ⟨23493992924444533087304567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62650647798518754899478845 23493992924444533087304567)
          ·
            refine ⟨35240989386666799630956851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23493992924444533087304567 35240989386666799630956851)
            ·
              refine ⟨52861484080000199446435277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35240989386666799630956851 52861484080000199446435277)
              ·
                refine ⟨19823056530000074792413229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52861484080000199446435277 19823056530000074792413229)
                ·
                  refine ⟨7433646198750028047154961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19823056530000074792413229 7433646198750028047154961)
                  ·
                    refine ⟨5575234649062521035366221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433646198750028047154961 5575234649062521035366221)
                    ·
                      refine ⟨2090712993398445388262333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5575234649062521035366221 2090712993398445388262333)
                      ·
                        rfl

theorem cell23_4071649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_4071649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071649 prefixEnd_4071649 := by exact prefixLift 4071649
  have htrace : WordTrace (prefixWord ++ tailWord_4071649) baseStart_4071649 baseEnd_4071649 := by
    simpa [prefixWord, tailWord_4071649, baseEnd_4071649] using wordTrace_append hprefix tailTrace_4071649
  have hstable : (prefixWord ++ tailWord_4071649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071649).length < 2 ^ (prefixWord ++ tailWord_4071649).sum := by decide
  have hdescent : baseEnd_4071649 < baseStart_4071649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071663 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 1, 1, 4]
def baseStart_4071663 : Nat := 118140960795 + 4071663 * 2 ^ 59
def prefixEnd_4071663 : Nat := 4983230072969 + 3 ^ 40 * 4071663 * 2
def baseEnd_4071663 : Nat := 2090720182127608333487269

theorem tailTrace_4071663 : CollatzResearch.WordTrace tailWord_4071663 prefixEnd_4071663 2090720182127608333487269 := by
  unfold tailWord_4071663
  simp only [CollatzResearch.WordTrace]
  refine ⟨148505749848067810523107643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99003833232045207015405095 148505749848067810523107643)
  ·
    refine ⟨222758624772101715784661465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148505749848067810523107643 222758624772101715784661465)
    ·
      refine ⟨167068968579076286838496099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222758624772101715784661465 167068968579076286838496099)
      ·
        refine ⟨250603452868614430257744149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167068968579076286838496099 250603452868614430257744149)
        ·
          refine ⟨11747036853216301418331757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250603452868614430257744149 11747036853216301418331757)
          ·
            refine ⟨4405138819956113031874409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11747036853216301418331757 4405138819956113031874409)
            ·
              refine ⟨3303854114967084773905807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405138819956113031874409 3303854114967084773905807)
              ·
                refine ⟨4955781172450627160858711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303854114967084773905807 4955781172450627160858711)
                ·
                  refine ⟨7433671758675940741288067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955781172450627160858711 7433671758675940741288067)
                  ·
                    refine ⟨11150507638013911111932101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7433671758675940741288067 11150507638013911111932101)
                    ·
                      refine ⟨2090720182127608333487269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11150507638013911111932101 2090720182127608333487269)
                      ·
                        rfl

theorem cell23_4071663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 1, 4].length) (baseStart_4071663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071663 prefixEnd_4071663 := by exact prefixLift 4071663
  have htrace : WordTrace (prefixWord ++ tailWord_4071663) baseStart_4071663 baseEnd_4071663 := by
    simpa [prefixWord, tailWord_4071663, baseEnd_4071663] using wordTrace_append hprefix tailTrace_4071663
  have hstable : (prefixWord ++ tailWord_4071663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071663).length < 2 ^ (prefixWord ++ tailWord_4071663).sum := by decide
  have hdescent : baseEnd_4071663 < baseStart_4071663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071769 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_4071769 : Nat := 118140960795 + 4071769 * 2 ^ 59
def prefixEnd_4071769 : Nat := 4983230072969 + 3 ^ 40 * 4071769 * 2
def baseEnd_4071769 : Nat := 2090774611076984918761781

theorem tailTrace_4071769 : CollatzResearch.WordTrace tailWord_4071769 prefixEnd_4071769 2090774611076984918761781 := by
  unfold tailWord_4071769
  simp only [CollatzResearch.WordTrace]
  refine ⟨148509615985683790626466361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99006410657122527084310907 148509615985683790626466361)
  ·
    refine ⟨111382211989262842969849771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148509615985683790626466361 111382211989262842969849771)
    ·
      refine ⟨167073317983894264454774657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111382211989262842969849771 167073317983894264454774657)
      ·
        refine ⟨125304988487920698341080993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167073317983894264454774657 125304988487920698341080993)
        ·
          refine ⟨93978741365940523755810745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125304988487920698341080993 93978741365940523755810745)
          ·
            refine ⟨70484056024455392816858059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93978741365940523755810745 70484056024455392816858059)
            ·
              refine ⟨105726084036683089225287089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70484056024455392816858059 105726084036683089225287089)
              ·
                refine ⟨79294563027512316918965317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105726084036683089225287089 79294563027512316918965317)
                ·
                  refine ⟨14867730567658559422305997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79294563027512316918965317 14867730567658559422305997)
                  ·
                    refine ⟨5575398962871959783364749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14867730567658559422305997 5575398962871959783364749)
                    ·
                      refine ⟨2090774611076984918761781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5575398962871959783364749 2090774611076984918761781)
                      ·
                        rfl

theorem cell23_4071769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_4071769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071769 prefixEnd_4071769 := by exact prefixLift 4071769
  have htrace : WordTrace (prefixWord ++ tailWord_4071769) baseStart_4071769 baseEnd_4071769 := by
    simpa [prefixWord, tailWord_4071769, baseEnd_4071769] using wordTrace_append hprefix tailTrace_4071769
  have hstable : (prefixWord ++ tailWord_4071769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071769).length < 2 ^ (prefixWord ++ tailWord_4071769).sum := by decide
  have hdescent : baseEnd_4071769 < baseStart_4071769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071839 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4071839 : Nat := 118140960795 + 4071839 * 2 ^ 59
def prefixEnd_4071839 : Nat := 4983230072969 + 3 ^ 40 * 4071839 * 2
def baseEnd_4071839 : Nat := 2090810554722799644886459

theorem tailTrace_4071839 : CollatzResearch.WordTrace tailWord_4071839 prefixEnd_4071839 2090810554722799644886459 := by
  unfold tailWord_4071839
  simp only [CollatzResearch.WordTrace]
  refine ⟨148512169095430192581514571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99008112730286795054343047 148512169095430192581514571)
  ·
    refine ⟨222768253643145288872271857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148512169095430192581514571 222768253643145288872271857)
    ·
      refine ⟨167076190232358966654203893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222768253643145288872271857 167076190232358966654203893)
      ·
        refine ⟨15663392834283653123831615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167076190232358966654203893 15663392834283653123831615)
        ·
          refine ⟨23495089251425479685747423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663392834283653123831615 23495089251425479685747423)
          ·
            refine ⟨35242633877138219528621135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23495089251425479685747423 35242633877138219528621135)
            ·
              refine ⟨52863950815707329292931703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35242633877138219528621135 52863950815707329292931703)
              ·
                refine ⟨79295926223560993939397555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52863950815707329292931703 79295926223560993939397555)
                ·
                  refine ⟨118943889335341490909096333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79295926223560993939397555 118943889335341490909096333)
                  ·
                    refine ⟨44603958500753059090911125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118943889335341490909096333 44603958500753059090911125)
                    ·
                      refine ⟨2090810554722799644886459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44603958500753059090911125 2090810554722799644886459)
                      ·
                        rfl

theorem cell23_4071839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4071839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071839 prefixEnd_4071839 := by exact prefixLift 4071839
  have htrace : WordTrace (prefixWord ++ tailWord_4071839) baseStart_4071839 baseEnd_4071839 := by
    simpa [prefixWord, tailWord_4071839, baseEnd_4071839] using wordTrace_append hprefix tailTrace_4071839
  have hstable : (prefixWord ++ tailWord_4071839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071839).length < 2 ^ (prefixWord ++ tailWord_4071839).sum := by decide
  have hdescent : baseEnd_4071839 < baseStart_4071839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071903 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 4, 3, 2]
def baseStart_4071903 : Nat := 118140960795 + 4071903 * 2 ^ 59
def prefixEnd_4071903 : Nat := 4983230072969 + 3 ^ 40 * 4071903 * 2
def baseEnd_4071903 : Nat := 2090843417484687394486165

theorem tailTrace_4071903 : CollatzResearch.WordTrace tailWord_4071903 prefixEnd_4071903 2090843417484687394486165 := by
  unfold tailWord_4071903
  simp only [CollatzResearch.WordTrace]
  refine ⟨148514503367198331511844363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99009668911465554341229575 148514503367198331511844363)
  ·
    refine ⟨222771755050797497267766545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148514503367198331511844363 222771755050797497267766545)
    ·
      refine ⟨167078816288098122950824909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222771755050797497267766545 167078816288098122950824909)
      ·
        refine ⟨62654556108036796106559341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167078816288098122950824909 62654556108036796106559341)
        ·
          refine ⟨23495458540513798539959753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62654556108036796106559341 23495458540513798539959753)
          ·
            refine ⟨17621593905385348904969815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23495458540513798539959753 17621593905385348904969815)
            ·
              refine ⟨26432390858078023357454723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17621593905385348904969815 26432390858078023357454723)
              ·
                refine ⟨39648586287117035036182085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26432390858078023357454723 39648586287117035036182085)
                ·
                  refine ⟨7434109928834444069284141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39648586287117035036182085 7434109928834444069284141)
                  ·
                    refine ⟨2787791223312916525981553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7434109928834444069284141 2787791223312916525981553)
                    ·
                      refine ⟨2090843417484687394486165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787791223312916525981553 2090843417484687394486165)
                      ·
                        rfl

theorem cell23_4071903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_4071903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071903 prefixEnd_4071903 := by exact prefixLift 4071903
  have htrace : WordTrace (prefixWord ++ tailWord_4071903) baseStart_4071903 baseEnd_4071903 := by
    simpa [prefixWord, tailWord_4071903, baseEnd_4071903] using wordTrace_append hprefix tailTrace_4071903
  have hstable : (prefixWord ++ tailWord_4071903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071903).length < 2 ^ (prefixWord ++ tailWord_4071903).sum := by decide
  have hdescent : baseEnd_4071903 < baseStart_4071903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071916 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_4071916 : Nat := 118140960795 + 4071916 * 2 ^ 59
def prefixEnd_4071916 : Nat := 4983230072969 + 3 ^ 40 * 4071916 * 2
def baseEnd_4071916 : Nat := 2090850092733195843623605

theorem tailTrace_4071916 : CollatzResearch.WordTrace tailWord_4071916 prefixEnd_4071916 2090850092733195843623605 := by
  unfold tailWord_4071916
  simp only [CollatzResearch.WordTrace]
  refine ⟨74257488758075617366033801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99009985010767489821378401 74257488758075617366033801)
  ·
    refine ⟨55693116568556713024525351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74257488758075617366033801 55693116568556713024525351)
    ·
      refine ⟨83539674852835069536788027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55693116568556713024525351 83539674852835069536788027)
      ·
        refine ⟨125309512279252604305182041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83539674852835069536788027 125309512279252604305182041)
        ·
          refine ⟨93982134209439453228886531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125309512279252604305182041 93982134209439453228886531)
          ·
            refine ⟨140973201314159179843329797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93982134209439453228886531 140973201314159179843329797)
            ·
              refine ⟨26432475246404846220624337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140973201314159179843329797 26432475246404846220624337)
              ·
                refine ⟨19824356434803634665468253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26432475246404846220624337 19824356434803634665468253)
                ·
                  refine ⟨7434133663051362999550595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19824356434803634665468253 7434133663051362999550595)
                  ·
                    refine ⟨11151200494577044499325893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7434133663051362999550595 11151200494577044499325893)
                    ·
                      refine ⟨2090850092733195843623605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11151200494577044499325893 2090850092733195843623605)
                      ·
                        rfl

theorem cell23_4071916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_4071916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071916 prefixEnd_4071916 := by exact prefixLift 4071916
  have htrace : WordTrace (prefixWord ++ tailWord_4071916) baseStart_4071916 baseEnd_4071916 := by
    simpa [prefixWord, tailWord_4071916, baseEnd_4071916] using wordTrace_append hprefix tailTrace_4071916
  have hstable : (prefixWord ++ tailWord_4071916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071916).length < 2 ^ (prefixWord ++ tailWord_4071916).sum := by decide
  have hdescent : baseEnd_4071916 < baseStart_4071916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071939 : List Nat := [1, 1, 1, 3, 2, 1, 3, 11]
def baseStart_4071939 : Nat := 118140960795 + 4071939 * 2 ^ 59
def prefixEnd_4071939 : Nat := 4983230072969 + 3 ^ 40 * 4071939 * 2
def baseEnd_4071939 : Nat := 77439329732898120505037

theorem tailTrace_4071939 : CollatzResearch.WordTrace tailWord_4071939 prefixEnd_4071939 77439329732898120505037 := by
  unfold tailWord_4071939
  simp only [CollatzResearch.WordTrace]
  refine ⟨148515816395067909660154871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99010544263378606440103247 148515816395067909660154871)
  ·
    refine ⟨222773724592601864490232307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148515816395067909660154871 222773724592601864490232307)
    ·
      refine ⟨334160586888902796735348461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222773724592601864490232307 334160586888902796735348461)
      ·
        refine ⟨125310220083338548775755673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334160586888902796735348461 125310220083338548775755673)
        ·
          refine ⟨93982665062503911581816755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125310220083338548775755673 93982665062503911581816755)
          ·
            refine ⟨140973997593755867372725133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93982665062503911581816755 140973997593755867372725133)
            ·
              refine ⟨52865249097658450264771925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140973997593755867372725133 52865249097658450264771925)
              ·
                refine ⟨77439329732898120505037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 52865249097658450264771925 77439329732898120505037)
                ·
                  rfl

theorem cell23_4071939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 11].length) (baseStart_4071939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071939 prefixEnd_4071939 := by exact prefixLift 4071939
  have htrace : WordTrace (prefixWord ++ tailWord_4071939) baseStart_4071939 baseEnd_4071939 := by
    simpa [prefixWord, tailWord_4071939, baseEnd_4071939] using wordTrace_append hprefix tailTrace_4071939
  have hstable : (prefixWord ++ tailWord_4071939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071939).length < 2 ^ (prefixWord ++ tailWord_4071939).sum := by decide
  have hdescent : baseEnd_4071939 < baseStart_4071939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071943 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 1, 6]
def baseStart_4071943 : Nat := 118140960795 + 4071943 * 2 ^ 59
def prefixEnd_4071943 : Nat := 4983230072969 + 3 ^ 40 * 4071943 * 2
def baseEnd_4071943 : Nat := 696954652236955745995327

theorem tailTrace_4071943 : CollatzResearch.WordTrace tailWord_4071943 prefixEnd_4071943 696954652236955745995327 := by
  unfold tailWord_4071943
  simp only [CollatzResearch.WordTrace]
  refine ⟨148515962287053418343300483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99010641524702278895533655 148515962287053418343300483)
  ·
    refine ⟨222773943430580127514950725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148515962287053418343300483 222773943430580127514950725)
    ·
      refine ⟨41770114393233773909053261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222773943430580127514950725 41770114393233773909053261)
      ·
        refine ⟨15663792897462665215894973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41770114393233773909053261 15663792897462665215894973)
        ·
          refine ⟨5873922336548499455960615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15663792897462665215894973 5873922336548499455960615)
          ·
            refine ⟨8810883504822749183940923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873922336548499455960615 8810883504822749183940923)
            ·
              refine ⟨13216325257234123775911385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810883504822749183940923 13216325257234123775911385)
              ·
                refine ⟨9912243942925592831933539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13216325257234123775911385 9912243942925592831933539)
                ·
                  refine ⟨14868365914388389247900309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912243942925592831933539 14868365914388389247900309)
                  ·
                    refine ⟨696954652236955745995327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14868365914388389247900309 696954652236955745995327)
                    ·
                      rfl

theorem cell23_4071943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_4071943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071943 prefixEnd_4071943 := by exact prefixLift 4071943
  have htrace : WordTrace (prefixWord ++ tailWord_4071943) baseStart_4071943 baseEnd_4071943 := by
    simpa [prefixWord, tailWord_4071943, baseEnd_4071943] using wordTrace_append hprefix tailTrace_4071943
  have hstable : (prefixWord ++ tailWord_4071943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071943).length < 2 ^ (prefixWord ++ tailWord_4071943).sum := by decide
  have hdescent : baseEnd_4071943 < baseStart_4071943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071960 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 2, 4]
def baseStart_4071960 : Nat := 118140960795 + 4071960 * 2 ^ 59
def prefixEnd_4071960 : Nat := 4983230072969 + 3 ^ 40 * 4071960 * 2
def baseEnd_4071960 : Nat := 696957561960664557157801

theorem tailTrace_4071960 : CollatzResearch.WordTrace tailWord_4071960 prefixEnd_4071960 696957561960664557157801 := by
  unfold tailWord_4071960
  simp only [CollatzResearch.WordTrace]
  refine ⟨74258291163995915123334667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99011054885327886831112889 74258291163995915123334667)
  ·
    refine ⟨111387436745993872685002001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74258291163995915123334667 111387436745993872685002001)
    ·
      refine ⟨83540577559495404513751501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111387436745993872685002001 83540577559495404513751501)
      ·
        refine ⟨31327716584810776692656813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83540577559495404513751501 31327716584810776692656813)
        ·
          refine ⟨11747893719304041259746305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31327716584810776692656813 11747893719304041259746305)
          ·
            refine ⟨8810920289478030944809729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11747893719304041259746305 8810920289478030944809729)
            ·
              refine ⟨6608190217108523208607297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8810920289478030944809729 6608190217108523208607297)
              ·
                refine ⟨4956142662831392406455473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6608190217108523208607297 4956142662831392406455473)
                ·
                  refine ⟨3717106997123544304841605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956142662831392406455473 3717106997123544304841605)
                  ·
                    refine ⟨696957561960664557157801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3717106997123544304841605 696957561960664557157801)
                    ·
                      rfl

theorem cell23_4071960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_4071960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071960 prefixEnd_4071960 := by exact prefixLift 4071960
  have htrace : WordTrace (prefixWord ++ tailWord_4071960) baseStart_4071960 baseEnd_4071960 := by
    simpa [prefixWord, tailWord_4071960, baseEnd_4071960] using wordTrace_append hprefix tailTrace_4071960
  have hstable : (prefixWord ++ tailWord_4071960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071960).length < 2 ^ (prefixWord ++ tailWord_4071960).sum := by decide
  have hdescent : baseEnd_4071960 < baseStart_4071960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071990 : List Nat := [5, 1, 2, 1, 2, 2, 3, 7]
def baseStart_4071990 : Nat := 118140960795 + 4071990 * 2 ^ 59
def prefixEnd_4071990 : Nat := 4983230072969 + 3 ^ 40 * 4071990 * 2
def baseEnd_4071990 : Nat := 77440299640801057559195

theorem tailTrace_4071990 : CollatzResearch.WordTrace tailWord_4071990 prefixEnd_4071990 77440299640801057559195 := by
  unfold tailWord_4071990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282354782367696585641339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99011784345255430246840949 9282354782367696585641339)
  ·
    refine ⟨13923532173551544878462009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282354782367696585641339 13923532173551544878462009)
    ·
      refine ⟨10442649130163658658846507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13923532173551544878462009 10442649130163658658846507)
      ·
        refine ⟨15663973695245487988269761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442649130163658658846507 15663973695245487988269761)
        ·
          refine ⟨11747980271434115991202321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15663973695245487988269761 11747980271434115991202321)
          ·
            refine ⟨8810985203575586993401741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11747980271434115991202321 8810985203575586993401741)
            ·
              refine ⟨3304119451340845122525653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8810985203575586993401741 3304119451340845122525653)
              ·
                refine ⟨77440299640801057559195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3304119451340845122525653 77440299640801057559195)
                ·
                  rfl

theorem cell23_4071990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_4071990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4071990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4071990 prefixEnd_4071990 := by exact prefixLift 4071990
  have htrace : WordTrace (prefixWord ++ tailWord_4071990) baseStart_4071990 baseEnd_4071990 := by
    simpa [prefixWord, tailWord_4071990, baseEnd_4071990] using wordTrace_append hprefix tailTrace_4071990
  have hstable : (prefixWord ++ tailWord_4071990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071990).length < 2 ^ (prefixWord ++ tailWord_4071990).sum := by decide
  have hdescent : baseEnd_4071990 < baseStart_4071990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072017 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_4072017 : Nat := 118140960795 + 4072017 * 2 ^ 59
def prefixEnd_4072017 : Nat := 4983230072969 + 3 ^ 40 * 4072017 * 2
def baseEnd_4072017 : Nat := 2090901954279299948460641

theorem tailTrace_4072017 : CollatzResearch.WordTrace tailWord_4072017 prefixEnd_4072017 2090901954279299948460641 := by
  unfold tailWord_4072017
  simp only [CollatzResearch.WordTrace]
  refine ⟨148518661288785328981494305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99012440859190219320996203 148518661288785328981494305)
  ·
    refine ⟨111388995966588996736120729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148518661288785328981494305 111388995966588996736120729)
    ·
      refine ⟨83541746974941747552090547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111388995966588996736120729 83541746974941747552090547)
      ·
        refine ⟨125312620462412621328135821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83541746974941747552090547 125312620462412621328135821)
        ·
          refine ⟨46992232673404732998050933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125312620462412621328135821 46992232673404732998050933)
          ·
            refine ⟨4405521813131693718567275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46992232673404732998050933 4405521813131693718567275)
            ·
              refine ⟨6608282719697540577850913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405521813131693718567275 6608282719697540577850913)
              ·
                refine ⟨4956212039773155433388185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6608282719697540577850913 4956212039773155433388185)
                ·
                  refine ⟨3717159029829866575041139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956212039773155433388185 3717159029829866575041139)
                  ·
                    refine ⟨5575738544744799862561709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3717159029829866575041139 5575738544744799862561709)
                    ·
                      refine ⟨2090901954279299948460641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5575738544744799862561709 2090901954279299948460641)
                      ·
                        rfl

theorem cell23_4072017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_4072017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072017 prefixEnd_4072017 := by exact prefixLift 4072017
  have htrace : WordTrace (prefixWord ++ tailWord_4072017) baseStart_4072017 baseEnd_4072017 := by
    simpa [prefixWord, tailWord_4072017, baseEnd_4072017] using wordTrace_append hprefix tailTrace_4072017
  have hstable : (prefixWord ++ tailWord_4072017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072017).length < 2 ^ (prefixWord ++ tailWord_4072017).sum := by decide
  have hdescent : baseEnd_4072017 < baseStart_4072017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072026 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_4072026 : Nat := 118140960795 + 4072026 * 2 ^ 59
def prefixEnd_4072026 : Nat := 4983230072969 + 3 ^ 40 * 4072026 * 2
def baseEnd_4072026 : Nat := 2090906575605190413248099

theorem tailTrace_4072026 : CollatzResearch.WordTrace tailWord_4072026 prefixEnd_4072026 2090906575605190413248099 := by
  unfold tailWord_4072026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37129747386438180879642983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99012659697168482345714621 37129747386438180879642983)
  ·
    refine ⟨55694621079657271319464475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37129747386438180879642983 55694621079657271319464475)
    ·
      refine ⟨83541931619485906979196713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55694621079657271319464475 83541931619485906979196713)
      ·
        refine ⟨62656448714614430234397535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83541931619485906979196713 62656448714614430234397535)
        ·
          refine ⟨93984673071921645351596303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62656448714614430234397535 93984673071921645351596303)
          ·
            refine ⟨140977009607882468027394455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93984673071921645351596303 140977009607882468027394455)
            ·
              refine ⟨211465514411823702041091683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140977009607882468027394455 211465514411823702041091683)
              ·
                refine ⟨317198271617735553061637525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211465514411823702041091683 317198271617735553061637525)
                ·
                  refine ⟨14868668982081354049764259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317198271617735553061637525 14868668982081354049764259)
                  ·
                    refine ⟨22303003473122031074646389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14868668982081354049764259 22303003473122031074646389)
                    ·
                      refine ⟨2090906575605190413248099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22303003473122031074646389 2090906575605190413248099)
                      ·
                        rfl

theorem cell23_4072026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_4072026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072026 prefixEnd_4072026 := by exact prefixLift 4072026
  have htrace : WordTrace (prefixWord ++ tailWord_4072026) baseStart_4072026 baseEnd_4072026 := by
    simpa [prefixWord, tailWord_4072026, baseEnd_4072026] using wordTrace_append hprefix tailTrace_4072026
  have hstable : (prefixWord ++ tailWord_4072026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072026).length < 2 ^ (prefixWord ++ tailWord_4072026).sum := by decide
  have hdescent : baseEnd_4072026 < baseStart_4072026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072034 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4072034 : Nat := 118140960795 + 4072034 * 2 ^ 59
def prefixEnd_4072034 : Nat := 4983230072969 + 3 ^ 40 * 4072034 * 2
def baseEnd_4072034 : Nat := 2090910683450426381948063

theorem tailTrace_4072034 : CollatzResearch.WordTrace tailWord_4072034 prefixEnd_4072034 2090910683450426381948063 := by
  unfold tailWord_4072034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37129820332430935221215789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99012854219815827256575437 37129820332430935221215789)
  ·
    refine ⟨13923682624661600707955921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37129820332430935221215789 13923682624661600707955921)
    ·
      refine ⟨10442761968496200530966941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13923682624661600707955921 10442761968496200530966941)
      ·
        refine ⟨3916035738186075199112603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10442761968496200530966941 3916035738186075199112603)
        ·
          refine ⟨5874053607279112798668905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916035738186075199112603 5874053607279112798668905)
          ·
            refine ⟨4405540205459334599001679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5874053607279112798668905 4405540205459334599001679)
            ·
              refine ⟨6608310308189001898502519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405540205459334599001679 6608310308189001898502519)
              ·
                refine ⟨9912465462283502847753779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608310308189001898502519 9912465462283502847753779)
                ·
                  refine ⟨14868698193425254271630669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912465462283502847753779 14868698193425254271630669)
                  ·
                    refine ⟨5575761822534470351861501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14868698193425254271630669 5575761822534470351861501)
                    ·
                      refine ⟨2090910683450426381948063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5575761822534470351861501 2090910683450426381948063)
                      ·
                        rfl

theorem cell23_4072034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4072034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072034 prefixEnd_4072034 := by exact prefixLift 4072034
  have htrace : WordTrace (prefixWord ++ tailWord_4072034) baseStart_4072034 baseEnd_4072034 := by
    simpa [prefixWord, tailWord_4072034, baseEnd_4072034] using wordTrace_append hprefix tailTrace_4072034
  have hstable : (prefixWord ++ tailWord_4072034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072034).length < 2 ^ (prefixWord ++ tailWord_4072034).sum := by decide
  have hdescent : baseEnd_4072034 < baseStart_4072034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072063 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 5]
def baseStart_4072063 : Nat := 118140960795 + 4072063 * 2 ^ 59
def prefixEnd_4072063 : Nat := 4983230072969 + 3 ^ 40 * 4072063 * 2
def baseEnd_4072063 : Nat := 232325063821045196498381

theorem tailTrace_4072063 : CollatzResearch.WordTrace tailWord_4072063 prefixEnd_4072063 232325063821045196498381 := by
  unfold tailWord_4072063
  simp only [CollatzResearch.WordTrace]
  refine ⟨148520339046618678837668843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99013559364412452558445895 148520339046618678837668843)
  ·
    refine ⟨222780508569928018256503265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148520339046618678837668843 222780508569928018256503265)
    ·
      refine ⟨167085381427446013692377449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222780508569928018256503265 167085381427446013692377449)
      ·
        refine ⟨125314036070584510269283087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167085381427446013692377449 125314036070584510269283087)
        ·
          refine ⟨187971054105876765403924631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125314036070584510269283087 187971054105876765403924631)
          ·
            refine ⟨281956581158815148105886947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187971054105876765403924631 281956581158815148105886947)
            ·
              refine ⟨422934871738222722158830421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281956581158815148105886947 422934871738222722158830421)
              ·
                refine ⟨2478134014091148762649397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 422934871738222722158830421 2478134014091148762649397)
                ·
                  refine ⟨232325063821045196498381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478134014091148762649397 232325063821045196498381)
                  ·
                    rfl

theorem cell23_4072063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 5].length) (baseStart_4072063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072063 prefixEnd_4072063 := by exact prefixLift 4072063
  have htrace : WordTrace (prefixWord ++ tailWord_4072063) baseStart_4072063 baseEnd_4072063 := by
    simpa [prefixWord, tailWord_4072063, baseEnd_4072063] using wordTrace_append hprefix tailTrace_4072063
  have hstable : (prefixWord ++ tailWord_4072063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072063).length < 2 ^ (prefixWord ++ tailWord_4072063).sum := by decide
  have hdescent : baseEnd_4072063 < baseStart_4072063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072076 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_4072076 : Nat := 118140960795 + 4072076 * 2 ^ 59
def prefixEnd_4072076 : Nat := 4983230072969 + 3 ^ 40 * 4072076 * 2
def baseEnd_4072076 : Nat := 696977416545971739207623

theorem tailTrace_4072076 : CollatzResearch.WordTrace tailWord_4072076 prefixEnd_4072076 696977416545971739207623 := by
  unfold tailWord_4072076
  simp only [CollatzResearch.WordTrace]
  refine ⟨74260406597785791028946041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99013875463714388038594721 74260406597785791028946041)
  ·
    refine ⟨55695304948339343271709531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74260406597785791028946041 55695304948339343271709531)
    ·
      refine ⟨83542957422509014907564297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55695304948339343271709531 83542957422509014907564297)
      ·
        refine ⟨62657218066881761180673223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83542957422509014907564297 62657218066881761180673223)
        ·
          refine ⟨93985827100322641771009835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62657218066881761180673223 93985827100322641771009835)
          ·
            refine ⟨140978740650483962656514753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93985827100322641771009835 140978740650483962656514753)
            ·
              refine ⟨105734055487862971992386065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140978740650483962656514753 105734055487862971992386065)
              ·
                refine ⟨79300541615897228994289549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105734055487862971992386065 79300541615897228994289549)
                ·
                  refine ⟨29737703105961460872858581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79300541615897228994289549 29737703105961460872858581)
                  ·
                    refine ⟨696977416545971739207623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29737703105961460872858581 696977416545971739207623)
                    ·
                      rfl

theorem cell23_4072076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_4072076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072076 prefixEnd_4072076 := by exact prefixLift 4072076
  have htrace : WordTrace (prefixWord ++ tailWord_4072076) baseStart_4072076 baseEnd_4072076 := by
    simpa [prefixWord, tailWord_4072076, baseEnd_4072076] using wordTrace_append hprefix tailTrace_4072076
  have hstable : (prefixWord ++ tailWord_4072076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072076).length < 2 ^ (prefixWord ++ tailWord_4072076).sum := by decide
  have hdescent : baseEnd_4072076 < baseStart_4072076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072083 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 7, 2]
def baseStart_4072083 : Nat := 118140960795 + 4072083 * 2 ^ 59
def prefixEnd_4072083 : Nat := 4983230072969 + 3 ^ 40 * 4072083 * 2
def baseEnd_4072083 : Nat := 2090935844002496690235337

theorem tailTrace_4072083 : CollatzResearch.WordTrace tailWord_4072083 prefixEnd_4072083 2090935844002496690235337 := by
  unfold tailWord_4072083
  simp only [CollatzResearch.WordTrace]
  refine ⟨148521068506546222253396903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99014045671030814835597935 148521068506546222253396903)
  ·
    refine ⟨222781602759819333380095355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148521068506546222253396903 222781602759819333380095355)
    ·
      refine ⟨334172404139729000070143033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222781602759819333380095355 334172404139729000070143033)
      ·
        refine ⟨250629303104796750052607275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334172404139729000070143033 250629303104796750052607275)
        ·
          refine ⟨375943954657195125078910913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250629303104796750052607275 375943954657195125078910913)
          ·
            refine ⟨281957965992896343809183185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375943954657195125078910913 281957965992896343809183185)
            ·
              refine ⟨211468474494672257856887389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281957965992896343809183185 211468474494672257856887389)
              ·
                refine ⟨79300677935502096696332771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211468474494672257856887389 79300677935502096696332771)
                ·
                  refine ⟨118951016903253145044499157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79300677935502096696332771 118951016903253145044499157)
                  ·
                    refine ⟨2787914458669995586980449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118951016903253145044499157 2787914458669995586980449)
                    ·
                      refine ⟨2090935844002496690235337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2787914458669995586980449 2090935844002496690235337)
                      ·
                        rfl

theorem cell23_4072083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7, 2].length) (baseStart_4072083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072083 prefixEnd_4072083 := by exact prefixLift 4072083
  have htrace : WordTrace (prefixWord ++ tailWord_4072083) baseStart_4072083 baseEnd_4072083 := by
    simpa [prefixWord, tailWord_4072083, baseEnd_4072083] using wordTrace_append hprefix tailTrace_4072083
  have hstable : (prefixWord ++ tailWord_4072083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072083).length < 2 ^ (prefixWord ++ tailWord_4072083).sum := by decide
  have hdescent : baseEnd_4072083 < baseStart_4072083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072153 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 6]
def baseStart_4072153 : Nat := 118140960795 + 4072153 * 2 ^ 59
def prefixEnd_4072153 : Nat := 4983230072969 + 3 ^ 40 * 4072153 * 2
def baseEnd_4072153 : Nat := 232330198627590157373335

theorem tailTrace_4072153 : CollatzResearch.WordTrace tailWord_4072153 prefixEnd_4072153 232330198627590157373335 := by
  unfold tailWord_4072153
  simp only [CollatzResearch.WordTrace]
  refine ⟨148523621616292624208445113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99015747744195082805630075 148523621616292624208445113)
  ·
    refine ⟨111392716212219468156333835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148523621616292624208445113 111392716212219468156333835)
    ·
      refine ⟨167089074318329202234500753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111392716212219468156333835 167089074318329202234500753)
      ·
        refine ⟨125316805738746901675875565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167089074318329202234500753 125316805738746901675875565)
        ·
          refine ⟨46993802152030088128453337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125316805738746901675875565 46993802152030088128453337)
          ·
            refine ⟨35245351614022566096340003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46993802152030088128453337 35245351614022566096340003)
            ·
              refine ⟨52868027421033849144510005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35245351614022566096340003 52868027421033849144510005)
              ·
                refine ⟨4956377570721923357297813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52868027421033849144510005 4956377570721923357297813)
                ·
                  refine ⟨232330198627590157373335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4956377570721923357297813 232330198627590157373335)
                  ·
                    rfl

theorem cell23_4072153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_4072153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072153 prefixEnd_4072153 := by exact prefixLift 4072153
  have htrace : WordTrace (prefixWord ++ tailWord_4072153) baseStart_4072153 baseEnd_4072153 := by
    simpa [prefixWord, tailWord_4072153, baseEnd_4072153] using wordTrace_append hprefix tailTrace_4072153
  have hstable : (prefixWord ++ tailWord_4072153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072153).length < 2 ^ (prefixWord ++ tailWord_4072153).sum := by decide
  have hdescent : baseEnd_4072153 < baseStart_4072153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072174 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_4072174 : Nat := 118140960795 + 4072174 * 2 ^ 59
def prefixEnd_4072174 : Nat := 4983230072969 + 3 ^ 40 * 4072174 * 2
def baseEnd_4072174 : Nat := 696994190247351944732473

theorem tailTrace_4072174 : CollatzResearch.WordTrace tailWord_4072174 prefixEnd_4072174 696994190247351944732473 := by
  unfold tailWord_4072174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565548443652068099369947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99016258366144363196639717 18565548443652068099369947)
  ·
    refine ⟨27848322665478102149054921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18565548443652068099369947 27848322665478102149054921)
    ·
      refine ⟨20886241999108576611791191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27848322665478102149054921 20886241999108576611791191)
      ·
        refine ⟨31329362998662864917686787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20886241999108576611791191 31329362998662864917686787)
        ·
          refine ⟨46994044497994297376530181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31329362998662864917686787 46994044497994297376530181)
          ·
            refine ⟨8811383343373930758099409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46994044497994297376530181 8811383343373930758099409)
            ·
              refine ⟨6608537507530448068574557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8811383343373930758099409 6608537507530448068574557)
              ·
                refine ⟨2478201565323918025715459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6608537507530448068574557 2478201565323918025715459)
                ·
                  refine ⟨3717302347985877038573189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478201565323918025715459 3717302347985877038573189)
                  ·
                    refine ⟨696994190247351944732473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3717302347985877038573189 696994190247351944732473)
                    ·
                      rfl

theorem cell23_4072174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_4072174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072174 prefixEnd_4072174 := by exact prefixLift 4072174
  have htrace : WordTrace (prefixWord ++ tailWord_4072174) baseStart_4072174 baseEnd_4072174 := by
    simpa [prefixWord, tailWord_4072174, baseEnd_4072174] using wordTrace_append hprefix tailTrace_4072174
  have hstable : (prefixWord ++ tailWord_4072174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072174).length < 2 ^ (prefixWord ++ tailWord_4072174).sum := by decide
  have hdescent : baseEnd_4072174 < baseStart_4072174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072190 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4072190 : Nat := 118140960795 + 4072190 * 2 ^ 59
def prefixEnd_4072190 : Nat := 4983230072969 + 3 ^ 40 * 4072190 * 2
def baseEnd_4072190 : Nat := 2090990786432527771597345

theorem tailTrace_4072190 : CollatzResearch.WordTrace tailWord_4072190 prefixEnd_4072190 2090990786432527771597345 := by
  unfold tailWord_4072190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565621389644822440942753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99016647411439053018361349 18565621389644822440942753)
  ·
    refine ⟨13924216042233616830707065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18565621389644822440942753 13924216042233616830707065)
    ·
      refine ⟨10443162031675212623030299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13924216042233616830707065 10443162031675212623030299)
      ·
        refine ⟨15664743047512818934545449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10443162031675212623030299 15664743047512818934545449)
        ·
          refine ⟨11748557285634614200909087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15664743047512818934545449 11748557285634614200909087)
          ·
            refine ⟨17622835928451921301363631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11748557285634614200909087 17622835928451921301363631)
            ·
              refine ⟨26434253892677881952045447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17622835928451921301363631 26434253892677881952045447)
              ·
                refine ⟨39651380839016822928068171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26434253892677881952045447 39651380839016822928068171)
                ·
                  refine ⟨59477071258525234392102257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39651380839016822928068171 59477071258525234392102257)
                  ·
                    refine ⟨44607803443893925794076693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59477071258525234392102257 44607803443893925794076693)
                    ·
                      refine ⟨2090990786432527771597345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44607803443893925794076693 2090990786432527771597345)
                      ·
                        rfl

theorem cell23_4072190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4072190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072190 prefixEnd_4072190 := by exact prefixLift 4072190
  have htrace : WordTrace (prefixWord ++ tailWord_4072190) baseStart_4072190 baseEnd_4072190 := by
    simpa [prefixWord, tailWord_4072190, baseEnd_4072190] using wordTrace_append hprefix tailTrace_4072190
  have hstable : (prefixWord ++ tailWord_4072190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072190).length < 2 ^ (prefixWord ++ tailWord_4072190).sum := by decide
  have hdescent : baseEnd_4072190 < baseStart_4072190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072243 : List Nat := [1, 1, 1, 2, 6, 1, 11]
def baseStart_4072243 : Nat := 118140960795 + 4072243 * 2 ^ 59
def prefixEnd_4072243 : Nat := 4983230072969 + 3 ^ 40 * 4072243 * 2
def baseEnd_4072243 : Nat := 25815037048237235360921

theorem tailTrace_4072243 : CollatzResearch.WordTrace tailWord_4072243 prefixEnd_4072243 25815037048237235360921 := by
  unfold tailWord_4072243
  simp only [CollatzResearch.WordTrace]
  refine ⟨148526904185966569579221383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99017936123977713052814255 148526904185966569579221383)
  ·
    refine ⟨222790356278949854368832075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148526904185966569579221383 222790356278949854368832075)
    ·
      refine ⟨334185534418424781553248113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222790356278949854368832075 334185534418424781553248113)
      ·
        refine ⟨250639150813818586164936085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334185534418424781553248113 250639150813818586164936085)
        ·
          refine ⟨11748710194397746226481379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250639150813818586164936085 11748710194397746226481379)
          ·
            refine ⟨17623065291596619339722069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11748710194397746226481379 17623065291596619339722069)
            ·
              refine ⟨25815037048237235360921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17623065291596619339722069 25815037048237235360921)
              ·
                rfl

theorem cell23_4072243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 11].length) (baseStart_4072243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072243 prefixEnd_4072243 := by exact prefixLift 4072243
  have htrace : WordTrace (prefixWord ++ tailWord_4072243) baseStart_4072243 baseEnd_4072243 := by
    simpa [prefixWord, tailWord_4072243, baseEnd_4072243] using wordTrace_append hprefix tailTrace_4072243
  have hstable : (prefixWord ++ tailWord_4072243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072243).length < 2 ^ (prefixWord ++ tailWord_4072243).sum := by decide
  have hdescent : baseEnd_4072243 < baseStart_4072243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072263 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_4072263 : Nat := 118140960795 + 4072263 * 2 ^ 59
def prefixEnd_4072263 : Nat := 4983230072969 + 3 ^ 40 * 4072263 * 2
def baseEnd_4072263 : Nat := 2091028270520305985984509

theorem tailTrace_4072263 : CollatzResearch.WordTrace tailWord_4072263 prefixEnd_4072263 2091028270520305985984509 := by
  unfold tailWord_4072263
  simp only [CollatzResearch.WordTrace]
  refine ⟨148527633645894112994949443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99018422430596075329966295 148527633645894112994949443)
  ·
    refine ⟨222791450468841169492424165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148527633645894112994949443 222791450468841169492424165)
    ·
      refine ⟨41773396962907719279829531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222791450468841169492424165 41773396962907719279829531)
      ·
        refine ⟨62660095444361578919744297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41773396962907719279829531 62660095444361578919744297)
        ·
          refine ⟨46995071583271184189808223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62660095444361578919744297 46995071583271184189808223)
          ·
            refine ⟨70492607374906776284712335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46995071583271184189808223 70492607374906776284712335)
            ·
              refine ⟨105738911062360164427068503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70492607374906776284712335 105738911062360164427068503)
              ·
                refine ⟨158608366593540246640602755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105738911062360164427068503 158608366593540246640602755)
                ·
                  refine ⟨237912549890310369960904133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158608366593540246640602755 237912549890310369960904133)
                  ·
                    refine ⟨44608603104433194367669525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 237912549890310369960904133 44608603104433194367669525)
                    ·
                      refine ⟨2091028270520305985984509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44608603104433194367669525 2091028270520305985984509)
                      ·
                        rfl

theorem cell23_4072263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_4072263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072263 prefixEnd_4072263 := by exact prefixLift 4072263
  have htrace : WordTrace (prefixWord ++ tailWord_4072263) baseStart_4072263 baseEnd_4072263 := by
    simpa [prefixWord, tailWord_4072263, baseEnd_4072263] using wordTrace_append hprefix tailTrace_4072263
  have hstable : (prefixWord ++ tailWord_4072263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072263).length < 2 ^ (prefixWord ++ tailWord_4072263).sum := by decide
  have hdescent : baseEnd_4072263 < baseStart_4072263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072270 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_4072270 : Nat := 118140960795 + 4072270 * 2 ^ 59
def prefixEnd_4072270 : Nat := 4983230072969 + 3 ^ 40 * 4072270 * 2
def baseEnd_4072270 : Nat := 2091031864884887458596977

theorem tailTrace_4072270 : CollatzResearch.WordTrace tailWord_4072270 prefixEnd_4072270 2091031864884887458596977 := by
  unfold tailWord_4072270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565986119608594148806783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99018592637912502126969509 18565986119608594148806783)
  ·
    refine ⟨27848979179412891223210175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18565986119608594148806783 27848979179412891223210175)
    ·
      refine ⟨41773468769119336834815263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27848979179412891223210175 41773468769119336834815263)
      ·
        refine ⟨62660203153679005252222895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41773468769119336834815263 62660203153679005252222895)
        ·
          refine ⟨93990304730518507878334343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62660203153679005252222895 93990304730518507878334343)
          ·
            refine ⟨140985457095777761817501515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93990304730518507878334343 140985457095777761817501515)
            ·
              refine ⟨211478185643666642726252273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140985457095777761817501515 211478185643666642726252273)
              ·
                refine ⟨158608639232749982044689205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211478185643666642726252273 158608639232749982044689205)
                ·
                  refine ⟨14869559928070310816689613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158608639232749982044689205 14869559928070310816689613)
                  ·
                    refine ⟨5576084973026366556258605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14869559928070310816689613 5576084973026366556258605)
                    ·
                      refine ⟨2091031864884887458596977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5576084973026366556258605 2091031864884887458596977)
                      ·
                        rfl

theorem cell23_4072270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_4072270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072270 prefixEnd_4072270 := by exact prefixLift 4072270
  have htrace : WordTrace (prefixWord ++ tailWord_4072270) baseStart_4072270 baseEnd_4072270 := by
    simpa [prefixWord, tailWord_4072270, baseEnd_4072270] using wordTrace_append hprefix tailTrace_4072270
  have hstable : (prefixWord ++ tailWord_4072270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072270).length < 2 ^ (prefixWord ++ tailWord_4072270).sum := by decide
  have hdescent : baseEnd_4072270 < baseStart_4072270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072283 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_4072283 : Nat := 118140960795 + 4072283 * 2 ^ 59
def prefixEnd_4072283 : Nat := 4983230072969 + 3 ^ 40 * 4072283 * 2
def baseEnd_4072283 : Nat := 2091038540133395907734417

theorem tailTrace_4072283 : CollatzResearch.WordTrace tailWord_4072283 prefixEnd_4072283 2091038540133395907734417 := by
  unfold tailWord_4072283
  simp only [CollatzResearch.WordTrace]
  refine ⟨148528363105821656410677503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99018908737214437607118335 148528363105821656410677503)
  ·
    refine ⟨222792544658732484616016255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148528363105821656410677503 222792544658732484616016255)
    ·
      refine ⟨334188816988098726924024383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222792544658732484616016255 334188816988098726924024383)
      ·
        refine ⟨501283225482148090386036575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334188816988098726924024383 501283225482148090386036575)
        ·
          refine ⟨751924838223222135579054863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501283225482148090386036575 751924838223222135579054863)
          ·
            refine ⟨1127887257334833203368582295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751924838223222135579054863 1127887257334833203368582295)
            ·
              refine ⟨1691830886002249805052873443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127887257334833203368582295 1691830886002249805052873443)
              ·
                refine ⟨2537746329003374707579310165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691830886002249805052873443 2537746329003374707579310165)
                ·
                  refine ⟨29739214793008297354445041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2537746329003374707579310165 29739214793008297354445041)
                  ·
                    refine ⟨22304411094756223015833781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29739214793008297354445041 22304411094756223015833781)
                    ·
                      refine ⟨2091038540133395907734417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22304411094756223015833781 2091038540133395907734417)
                      ·
                        rfl

theorem cell23_4072283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_4072283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072283 prefixEnd_4072283 := by exact prefixLift 4072283
  have htrace : WordTrace (prefixWord ++ tailWord_4072283) baseStart_4072283 baseEnd_4072283 := by
    simpa [prefixWord, tailWord_4072283, baseEnd_4072283] using wordTrace_append hprefix tailTrace_4072283
  have hstable : (prefixWord ++ tailWord_4072283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072283).length < 2 ^ (prefixWord ++ tailWord_4072283).sum := by decide
  have hdescent : baseEnd_4072283 < baseStart_4072283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072303 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 8]
def baseStart_4072303 : Nat := 118140960795 + 4072303 * 2 ^ 59
def prefixEnd_4072303 : Nat := 4983230072969 + 3 ^ 40 * 4072303 * 2
def baseEnd_4072303 : Nat := 697016269915495276494775

theorem tailTrace_4072303 : CollatzResearch.WordTrace tailWord_4072303 prefixEnd_4072303 697016269915495276494775 := by
  unfold tailWord_4072303
  simp only [CollatzResearch.WordTrace]
  refine ⟨148529092565749199826405563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99019395043832799884270375 148529092565749199826405563)
  ·
    refine ⟨222793638848623799739608345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148529092565749199826405563 222793638848623799739608345)
    ·
      refine ⟨167095229136467849804706259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222793638848623799739608345 167095229136467849804706259)
      ·
        refine ⟨250642843704701774707059389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167095229136467849804706259 250642843704701774707059389)
        ·
          refine ⟨93991066389263165515147271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250642843704701774707059389 93991066389263165515147271)
          ·
            refine ⟨140986599583894748272720907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93991066389263165515147271 140986599583894748272720907)
            ·
              refine ⟨211479899375842122409081361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140986599583894748272720907 211479899375842122409081361)
              ·
                refine ⟨158609924531881591806811021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211479899375842122409081361 158609924531881591806811021)
                ·
                  refine ⟨59478721699455596927554133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158609924531881591806811021 59478721699455596927554133)
                  ·
                    refine ⟨697016269915495276494775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59478721699455596927554133 697016269915495276494775)
                    ·
                      rfl

theorem cell23_4072303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_4072303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072303 prefixEnd_4072303 := by exact prefixLift 4072303
  have htrace : WordTrace (prefixWord ++ tailWord_4072303) baseStart_4072303 baseEnd_4072303 := by
    simpa [prefixWord, tailWord_4072303, baseEnd_4072303] using wordTrace_append hprefix tailTrace_4072303
  have hstable : (prefixWord ++ tailWord_4072303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072303).length < 2 ^ (prefixWord ++ tailWord_4072303).sum := by decide
  have hdescent : baseEnd_4072303 < baseStart_4072303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072377 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4072377 : Nat := 118140960795 + 4072377 * 2 ^ 59
def prefixEnd_4072377 : Nat := 4983230072969 + 3 ^ 40 * 4072377 * 2
def baseEnd_4072377 : Nat := 2091086807314918539958985

theorem tailTrace_4072377 : CollatzResearch.WordTrace tailWord_4072377 prefixEnd_4072377 2091086807314918539958985 := by
  unfold tailWord_4072377
  simp only [CollatzResearch.WordTrace]
  refine ⟨148531791567481110464599385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99021194378320740309732923 148531791567481110464599385)
  ·
    refine ⟨111398843675610832848449539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148531791567481110464599385 111398843675610832848449539)
    ·
      refine ⟨167098265513416249272674309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111398843675610832848449539 167098265513416249272674309)
      ·
        refine ⟨31330924783765546738626433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167098265513416249272674309 31330924783765546738626433)
        ·
          refine ⟨23498193587824160053969825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31330924783765546738626433 23498193587824160053969825)
          ·
            refine ⟨17623645190868120040477369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23498193587824160053969825 17623645190868120040477369)
            ·
              refine ⟨13217733893151090030358027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17623645190868120040477369 13217733893151090030358027)
              ·
                refine ⟨19826600839726635045537041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13217733893151090030358027 19826600839726635045537041)
                ·
                  refine ⟨14869950629794976284152781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19826600839726635045537041 14869950629794976284152781)
                  ·
                    refine ⟨5576231486173116106557293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14869950629794976284152781 5576231486173116106557293)
                    ·
                      refine ⟨2091086807314918539958985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5576231486173116106557293 2091086807314918539958985)
                      ·
                        rfl

theorem cell23_4072377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4072377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072377 prefixEnd_4072377 := by exact prefixLift 4072377
  have htrace : WordTrace (prefixWord ++ tailWord_4072377) baseStart_4072377 baseEnd_4072377 := by
    simpa [prefixWord, tailWord_4072377, baseEnd_4072377] using wordTrace_append hprefix tailTrace_4072377
  have hstable : (prefixWord ++ tailWord_4072377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072377).length < 2 ^ (prefixWord ++ tailWord_4072377).sum := by decide
  have hdescent : baseEnd_4072377 < baseStart_4072377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072418 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_4072418 : Nat := 118140960795 + 4072418 * 2 ^ 59
def prefixEnd_4072418 : Nat := 4983230072969 + 3 ^ 40 * 4072418 * 2
def baseEnd_4072418 : Nat := 232345317780194764394033

theorem tailTrace_4072418 : CollatzResearch.WordTrace tailWord_4072418 prefixEnd_4072418 232345317780194764394033 := by
  unfold tailWord_4072418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37133321740083143616710477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99022191306888382977894605 37133321740083143616710477)
  ·
    refine ⟨13924995652531178856266429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37133321740083143616710477 13924995652531178856266429)
    ·
      refine ⟨5221873369699192071099911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13924995652531178856266429 5221873369699192071099911)
      ·
        refine ⟨7832810054548788106649867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221873369699192071099911 7832810054548788106649867)
        ·
          refine ⟨11749215081823182159974801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832810054548788106649867 11749215081823182159974801)
          ·
            refine ⟨8811911311367386619981101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11749215081823182159974801 8811911311367386619981101)
            ·
              refine ⟨3304466741762769982492913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8811911311367386619981101 3304466741762769982492913)
              ·
                refine ⟨2478350056322077486869685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3304466741762769982492913 2478350056322077486869685)
                ·
                  refine ⟨232345317780194764394033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478350056322077486869685 232345317780194764394033)
                  ·
                    rfl

theorem cell23_4072418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_4072418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072418 prefixEnd_4072418 := by exact prefixLift 4072418
  have htrace : WordTrace (prefixWord ++ tailWord_4072418) baseStart_4072418 baseEnd_4072418 := by
    simpa [prefixWord, tailWord_4072418, baseEnd_4072418] using wordTrace_append hprefix tailTrace_4072418
  have hstable : (prefixWord ++ tailWord_4072418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072418).length < 2 ^ (prefixWord ++ tailWord_4072418).sum := by decide
  have hdescent : baseEnd_4072418 < baseStart_4072418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072420 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4072420 : Nat := 118140960795 + 4072420 * 2 ^ 59
def prefixEnd_4072420 : Nat := 4983230072969 + 3 ^ 40 * 4072420 * 2
def baseEnd_4072420 : Nat := 2091108886983061871721287

theorem tailTrace_4072420 : CollatzResearch.WordTrace tailWord_4072420 prefixEnd_4072420 2091108886983061871721287 := by
  unfold tailWord_4072420
  simp only [CollatzResearch.WordTrace]
  refine ⟨74266679953162664404207357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99022239937550219205609809 74266679953162664404207357)
  ·
    refine ⟨27850004982435999151577759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74266679953162664404207357 27850004982435999151577759)
    ·
      refine ⟨41775007473653998727366639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27850004982435999151577759 41775007473653998727366639)
      ·
        refine ⟨62662511210480998091049959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41775007473653998727366639 62662511210480998091049959)
        ·
          refine ⟨93993766815721497136574939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62662511210480998091049959 93993766815721497136574939)
          ·
            refine ⟨140990650223582245704862409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93993766815721497136574939 140990650223582245704862409)
            ·
              refine ⟨105742987667686684278646807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140990650223582245704862409 105742987667686684278646807)
              ·
                refine ⟨158614481501530026417970211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105742987667686684278646807 158614481501530026417970211)
                ·
                  refine ⟨237921722252295039626955317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158614481501530026417970211 237921722252295039626955317)
                  ·
                    refine ⟨22305161461152659965027061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237921722252295039626955317 22305161461152659965027061)
                    ·
                      refine ⟨2091108886983061871721287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22305161461152659965027061 2091108886983061871721287)
                      ·
                        rfl

theorem cell23_4072420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4072420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072420 prefixEnd_4072420 := by exact prefixLift 4072420
  have htrace : WordTrace (prefixWord ++ tailWord_4072420) baseStart_4072420 baseEnd_4072420 := by
    simpa [prefixWord, tailWord_4072420, baseEnd_4072420] using wordTrace_append hprefix tailTrace_4072420
  have hstable : (prefixWord ++ tailWord_4072420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072420).length < 2 ^ (prefixWord ++ tailWord_4072420).sum := by decide
  have hdescent : baseEnd_4072420 < baseStart_4072420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072517 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_4072517 : Nat := 118140960795 + 4072517 * 2 ^ 59
def prefixEnd_4072517 : Nat := 4983230072969 + 3 ^ 40 * 4072517 * 2
def baseEnd_4072517 : Nat := 697052898202182664069447

theorem tailTrace_4072517 : CollatzResearch.WordTrace tailWord_4072517 prefixEnd_4072517 697052898202182664069447 := by
  unfold tailWord_4072517
  simp only [CollatzResearch.WordTrace]
  refine ⟨148536897786973914374695805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99024598524649276249797203 148536897786973914374695805)
  ·
    refine ⟨55701336670115217890510927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148536897786973914374695805 55701336670115217890510927)
    ·
      refine ⟨83552005005172826835766391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55701336670115217890510927 83552005005172826835766391)
      ·
        refine ⟨125328007507759240253649587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83552005005172826835766391 125328007507759240253649587)
        ·
          refine ⟨187992011261638860380474381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125328007507759240253649587 187992011261638860380474381)
          ·
            refine ⟨70497004223114572642677893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187992011261638860380474381 70497004223114572642677893)
            ·
              refine ⟨13218188291833982370502105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70497004223114572642677893 13218188291833982370502105)
              ·
                refine ⟨9913641218875486777876579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13218188291833982370502105 9913641218875486777876579)
                ·
                  refine ⟨14870461828313230166814869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913641218875486777876579 14870461828313230166814869)
                  ·
                    refine ⟨697052898202182664069447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14870461828313230166814869 697052898202182664069447)
                    ·
                      rfl

theorem cell23_4072517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_4072517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072517 prefixEnd_4072517 := by exact prefixLift 4072517
  have htrace : WordTrace (prefixWord ++ tailWord_4072517) baseStart_4072517 baseEnd_4072517 := by
    simpa [prefixWord, tailWord_4072517, baseEnd_4072517] using wordTrace_append hprefix tailTrace_4072517
  have hstable : (prefixWord ++ tailWord_4072517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072517).length < 2 ^ (prefixWord ++ tailWord_4072517).sum := by decide
  have hdescent : baseEnd_4072517 < baseStart_4072517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072554 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4072554 : Nat := 118140960795 + 4072554 * 2 ^ 59
def prefixEnd_4072554 : Nat := 4983230072969 + 3 ^ 40 * 4072554 * 2
def baseEnd_4072554 : Nat := 2091177693390764347445671

theorem tailTrace_4072554 : CollatzResearch.WordTrace tailWord_4072554 prefixEnd_4072554 2091177693390764347445671 := by
  unfold tailWord_4072554
  simp only [CollatzResearch.WordTrace]
  refine ⟨37134561821959967423448179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99025498191893246462528477 37134561821959967423448179)
  ·
    refine ⟨55701842732939951135172269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37134561821959967423448179 55701842732939951135172269)
    ·
      refine ⟨20888191024852481675689601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55701842732939951135172269 20888191024852481675689601)
      ·
        refine ⟨15666143268639361256767201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20888191024852481675689601 15666143268639361256767201)
        ·
          refine ⟨11749607451479520942575401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15666143268639361256767201 11749607451479520942575401)
          ·
            refine ⟨8812205588609640706931551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11749607451479520942575401 8812205588609640706931551)
            ·
              refine ⟨13218308382914461060397327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812205588609640706931551 13218308382914461060397327)
              ·
                refine ⟨19827462574371691590595991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13218308382914461060397327 19827462574371691590595991)
                ·
                  refine ⟨29741193861557537385893987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19827462574371691590595991 29741193861557537385893987)
                  ·
                    refine ⟨44611790792336306078840981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29741193861557537385893987 44611790792336306078840981)
                    ·
                      refine ⟨2091177693390764347445671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44611790792336306078840981 2091177693390764347445671)
                      ·
                        rfl

theorem cell23_4072554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4072554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072554 prefixEnd_4072554 := by exact prefixLift 4072554
  have htrace : WordTrace (prefixWord ++ tailWord_4072554) baseStart_4072554 baseEnd_4072554 := by
    simpa [prefixWord, tailWord_4072554, baseEnd_4072554] using wordTrace_append hprefix tailTrace_4072554
  have hstable : (prefixWord ++ tailWord_4072554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072554).length < 2 ^ (prefixWord ++ tailWord_4072554).sum := by decide
  have hdescent : baseEnd_4072554 < baseStart_4072554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072558 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_4072558 : Nat := 118140960795 + 4072558 * 2 ^ 59
def prefixEnd_4072558 : Nat := 4983230072969 + 3 ^ 40 * 4072558 * 2
def baseEnd_4072558 : Nat := 2091179747313382331795653

theorem tailTrace_4072558 : CollatzResearch.WordTrace tailWord_4072558 prefixEnd_4072558 2091179747313382331795653 := by
  unfold tailWord_4072558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567299147478172297117291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99025595453216918917958885 18567299147478172297117291)
  ·
    refine ⟨27850948721217258445675937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18567299147478172297117291 27850948721217258445675937)
    ·
      refine ⟨20888211540912943834256953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27850948721217258445675937 20888211540912943834256953)
      ·
        refine ⟨15666158655684707875692715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20888211540912943834256953 15666158655684707875692715)
        ·
          refine ⟨23499237983527061813539073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15666158655684707875692715 23499237983527061813539073)
          ·
            refine ⟨17624428487645296360154305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23499237983527061813539073 17624428487645296360154305)
            ·
              refine ⟨13218321365733972270115729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17624428487645296360154305 13218321365733972270115729)
              ·
                refine ⟨9913741024300479202586797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13218321365733972270115729 9913741024300479202586797)
                ·
                  refine ⟨3717652884112679700970049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9913741024300479202586797 3717652884112679700970049)
                  ·
                    refine ⟨2788239663084509775727537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3717652884112679700970049 2788239663084509775727537)
                    ·
                      refine ⟨2091179747313382331795653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788239663084509775727537 2091179747313382331795653)
                      ·
                        rfl

theorem cell23_4072558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_4072558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072558 prefixEnd_4072558 := by exact prefixLift 4072558
  have htrace : WordTrace (prefixWord ++ tailWord_4072558) baseStart_4072558 baseEnd_4072558 := by
    simpa [prefixWord, tailWord_4072558, baseEnd_4072558] using wordTrace_append hprefix tailTrace_4072558
  have hstable : (prefixWord ++ tailWord_4072558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072558).length < 2 ^ (prefixWord ++ tailWord_4072558).sum := by decide
  have hdescent : baseEnd_4072558 < baseStart_4072558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072631 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 1, 4, 2]
def baseStart_4072631 : Nat := 118140960795 + 4072631 * 2 ^ 59
def prefixEnd_4072631 : Nat := 4983230072969 + 3 ^ 40 * 4072631 * 2
def baseEnd_4072631 : Nat := 2091217231401160546182817

theorem tailTrace_4072631 : CollatzResearch.WordTrace tailWord_4072631 prefixEnd_4072631 2091217231401160546182817 := by
  unfold tailWord_4072631
  simp only [CollatzResearch.WordTrace]
  refine ⟨148541055708560911844345747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99027370472373941229563831 148541055708560911844345747)
  ·
    refine ⟨222811583562841367766518621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148541055708560911844345747 222811583562841367766518621)
    ·
      refine ⟨83554343836065512912444483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222811583562841367766518621 83554343836065512912444483)
      ·
        refine ⟨125331515754098269368666725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83554343836065512912444483 125331515754098269368666725)
        ·
          refine ⟨23499659203893425506625011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125331515754098269368666725 23499659203893425506625011)
          ·
            refine ⟨35249488805840138259937517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23499659203893425506625011 35249488805840138259937517)
            ·
              refine ⟨13218558302190051847476569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35249488805840138259937517 13218558302190051847476569)
              ·
                refine ⟨9913918726642538885607427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13218558302190051847476569 9913918726642538885607427)
                ·
                  refine ⟨14870878089963808328411141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913918726642538885607427 14870878089963808328411141)
                  ·
                    refine ⟨2788289641868214061577089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14870878089963808328411141 2788289641868214061577089)
                    ·
                      refine ⟨2091217231401160546182817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788289641868214061577089 2091217231401160546182817)
                      ·
                        rfl

theorem cell23_4072631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_4072631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072631 prefixEnd_4072631 := by exact prefixLift 4072631
  have htrace : WordTrace (prefixWord ++ tailWord_4072631) baseStart_4072631 baseEnd_4072631 := by
    simpa [prefixWord, tailWord_4072631, baseEnd_4072631] using wordTrace_append hprefix tailTrace_4072631
  have hstable : (prefixWord ++ tailWord_4072631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072631).length < 2 ^ (prefixWord ++ tailWord_4072631).sum := by decide
  have hdescent : baseEnd_4072631 < baseStart_4072631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072647 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_4072647 : Nat := 118140960795 + 4072647 * 2 ^ 59
def prefixEnd_4072647 : Nat := 4983230072969 + 3 ^ 40 * 4072647 * 2
def baseEnd_4072647 : Nat := 2091225447091632483582743

theorem tailTrace_4072647 : CollatzResearch.WordTrace tailWord_4072647 prefixEnd_4072647 2091225447091632483582743 := by
  unfold tailWord_4072647
  simp only [CollatzResearch.WordTrace]
  refine ⟨148541639276502946576928195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99027759517668631051285463 148541639276502946576928195)
  ·
    refine ⟨222812458914754419865392293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148541639276502946576928195 222812458914754419865392293)
    ·
      refine ⟨41777336046516453724761055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222812458914754419865392293 41777336046516453724761055)
      ·
        refine ⟨62666004069774680587141583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41777336046516453724761055 62666004069774680587141583)
        ·
          refine ⟨93999006104662020880712375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62666004069774680587141583 93999006104662020880712375)
          ·
            refine ⟨140998509156993031321068563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93999006104662020880712375 140998509156993031321068563)
            ·
              refine ⟨211497763735489546981602845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140998509156993031321068563 211497763735489546981602845)
              ·
                refine ⟨79311661400808580118101067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211497763735489546981602845 79311661400808580118101067)
                ·
                  refine ⟨118967492101212870177151601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79311661400808580118101067 118967492101212870177151601)
                  ·
                    refine ⟨89225619075909652632863701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118967492101212870177151601 89225619075909652632863701)
                    ·
                      refine ⟨2091225447091632483582743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89225619075909652632863701 2091225447091632483582743)
                      ·
                        rfl

theorem cell23_4072647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_4072647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072647 prefixEnd_4072647 := by exact prefixLift 4072647
  have htrace : WordTrace (prefixWord ++ tailWord_4072647) baseStart_4072647 baseEnd_4072647 := by
    simpa [prefixWord, tailWord_4072647, baseEnd_4072647] using wordTrace_append hprefix tailTrace_4072647
  have hstable : (prefixWord ++ tailWord_4072647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072647).length < 2 ^ (prefixWord ++ tailWord_4072647).sum := by decide
  have hdescent : baseEnd_4072647 < baseStart_4072647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072648 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_4072648 : Nat := 118140960795 + 4072648 * 2 ^ 59
def prefixEnd_4072648 : Nat := 4983230072969 + 3 ^ 40 * 4072648 * 2
def baseEnd_4072648 : Nat := 2091225960572286979670239

theorem tailTrace_4072648 : CollatzResearch.WordTrace tailWord_4072648 prefixEnd_4072648 2091225960572286979670239 := by
  unfold tailWord_4072648
  simp only [CollatzResearch.WordTrace]
  refine ⟨74270837874749661873857299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99027783832999549165143065 74270837874749661873857299)
  ·
    refine ⟨111406256812124492810785949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74270837874749661873857299 111406256812124492810785949)
    ·
      refine ⟨41777346304546684804044731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111406256812124492810785949 41777346304546684804044731)
      ·
        refine ⟨62666019456820027206067097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41777346304546684804044731 62666019456820027206067097)
        ·
          refine ⟨46999514592615020404550323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62666019456820027206067097 46999514592615020404550323)
          ·
            refine ⟨70499271888922530606825485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46999514592615020404550323 70499271888922530606825485)
            ·
              refine ⟨26437226958345948977559557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70499271888922530606825485 26437226958345948977559557)
              ·
                refine ⟨4956980054689865433292417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26437226958345948977559557 4956980054689865433292417)
                ·
                  refine ⟨3717735041017399074969313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956980054689865433292417 3717735041017399074969313)
                  ·
                    refine ⟨2788301280763049306226985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3717735041017399074969313 2788301280763049306226985)
                    ·
                      refine ⟨2091225960572286979670239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788301280763049306226985 2091225960572286979670239)
                      ·
                        rfl

theorem cell23_4072648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_4072648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072648 prefixEnd_4072648 := by exact prefixLift 4072648
  have htrace : WordTrace (prefixWord ++ tailWord_4072648) baseStart_4072648 baseEnd_4072648 := by
    simpa [prefixWord, tailWord_4072648, baseEnd_4072648] using wordTrace_append hprefix tailTrace_4072648
  have hstable : (prefixWord ++ tailWord_4072648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072648).length < 2 ^ (prefixWord ++ tailWord_4072648).sum := by decide
  have hdescent : baseEnd_4072648 < baseStart_4072648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072657 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_4072657 : Nat := 118140960795 + 4072657 * 2 ^ 59
def prefixEnd_4072657 : Nat := 4983230072969 + 3 ^ 40 * 4072657 * 2
def baseEnd_4072657 : Nat := 2091230581898177444457697

theorem tailTrace_4072657 : CollatzResearch.WordTrace tailWord_4072657 prefixEnd_4072657 2091230581898177444457697 := by
  unfold tailWord_4072657
  simp only [CollatzResearch.WordTrace]
  refine ⟨148542004006466718284792225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99028002670977812189861483 148542004006466718284792225)
  ·
    refine ⟨111406503004850038713594169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148542004006466718284792225 111406503004850038713594169)
    ·
      refine ⟨83554877253637529035195627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111406503004850038713594169 83554877253637529035195627)
      ·
        refine ⟨125332315880456293552793441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83554877253637529035195627 125332315880456293552793441)
        ·
          refine ⟨93999236910342220164595081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125332315880456293552793441 93999236910342220164595081)
          ·
            refine ⟨70499427682756665123446311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93999236910342220164595081 70499427682756665123446311)
            ·
              refine ⟨105749141524134997685169467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70499427682756665123446311 105749141524134997685169467)
              ·
                refine ⟨158623712286202496527754201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105749141524134997685169467 158623712286202496527754201)
                ·
                  refine ⟨118967784214651872395815651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158623712286202496527754201 118967784214651872395815651)
                  ·
                    refine ⟨178451676321977808593723477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118967784214651872395815651 178451676321977808593723477)
                    ·
                      refine ⟨2091230581898177444457697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 178451676321977808593723477 2091230581898177444457697)
                      ·
                        rfl

theorem cell23_4072657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_4072657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072657 prefixEnd_4072657 := by exact prefixLift 4072657
  have htrace : WordTrace (prefixWord ++ tailWord_4072657) baseStart_4072657 baseEnd_4072657 := by
    simpa [prefixWord, tailWord_4072657, baseEnd_4072657] using wordTrace_append hprefix tailTrace_4072657
  have hstable : (prefixWord ++ tailWord_4072657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072657).length < 2 ^ (prefixWord ++ tailWord_4072657).sum := by decide
  have hdescent : baseEnd_4072657 < baseStart_4072657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072661 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4072661 : Nat := 118140960795 + 4072661 * 2 ^ 59
def prefixEnd_4072661 : Nat := 4983230072969 + 3 ^ 40 * 4072661 * 2
def baseEnd_4072661 : Nat := 2091232635820795428807679

theorem tailTrace_4072661 : CollatzResearch.WordTrace tailWord_4072661 prefixEnd_4072661 2091232635820795428807679 := by
  unfold tailWord_4072661
  simp only [CollatzResearch.WordTrace]
  refine ⟨148542149898452226967937837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99028099932301484645291891 148542149898452226967937837)
  ·
    refine ⟨55703306211919585112976689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148542149898452226967937837 55703306211919585112976689)
    ·
      refine ⟨41777479658939688834732517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55703306211919585112976689 41777479658939688834732517)
      ·
        refine ⟨7833277436051191656512347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41777479658939688834732517 7833277436051191656512347)
        ·
          refine ⟨11749916154076787484768521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833277436051191656512347 11749916154076787484768521)
          ·
            refine ⟨8812437115557590613576391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11749916154076787484768521 8812437115557590613576391)
            ·
              refine ⟨13218655673336385920364587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812437115557590613576391 13218655673336385920364587)
              ·
                refine ⟨19827983510004578880546881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13218655673336385920364587 19827983510004578880546881)
                ·
                  refine ⟨14870987632503434160410161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19827983510004578880546881 14870987632503434160410161)
                  ·
                    refine ⟨11153240724377575620307621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14870987632503434160410161 11153240724377575620307621)
                    ·
                      refine ⟨2091232635820795428807679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11153240724377575620307621 2091232635820795428807679)
                      ·
                        rfl

theorem cell23_4072661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4072661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072661 prefixEnd_4072661 := by exact prefixLift 4072661
  have htrace : WordTrace (prefixWord ++ tailWord_4072661) baseStart_4072661 baseEnd_4072661 := by
    simpa [prefixWord, tailWord_4072661, baseEnd_4072661] using wordTrace_append hprefix tailTrace_4072661
  have hstable : (prefixWord ++ tailWord_4072661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072661).length < 2 ^ (prefixWord ++ tailWord_4072661).sum := by decide
  have hdescent : baseEnd_4072661 < baseStart_4072661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072684 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_4072684 : Nat := 118140960795 + 4072684 * 2 ^ 59
def prefixEnd_4072684 : Nat := 4983230072969 + 3 ^ 40 * 4072684 * 2
def baseEnd_4072684 : Nat := 697081481958616279606691

theorem tailTrace_4072684 : CollatzResearch.WordTrace tailWord_4072684 prefixEnd_4072684 697081481958616279606691 := by
  unfold tailWord_4072684
  simp only [CollatzResearch.WordTrace]
  refine ⟨74271494388684450948012553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99028659184912601264016737 74271494388684450948012553)
  ·
    refine ⟨55703620791513338211009415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74271494388684450948012553 55703620791513338211009415)
    ·
      refine ⟨83555431187270007316514123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55703620791513338211009415 83555431187270007316514123)
      ·
        refine ⟨125333146780905010974771185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83555431187270007316514123 125333146780905010974771185)
        ·
          refine ⟨93999860085678758231078389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125333146780905010974771185 93999860085678758231078389)
          ·
            refine ⟨8812486883032383584163599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93999860085678758231078389 8812486883032383584163599)
            ·
              refine ⟨13218730324548575376245399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812486883032383584163599 13218730324548575376245399)
              ·
                refine ⟨19828095486822863064368099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13218730324548575376245399 19828095486822863064368099)
                ·
                  refine ⟨29742143230234294596552149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19828095486822863064368099 29742143230234294596552149)
                  ·
                    refine ⟨697081481958616279606691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29742143230234294596552149 697081481958616279606691)
                    ·
                      rfl

theorem cell23_4072684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_4072684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072684 prefixEnd_4072684 := by exact prefixLift 4072684
  have htrace : WordTrace (prefixWord ++ tailWord_4072684) baseStart_4072684 baseEnd_4072684 := by
    simpa [prefixWord, tailWord_4072684, baseEnd_4072684] using wordTrace_append hprefix tailTrace_4072684
  have hstable : (prefixWord ++ tailWord_4072684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072684).length < 2 ^ (prefixWord ++ tailWord_4072684).sum := by decide
  have hdescent : baseEnd_4072684 < baseStart_4072684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072704 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_4072704 : Nat := 118140960795 + 4072704 * 2 ^ 59
def prefixEnd_4072704 : Nat := 4983230072969 + 3 ^ 40 * 4072704 * 2
def baseEnd_4072704 : Nat := 2091254715488938760569981

theorem tailTrace_4072704 : CollatzResearch.WordTrace tailWord_4072704 prefixEnd_4072704 2091254715488938760569981 := by
  unfold tailWord_4072704
  simp only [CollatzResearch.WordTrace]
  refine ⟨74271859118648222655876583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99029145491530963541168777 74271859118648222655876583)
  ·
    refine ⟨111407788677972333983814875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74271859118648222655876583 111407788677972333983814875)
    ·
      refine ⟨167111683016958500975722313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111407788677972333983814875 167111683016958500975722313)
      ·
        refine ⟨125333762262718875731791735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167111683016958500975722313 125333762262718875731791735)
        ·
          refine ⟨188000643394078313597687603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125333762262718875731791735 188000643394078313597687603)
          ·
            refine ⟨282000965091117470396531405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188000643394078313597687603 282000965091117470396531405)
            ·
              refine ⟨105750361909169051398699277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282000965091117470396531405 105750361909169051398699277)
              ·
                refine ⟨39656385715938394274512229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105750361909169051398699277 39656385715938394274512229)
                ·
                  refine ⟨7435572321738448926471043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39656385715938394274512229 7435572321738448926471043)
                  ·
                    refine ⟨11153358482607673389706565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7435572321738448926471043 11153358482607673389706565)
                    ·
                      refine ⟨2091254715488938760569981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11153358482607673389706565 2091254715488938760569981)
                      ·
                        rfl

theorem cell23_4072704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_4072704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072704 prefixEnd_4072704 := by exact prefixLift 4072704
  have htrace : WordTrace (prefixWord ++ tailWord_4072704) baseStart_4072704 baseEnd_4072704 := by
    simpa [prefixWord, tailWord_4072704, baseEnd_4072704] using wordTrace_append hprefix tailTrace_4072704
  have hstable : (prefixWord ++ tailWord_4072704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072704).length < 2 ^ (prefixWord ++ tailWord_4072704).sum := by decide
  have hdescent : baseEnd_4072704 < baseStart_4072704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072721 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 2, 4, 2]
def baseStart_4072721 : Nat := 118140960795 + 4072721 * 2 ^ 59
def prefixEnd_4072721 : Nat := 4983230072969 + 3 ^ 40 * 4072721 * 2
def baseEnd_4072721 : Nat := 2091263444660065194057403

theorem tailTrace_4072721 : CollatzResearch.WordTrace tailWord_4072721 prefixEnd_4072721 2091263444660065194057403 := by
  unfold tailWord_4072721
  simp only [CollatzResearch.WordTrace]
  refine ⟨148544338278234857215122017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99029558852156571476748011 148544338278234857215122017)
  ·
    refine ⟨111408253708676142911341513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148544338278234857215122017 111408253708676142911341513)
    ·
      refine ⟨83556190281507107183506135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111408253708676142911341513 83556190281507107183506135)
      ·
        refine ⟨125334285422260660775259203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83556190281507107183506135 125334285422260660775259203)
        ·
          refine ⟨188001428133390991162888805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125334285422260660775259203 188001428133390991162888805)
          ·
            refine ⟨35250267775010810843041651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188001428133390991162888805 35250267775010810843041651)
            ·
              refine ⟨52875401662516216264562477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35250267775010810843041651 52875401662516216264562477)
              ·
                refine ⟨19828275623443581099210929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52875401662516216264562477 19828275623443581099210929)
                ·
                  refine ⟨14871206717582685824408197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19828275623443581099210929 14871206717582685824408197)
                  ·
                    refine ⟨2788351259546753592076537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14871206717582685824408197 2788351259546753592076537)
                    ·
                      refine ⟨2091263444660065194057403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788351259546753592076537 2091263444660065194057403)
                      ·
                        rfl

theorem cell23_4072721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_4072721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072721 prefixEnd_4072721 := by exact prefixLift 4072721
  have htrace : WordTrace (prefixWord ++ tailWord_4072721) baseStart_4072721 baseEnd_4072721 := by
    simpa [prefixWord, tailWord_4072721, baseEnd_4072721] using wordTrace_append hprefix tailTrace_4072721
  have hstable : (prefixWord ++ tailWord_4072721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072721).length < 2 ^ (prefixWord ++ tailWord_4072721).sum := by decide
  have hdescent : baseEnd_4072721 < baseStart_4072721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072741 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_4072741 : Nat := 118140960795 + 4072741 * 2 ^ 59
def prefixEnd_4072741 : Nat := 4983230072969 + 3 ^ 40 * 4072741 * 2
def baseEnd_4072741 : Nat := 2091273714273155115807311

theorem tailTrace_4072741 : CollatzResearch.WordTrace tailWord_4072741 prefixEnd_4072741 2091273714273155115807311 := by
  unfold tailWord_4072741
  simp only [CollatzResearch.WordTrace]
  refine ⟨148545067738162400630850077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99030045158774933753900051 148545067738162400630850077)
  ·
    refine ⟨55704400401810900236568779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148545067738162400630850077 55704400401810900236568779)
    ·
      refine ⟨83556600602716350354853169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55704400401810900236568779 83556600602716350354853169)
      ·
        refine ⟨62667450452037262766139877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83556600602716350354853169 62667450452037262766139877)
        ·
          refine ⟨11750146959756986768651227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62667450452037262766139877 11750146959756986768651227)
          ·
            refine ⟨17625220439635480152976841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750146959756986768651227 17625220439635480152976841)
            ·
              refine ⟨13218915329726610114732631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17625220439635480152976841 13218915329726610114732631)
              ·
                refine ⟨19828372994589915172098947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13218915329726610114732631 19828372994589915172098947)
                ·
                  refine ⟨29742559491884872758148421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19828372994589915172098947 29742559491884872758148421)
                  ·
                    refine ⟨5576729904728413642152829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29742559491884872758148421 5576729904728413642152829)
                    ·
                      refine ⟨2091273714273155115807311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5576729904728413642152829 2091273714273155115807311)
                      ·
                        rfl

theorem cell23_4072741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_4072741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072741 prefixEnd_4072741 := by exact prefixLift 4072741
  have htrace : WordTrace (prefixWord ++ tailWord_4072741) baseStart_4072741 baseEnd_4072741 := by
    simpa [prefixWord, tailWord_4072741, baseEnd_4072741] using wordTrace_append hprefix tailTrace_4072741
  have hstable : (prefixWord ++ tailWord_4072741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072741).length < 2 ^ (prefixWord ++ tailWord_4072741).sum := by decide
  have hdescent : baseEnd_4072741 < baseStart_4072741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072788 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_4072788 : Nat := 118140960795 + 4072788 * 2 ^ 59
def prefixEnd_4072788 : Nat := 4983230072969 + 3 ^ 40 * 4072788 * 2
def baseEnd_4072788 : Nat := 2091297847863916431919595

theorem tailTrace_4072788 : CollatzResearch.WordTrace tailWord_4072788 prefixEnd_4072788 2091297847863916431919595 := by
  unfold tailWord_4072788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74273390984496063828905509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99031187979328085105207345 74273390984496063828905509)
  ·
    refine ⟨13926260809593011967919783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74273390984496063828905509 13926260809593011967919783)
    ·
      refine ⟨20889391214389517951879675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13926260809593011967919783 20889391214389517951879675)
      ·
        refine ⟨31334086821584276927819513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20889391214389517951879675 31334086821584276927819513)
        ·
          refine ⟨23500565116188207695864635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31334086821584276927819513 23500565116188207695864635)
          ·
            refine ⟨35250847674282311543796953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23500565116188207695864635 35250847674282311543796953)
            ·
              refine ⟨26438135755711733657847715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35250847674282311543796953 26438135755711733657847715)
              ·
                refine ⟨39657203633567600486771573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26438135755711733657847715 39657203633567600486771573)
                ·
                  refine ⟨3717862840646962545634835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39657203633567600486771573 3717862840646962545634835)
                  ·
                    refine ⟨5576794260970443818452253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3717862840646962545634835 5576794260970443818452253)
                    ·
                      refine ⟨2091297847863916431919595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5576794260970443818452253 2091297847863916431919595)
                      ·
                        rfl

theorem cell23_4072788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_4072788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072788 prefixEnd_4072788 := by exact prefixLift 4072788
  have htrace : WordTrace (prefixWord ++ tailWord_4072788) baseStart_4072788 baseEnd_4072788 := by
    simpa [prefixWord, tailWord_4072788, baseEnd_4072788] using wordTrace_append hprefix tailTrace_4072788
  have hstable : (prefixWord ++ tailWord_4072788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072788).length < 2 ^ (prefixWord ++ tailWord_4072788).sum := by decide
  have hdescent : baseEnd_4072788 < baseStart_4072788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072791 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 3, 5]
def baseStart_4072791 : Nat := 118140960795 + 4072791 * 2 ^ 59
def prefixEnd_4072791 : Nat := 4983230072969 + 3 ^ 40 * 4072791 * 2
def baseEnd_4072791 : Nat := 697099796101959973394027

theorem tailTrace_4072791 : CollatzResearch.WordTrace tailWord_4072791 prefixEnd_4072791 697099796101959973394027 := by
  unfold tailWord_4072791
  simp only [CollatzResearch.WordTrace]
  refine ⟨148546891387981259170170227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99031260925320839446780151 148546891387981259170170227)
  ·
    refine ⟨222820337081971888755255341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148546891387981259170170227 222820337081971888755255341)
    ·
      refine ⟨83557626405739458283220753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222820337081971888755255341 83557626405739458283220753)
      ·
        refine ⟨62668219804304593712415565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83557626405739458283220753 62668219804304593712415565)
        ·
          refine ⟨23500582426614222642155837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62668219804304593712415565 23500582426614222642155837)
          ·
            refine ⟨8812718409980333490808439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23500582426614222642155837 8812718409980333490808439)
            ·
              refine ⟨13219077614970500236212659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812718409980333490808439 13219077614970500236212659)
              ·
                refine ⟨19828616422455750354318989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13219077614970500236212659 19828616422455750354318989)
                ·
                  refine ⟨7435731158420906382869621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19828616422455750354318989 7435731158420906382869621)
                  ·
                    refine ⟨697099796101959973394027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7435731158420906382869621 697099796101959973394027)
                    ·
                      rfl

theorem cell23_4072791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_4072791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072791 prefixEnd_4072791 := by exact prefixLift 4072791
  have htrace : WordTrace (prefixWord ++ tailWord_4072791) baseStart_4072791 baseEnd_4072791 := by
    simpa [prefixWord, tailWord_4072791, baseEnd_4072791] using wordTrace_append hprefix tailTrace_4072791
  have hstable : (prefixWord ++ tailWord_4072791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072791).length < 2 ^ (prefixWord ++ tailWord_4072791).sum := by decide
  have hdescent : baseEnd_4072791 < baseStart_4072791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072805 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 1, 1, 3]
def baseStart_4072805 : Nat := 118140960795 + 4072805 * 2 ^ 59
def prefixEnd_4072805 : Nat := 4983230072969 + 3 ^ 40 * 4072805 * 2
def baseEnd_4072805 : Nat := 2091306577035042865407017

theorem tailTrace_4072805 : CollatzResearch.WordTrace tailWord_4072805 prefixEnd_4072805 2091306577035042865407017 := by
  unfold tailWord_4072805
  simp only [CollatzResearch.WordTrace]
  refine ⟨148547402009930539561179869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99031601339953693040786579 148547402009930539561179869)
  ·
    refine ⟨55705275753723952335442451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148547402009930539561179869 55705275753723952335442451)
    ·
      refine ⟨83557913630585928503163677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55705275753723952335442451 83557913630585928503163677)
      ·
        refine ⟨31334217611469723188686379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83557913630585928503163677 31334217611469723188686379)
        ·
          refine ⟨47001326417204584783029569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31334217611469723188686379 47001326417204584783029569)
          ·
            refine ⟨35250994812903438587272177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47001326417204584783029569 35250994812903438587272177)
            ·
              refine ⟨26438246109677578940454133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35250994812903438587272177 26438246109677578940454133)
              ·
                refine ⟨2478585572782273025667575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26438246109677578940454133 2478585572782273025667575)
                ·
                  refine ⟨3717878359173409538501363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478585572782273025667575 3717878359173409538501363)
                  ·
                    refine ⟨5576817538760114307752045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3717878359173409538501363 5576817538760114307752045)
                    ·
                      refine ⟨2091306577035042865407017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5576817538760114307752045 2091306577035042865407017)
                      ·
                        rfl

theorem cell23_4072805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_4072805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072805 prefixEnd_4072805 := by exact prefixLift 4072805
  have htrace : WordTrace (prefixWord ++ tailWord_4072805) baseStart_4072805 baseEnd_4072805 := by
    simpa [prefixWord, tailWord_4072805, baseEnd_4072805] using wordTrace_append hprefix tailTrace_4072805
  have hstable : (prefixWord ++ tailWord_4072805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072805).length < 2 ^ (prefixWord ++ tailWord_4072805).sum := by decide
  have hdescent : baseEnd_4072805 < baseStart_4072805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072862 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4072862 : Nat := 118140960795 + 4072862 * 2 ^ 59
def prefixEnd_4072862 : Nat := 4983230072969 + 3 ^ 40 * 4072862 * 2
def baseEnd_4072862 : Nat := 2091335845432349142394255

theorem tailTrace_4072862 : CollatzResearch.WordTrace tailWord_4072862 prefixEnd_4072862 2091335845432349142394255 := by
  unfold tailWord_4072862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18568685121340504787000605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99032987313816025530669893 18568685121340504787000605)
  ·
    refine ⟨6963256920502689295125227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18568685121340504787000605 6963256920502689295125227)
    ·
      refine ⟨10444885380754033942687841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6963256920502689295125227 10444885380754033942687841)
      ·
        refine ⟨7833664035565525457015881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10444885380754033942687841 7833664035565525457015881)
        ·
          refine ⟨5875248026674144092761911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7833664035565525457015881 5875248026674144092761911)
          ·
            refine ⟨8812872040011216139142867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875248026674144092761911 8812872040011216139142867)
            ·
              refine ⟨13219308060016824208714301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812872040011216139142867 13219308060016824208714301)
              ·
                refine ⟨4957240522506309078267863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13219308060016824208714301 4957240522506309078267863)
                ·
                  refine ⟨7435860783759463617401795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957240522506309078267863 7435860783759463617401795)
                  ·
                    refine ⟨11153791175639195426102693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7435860783759463617401795 11153791175639195426102693)
                    ·
                      refine ⟨2091335845432349142394255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11153791175639195426102693 2091335845432349142394255)
                      ·
                        rfl

theorem cell23_4072862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4072862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072862 prefixEnd_4072862 := by exact prefixLift 4072862
  have htrace : WordTrace (prefixWord ++ tailWord_4072862) baseStart_4072862 baseEnd_4072862 := by
    simpa [prefixWord, tailWord_4072862, baseEnd_4072862] using wordTrace_append hprefix tailTrace_4072862
  have hstable : (prefixWord ++ tailWord_4072862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072862).length < 2 ^ (prefixWord ++ tailWord_4072862).sum := by decide
  have hdescent : baseEnd_4072862 < baseStart_4072862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072888 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 5, 3, 2]
def baseStart_4072888 : Nat := 118140960795 + 4072888 * 2 ^ 59
def prefixEnd_4072888 : Nat := 4983230072969 + 3 ^ 40 * 4072888 * 2
def baseEnd_4072888 : Nat := 2091349195929366040669135

theorem tailTrace_4072888 : CollatzResearch.WordTrace tailWord_4072888 prefixEnd_4072888 2091349195929366040669135 := by
  unfold tailWord_4072888
  simp only [CollatzResearch.WordTrace]
  refine ⟨74275214634314922368225659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99033619512419896490967545 74275214634314922368225659)
  ·
    refine ⟨111412821951472383552338489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74275214634314922368225659 111412821951472383552338489)
    ·
      refine ⟨83559616463604287664253867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111412821951472383552338489 83559616463604287664253867)
      ·
        refine ⟨125339424695406431496380801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83559616463604287664253867 125339424695406431496380801)
        ·
          refine ⟨94004568521554823622285601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125339424695406431496380801 94004568521554823622285601)
          ·
            refine ⟨70503426391166117716714201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94004568521554823622285601 70503426391166117716714201)
            ·
              refine ⟨52877569793374588287535651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70503426391166117716714201 52877569793374588287535651)
              ·
                refine ⟨79316354690061882431303477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52877569793374588287535651 79316354690061882431303477)
                ·
                  refine ⟨7435908252193301477934701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79316354690061882431303477 7435908252193301477934701)
                  ·
                    refine ⟨2788465594572488054225513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7435908252193301477934701 2788465594572488054225513)
                    ·
                      refine ⟨2091349195929366040669135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788465594572488054225513 2091349195929366040669135)
                      ·
                        rfl

theorem cell23_4072888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_4072888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072888 prefixEnd_4072888 := by exact prefixLift 4072888
  have htrace : WordTrace (prefixWord ++ tailWord_4072888) baseStart_4072888 baseEnd_4072888 := by
    simpa [prefixWord, tailWord_4072888, baseEnd_4072888] using wordTrace_append hprefix tailTrace_4072888
  have hstable : (prefixWord ++ tailWord_4072888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072888).length < 2 ^ (prefixWord ++ tailWord_4072888).sum := by decide
  have hdescent : baseEnd_4072888 < baseStart_4072888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072892 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4072892 : Nat := 118140960795 + 4072892 * 2 ^ 59
def prefixEnd_4072892 : Nat := 4983230072969 + 3 ^ 40 * 4072892 * 2
def baseEnd_4072892 : Nat := 2091351249851984025019117

theorem tailTrace_4072892 : CollatzResearch.WordTrace tailWord_4072892 prefixEnd_4072892 2091351249851984025019117 := by
  unfold tailWord_4072892
  simp only [CollatzResearch.WordTrace]
  refine ⟨74275287580307676709798465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99033716773743568946397953 74275287580307676709798465)
  ·
    refine ⟨55706465685230757532348849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74275287580307676709798465 55706465685230757532348849)
    ·
      refine ⟨41779849263923068149261637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55706465685230757532348849 41779849263923068149261637)
      ·
        refine ⟨7833721736985575277986557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41779849263923068149261637 7833721736985575277986557)
        ·
          refine ⟨2937645651369590729244959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7833721736985575277986557 2937645651369590729244959)
          ·
            refine ⟨4406468477054386093867439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937645651369590729244959 4406468477054386093867439)
            ·
              refine ⟨6609702715581579140801159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406468477054386093867439 6609702715581579140801159)
              ·
                refine ⟨9914554073372368711201739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609702715581579140801159 9914554073372368711201739)
                ·
                  refine ⟨14871831110058553066802609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914554073372368711201739 14871831110058553066802609)
                  ·
                    refine ⟨11153873332543914800101957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14871831110058553066802609 11153873332543914800101957)
                    ·
                      refine ⟨2091351249851984025019117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11153873332543914800101957 2091351249851984025019117)
                      ·
                        rfl

theorem cell23_4072892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4072892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072892 prefixEnd_4072892 := by exact prefixLift 4072892
  have htrace : WordTrace (prefixWord ++ tailWord_4072892) baseStart_4072892 baseEnd_4072892 := by
    simpa [prefixWord, tailWord_4072892, baseEnd_4072892] using wordTrace_append hprefix tailTrace_4072892
  have hstable : (prefixWord ++ tailWord_4072892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072892).length < 2 ^ (prefixWord ++ tailWord_4072892).sum := by decide
  have hdescent : baseEnd_4072892 < baseStart_4072892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072921 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_4072921 : Nat := 118140960795 + 4072921 * 2 ^ 59
def prefixEnd_4072921 : Nat := 4983230072969 + 3 ^ 40 * 4072921 * 2
def baseEnd_4072921 : Nat := 2091366140790964411556483

theorem tailTrace_4072921 : CollatzResearch.WordTrace tailWord_4072921 prefixEnd_4072921 2091366140790964411556483 := by
  unfold tailWord_4072921
  simp only [CollatzResearch.WordTrace]
  refine ⟨148551632877510291372402617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99034421918340194248268411 148551632877510291372402617)
  ·
    refine ⟨111413724658132718529301963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148551632877510291372402617 111413724658132718529301963)
    ·
      refine ⟨167120586987199077793952945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111413724658132718529301963 167120586987199077793952945)
      ·
        refine ⟨125340440240399308345464709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167120586987199077793952945 125340440240399308345464709)
        ·
          refine ⟨23501332545074870314774633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125340440240399308345464709 23501332545074870314774633)
          ·
            refine ⟨17625999408806152736080975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23501332545074870314774633 17625999408806152736080975)
            ·
              refine ⟨26438999113209229104121463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17625999408806152736080975 26438999113209229104121463)
              ·
                refine ⟨39658498669813843656182195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26438999113209229104121463 39658498669813843656182195)
                ·
                  refine ⟨59487748004720765484273293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39658498669813843656182195 59487748004720765484273293)
                  ·
                    refine ⟨22307905501770287056602485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59487748004720765484273293 22307905501770287056602485)
                    ·
                      refine ⟨2091366140790964411556483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22307905501770287056602485 2091366140790964411556483)
                      ·
                        rfl

theorem cell23_4072921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_4072921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072921 prefixEnd_4072921 := by exact prefixLift 4072921
  have htrace : WordTrace (prefixWord ++ tailWord_4072921) baseStart_4072921 baseEnd_4072921 := by
    simpa [prefixWord, tailWord_4072921, baseEnd_4072921] using wordTrace_append hprefix tailTrace_4072921
  have hstable : (prefixWord ++ tailWord_4072921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072921).length < 2 ^ (prefixWord ++ tailWord_4072921).sum := by decide
  have hdescent : baseEnd_4072921 < baseStart_4072921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072952 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 2, 2, 2]
def baseStart_4072952 : Nat := 118140960795 + 4072952 * 2 ^ 59
def prefixEnd_4072952 : Nat := 4983230072969 + 3 ^ 40 * 4072952 * 2
def baseEnd_4072952 : Nat := 2091382058691253790268841

theorem tailTrace_4072952 : CollatzResearch.WordTrace tailWord_4072952 prefixEnd_4072952 2091382058691253790268841 := by
  unfold tailWord_4072952
  simp only [CollatzResearch.WordTrace]
  refine ⟨74276381770198991833390555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99035175693598655777854073 74276381770198991833390555)
  ·
    refine ⟨111414572655298487750085833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74276381770198991833390555 111414572655298487750085833)
    ·
      refine ⟨83560929491473865812564375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111414572655298487750085833 83560929491473865812564375)
      ·
        refine ⟨125341394237210798718846563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83560929491473865812564375 125341394237210798718846563)
        ·
          refine ⟨188012091355816198078269845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125341394237210798718846563 188012091355816198078269845)
          ·
            refine ⟨8813066782303884284918899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188012091355816198078269845 8813066782303884284918899)
            ·
              refine ⟨13219600173455826427378349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813066782303884284918899 13219600173455826427378349)
              ·
                refine ⟨4957350065045934910266881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13219600173455826427378349 4957350065045934910266881)
                ·
                  refine ⟨3718012548784451182700161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957350065045934910266881 3718012548784451182700161)
                  ·
                    refine ⟨2788509411588338387025121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3718012548784451182700161 2788509411588338387025121)
                    ·
                      refine ⟨2091382058691253790268841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788509411588338387025121 2091382058691253790268841)
                      ·
                        rfl

theorem cell23_4072952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_4072952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072952 prefixEnd_4072952 := by exact prefixLift 4072952
  have htrace : WordTrace (prefixWord ++ tailWord_4072952) baseStart_4072952 baseEnd_4072952 := by
    simpa [prefixWord, tailWord_4072952, baseEnd_4072952] using wordTrace_append hprefix tailTrace_4072952
  have hstable : (prefixWord ++ tailWord_4072952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072952).length < 2 ^ (prefixWord ++ tailWord_4072952).sum := by decide
  have hdescent : baseEnd_4072952 < baseStart_4072952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072973 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4072973 : Nat := 118140960795 + 4072973 * 2 ^ 59
def prefixEnd_4072973 : Nat := 4983230072969 + 3 ^ 40 * 4072973 * 2
def baseEnd_4072973 : Nat := 2091392841784998208106245

theorem tailTrace_4072973 : CollatzResearch.WordTrace tailWord_4072973 prefixEnd_4072973 2091392841784998208106245 := by
  unfold tailWord_4072973
  simp only [CollatzResearch.WordTrace]
  refine ⟨148553529473321904253295573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99035686315547936168863715 148553529473321904253295573)
  ·
    refine ⟨3481723347030982130936615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 148553529473321904253295573 3481723347030982130936615)
    ·
      refine ⟨5222585020546473196404923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3481723347030982130936615 5222585020546473196404923)
      ·
        refine ⟨7833877530819709794607385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222585020546473196404923 7833877530819709794607385)
        ·
          refine ⟨5875408148114782345955539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7833877530819709794607385 5875408148114782345955539)
          ·
            refine ⟨8813112222172173518933309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875408148114782345955539 8813112222172173518933309)
            ·
              refine ⟨3304917083314565069599991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8813112222172173518933309 3304917083314565069599991)
              ·
                refine ⟨4957375624971847604399987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304917083314565069599991 4957375624971847604399987)
                ·
                  refine ⟨7436063437457771406599981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957375624971847604399987 7436063437457771406599981)
                  ·
                    refine ⟨2788523789046664277474993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7436063437457771406599981 2788523789046664277474993)
                    ·
                      refine ⟨2091392841784998208106245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788523789046664277474993 2091392841784998208106245)
                      ·
                        rfl

theorem cell23_4072973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4072973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072973 prefixEnd_4072973 := by exact prefixLift 4072973
  have htrace : WordTrace (prefixWord ++ tailWord_4072973) baseStart_4072973 baseEnd_4072973 := by
    simpa [prefixWord, tailWord_4072973, baseEnd_4072973] using wordTrace_append hprefix tailTrace_4072973
  have hstable : (prefixWord ++ tailWord_4072973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072973).length < 2 ^ (prefixWord ++ tailWord_4072973).sum := by decide
  have hdescent : baseEnd_4072973 < baseStart_4072973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072988 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_4072988 : Nat := 118140960795 + 4072988 * 2 ^ 59
def prefixEnd_4072988 : Nat := 4983230072969 + 3 ^ 40 * 4072988 * 2
def baseEnd_4072988 : Nat := 697133514664938549806225

theorem tailTrace_4072988 : CollatzResearch.WordTrace tailWord_4072988 prefixEnd_4072988 697133514664938549806225 := by
  unfold tailWord_4072988
  simp only [CollatzResearch.WordTrace]
  refine ⟨74277038284133780907545809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99036051045511707876727745 74277038284133780907545809)
  ·
    refine ⟨55707778713100335680659357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74277038284133780907545809 55707778713100335680659357)
    ·
      refine ⟨20890417017412625880247259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55707778713100335680659357 20890417017412625880247259)
      ·
        refine ⟨31335625526118938820370889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20890417017412625880247259 31335625526118938820370889)
        ·
          refine ⟨23501719144589204115278167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31335625526118938820370889 23501719144589204115278167)
          ·
            refine ⟨35252578716883806172917251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23501719144589204115278167 35252578716883806172917251)
            ·
              refine ⟨52878868075325709259375877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35252578716883806172917251 52878868075325709259375877)
              ·
                refine ⟨9914787764123570486132977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52878868075325709259375877 9914787764123570486132977)
                ·
                  refine ⟨7436090823092677864599733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9914787764123570486132977 7436090823092677864599733)
                  ·
                    refine ⟨697133514664938549806225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7436090823092677864599733 697133514664938549806225)
                    ·
                      rfl

theorem cell23_4072988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_4072988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072988 prefixEnd_4072988 := by exact prefixLift 4072988
  have htrace : WordTrace (prefixWord ++ tailWord_4072988) baseStart_4072988 baseEnd_4072988 := by
    simpa [prefixWord, tailWord_4072988, baseEnd_4072988] using wordTrace_append hprefix tailTrace_4072988
  have hstable : (prefixWord ++ tailWord_4072988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072988).length < 2 ^ (prefixWord ++ tailWord_4072988).sum := by decide
  have hdescent : baseEnd_4072988 < baseStart_4072988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072992 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 5]
def baseStart_4072992 : Nat := 118140960795 + 4072992 * 2 ^ 59
def prefixEnd_4072992 : Nat := 4983230072969 + 3 ^ 40 * 4072992 * 2
def baseEnd_4072992 : Nat := 232378066435270403752073

theorem tailTrace_4072992 : CollatzResearch.WordTrace tailWord_4072992 prefixEnd_4072992 232378066435270403752073 := by
  unfold tailWord_4072992
  simp only [CollatzResearch.WordTrace]
  refine ⟨74277111230126535249118615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99036148306835380332158153 74277111230126535249118615)
  ·
    refine ⟨111415666845189802873677923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74277111230126535249118615 111415666845189802873677923)
    ·
      refine ⟨167123500267784704310516885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111415666845189802873677923 167123500267784704310516885)
      ·
        refine ⟨7833914075052408014555479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167123500267784704310516885 7833914075052408014555479)
        ·
          refine ⟨11750871112578612021833219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833914075052408014555479 11750871112578612021833219)
          ·
            refine ⟨17626306668867918032749829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750871112578612021833219 17626306668867918032749829)
            ·
              refine ⟨3304932500412734631140593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17626306668867918032749829 3304932500412734631140593)
              ·
                refine ⟨2478699375309550973355445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3304932500412734631140593 2478699375309550973355445)
                ·
                  refine ⟨232378066435270403752073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478699375309550973355445 232378066435270403752073)
                  ·
                    rfl

theorem cell23_4072992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 5].length) (baseStart_4072992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4072992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4072992 prefixEnd_4072992 := by exact prefixLift 4072992
  have htrace : WordTrace (prefixWord ++ tailWord_4072992) baseStart_4072992 baseEnd_4072992 := by
    simpa [prefixWord, tailWord_4072992, baseEnd_4072992] using wordTrace_append hprefix tailTrace_4072992
  have hstable : (prefixWord ++ tailWord_4072992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072992).length < 2 ^ (prefixWord ++ tailWord_4072992).sum := by decide
  have hdescent : baseEnd_4072992 < baseStart_4072992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073025 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4073025 : Nat := 118140960795 + 4073025 * 2 ^ 59
def prefixEnd_4073025 : Nat := 4983230072969 + 3 ^ 40 * 4073025 * 2
def baseEnd_4073025 : Nat := 2091419542779032004656005

theorem tailTrace_4073025 : CollatzResearch.WordTrace tailWord_4073025 prefixEnd_4073025 2091419542779032004656005 := by
  unfold tailWord_4073025
  simp only [CollatzResearch.WordTrace]
  refine ⟨148555426069133517134188529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99036950712755678089459019 148555426069133517134188529)
  ·
    refine ⟨111416569551850137850641397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148555426069133517134188529 111416569551850137850641397)
    ·
      refine ⟨10445303395485950423497631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111416569551850137850641397 10445303395485950423497631)
      ·
        refine ⟨15667955093228925635246447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10445303395485950423497631 15667955093228925635246447)
        ·
          refine ⟨23501932639843388452869671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667955093228925635246447 23501932639843388452869671)
          ·
            refine ⟨35252898959765082679304507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23501932639843388452869671 35252898959765082679304507)
            ·
              refine ⟨52879348439647624018956761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35252898959765082679304507 52879348439647624018956761)
              ·
                refine ⟨39659511329735718014217571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52879348439647624018956761 39659511329735718014217571)
                ·
                  refine ⟨59489266994603577021326357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39659511329735718014217571 59489266994603577021326357)
                  ·
                    refine ⟨2788559390372042672874673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59489266994603577021326357 2788559390372042672874673)
                    ·
                      refine ⟨2091419542779032004656005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788559390372042672874673 2091419542779032004656005)
                      ·
                        rfl

theorem cell23_4073025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4073025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073025 prefixEnd_4073025 := by exact prefixLift 4073025
  have htrace : WordTrace (prefixWord ++ tailWord_4073025) baseStart_4073025 baseEnd_4073025 := by
    simpa [prefixWord, tailWord_4073025, baseEnd_4073025] using wordTrace_append hprefix tailTrace_4073025
  have hstable : (prefixWord ++ tailWord_4073025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073025).length < 2 ^ (prefixWord ++ tailWord_4073025).sum := by decide
  have hdescent : baseEnd_4073025 < baseStart_4073025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073052 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4073052 : Nat := 118140960795 + 4073052 * 2 ^ 59
def prefixEnd_4073052 : Nat := 4983230072969 + 3 ^ 40 * 4073052 * 2
def baseEnd_4073052 : Nat := 697144468918901133006127

theorem tailTrace_4073052 : CollatzResearch.WordTrace tailWord_4073052 prefixEnd_4073052 697144468918901133006127 := by
  unfold tailWord_4073052
  simp only [CollatzResearch.WordTrace]
  refine ⟨74278205420017850372710705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99037607226690467163614273 74278205420017850372710705)
  ·
    refine ⟨55708654065013387779533029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74278205420017850372710705 55708654065013387779533029)
    ·
      refine ⟨10445372637190010208662443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55708654065013387779533029 10445372637190010208662443)
      ·
        refine ⟨15668058955785015312993665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10445372637190010208662443 15668058955785015312993665)
        ·
          refine ⟨11751044216838761484745249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15668058955785015312993665 11751044216838761484745249)
          ·
            refine ⟨8813283162629071113558937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11751044216838761484745249 8813283162629071113558937)
            ·
              refine ⟨6609962371971803335169203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8813283162629071113558937 6609962371971803335169203)
              ·
                refine ⟨9914943557957705002753805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609962371971803335169203 9914943557957705002753805)
                ·
                  refine ⟨3718103834234139376032677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9914943557957705002753805 3718103834234139376032677)
                  ·
                    refine ⟨697144468918901133006127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3718103834234139376032677 697144468918901133006127)
                    ·
                      rfl

theorem cell23_4073052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4073052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073052 prefixEnd_4073052 := by exact prefixLift 4073052
  have htrace : WordTrace (prefixWord ++ tailWord_4073052) baseStart_4073052 baseEnd_4073052 := by
    simpa [prefixWord, tailWord_4073052, baseEnd_4073052] using wordTrace_append hprefix tailTrace_4073052
  have hstable : (prefixWord ++ tailWord_4073052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073052).length < 2 ^ (prefixWord ++ tailWord_4073052).sum := by decide
  have hdescent : baseEnd_4073052 < baseStart_4073052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073095 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 1, 5]
def baseStart_4073095 : Nat := 118140960795 + 4073095 * 2 ^ 59
def prefixEnd_4073095 : Nat := 4983230072969 + 3 ^ 40 * 4073095 * 2
def baseEnd_4073095 : Nat := 697151828808282243593561

theorem tailTrace_4073095 : CollatzResearch.WordTrace tailWord_4073095 prefixEnd_4073095 697151828808282243593561 := by
  unfold tailWord_4073095
  simp only [CollatzResearch.WordTrace]
  refine ⟨148557979178879919089236739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99038652785919946059491159 148557979178879919089236739)
  ·
    refine ⟨222836968768319878633855109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148557979178879919089236739 222836968768319878633855109)
    ·
      refine ⟨41781931644059977243847833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222836968768319878633855109 41781931644059977243847833)
      ·
        refine ⟨31336448733044982932885875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41781931644059977243847833 31336448733044982932885875)
        ·
          refine ⟨47004673099567474399328813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31336448733044982932885875 47004673099567474399328813)
          ·
            refine ⟨17626752412337802899748305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47004673099567474399328813 17626752412337802899748305)
            ·
              refine ⟨13220064309253352174811229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17626752412337802899748305 13220064309253352174811229)
              ·
                refine ⟨4957524115970007065554211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13220064309253352174811229 4957524115970007065554211)
                ·
                  refine ⟨7436286173955010598331317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957524115970007065554211 7436286173955010598331317)
                  ·
                    refine ⟨697151828808282243593561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7436286173955010598331317 697151828808282243593561)
                    ·
                      rfl

theorem cell23_4073095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_4073095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073095 prefixEnd_4073095 := by exact prefixLift 4073095
  have htrace : WordTrace (prefixWord ++ tailWord_4073095) baseStart_4073095 baseEnd_4073095 := by
    simpa [prefixWord, tailWord_4073095, baseEnd_4073095] using wordTrace_append hprefix tailTrace_4073095
  have hstable : (prefixWord ++ tailWord_4073095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073095).length < 2 ^ (prefixWord ++ tailWord_4073095).sum := by decide
  have hdescent : baseEnd_4073095 < baseStart_4073095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073102 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_4073102 : Nat := 118140960795 + 4073102 * 2 ^ 59
def prefixEnd_4073102 : Nat := 4983230072969 + 3 ^ 40 * 4073102 * 2
def baseEnd_4073102 : Nat := 2091459080789428203393151

theorem tailTrace_4073102 : CollatzResearch.WordTrace tailWord_4073102 prefixEnd_4073102 2091459080789428203393151 := by
  unfold tailWord_4073102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18569779311231819910592695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99038822993236372856494373 18569779311231819910592695)
  ·
    refine ⟨27854668966847729865889043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18569779311231819910592695 27854668966847729865889043)
    ·
      refine ⟨41782003450271594798833565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27854668966847729865889043 41782003450271594798833565)
      ·
        refine ⟨15668251293851848049562587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41782003450271594798833565 15668251293851848049562587)
        ·
          refine ⟨23502376940777772074343881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15668251293851848049562587 23502376940777772074343881)
          ·
            refine ⟨17626782705583329055757911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23502376940777772074343881 17626782705583329055757911)
            ·
              refine ⟨26440174058374993583636867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626782705583329055757911 26440174058374993583636867)
              ·
                refine ⟨39660261087562490375455301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26440174058374993583636867 39660261087562490375455301)
                ·
                  refine ⟨7436298953917966945397869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39660261087562490375455301 7436298953917966945397869)
                  ·
                    refine ⟨2788612107719237604524201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7436298953917966945397869 2788612107719237604524201)
                    ·
                      refine ⟨2091459080789428203393151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788612107719237604524201 2091459080789428203393151)
                      ·
                        rfl

theorem cell23_4073102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_4073102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073102 prefixEnd_4073102 := by exact prefixLift 4073102
  have htrace : WordTrace (prefixWord ++ tailWord_4073102) baseStart_4073102 baseEnd_4073102 := by
    simpa [prefixWord, tailWord_4073102, baseEnd_4073102] using wordTrace_append hprefix tailTrace_4073102
  have hstable : (prefixWord ++ tailWord_4073102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073102).length < 2 ^ (prefixWord ++ tailWord_4073102).sum := by decide
  have hdescent : baseEnd_4073102 < baseStart_4073102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073135 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_4073135 : Nat := 118140960795 + 4073135 * 2 ^ 59
def prefixEnd_4073135 : Nat := 4983230072969 + 3 ^ 40 * 4073135 * 2
def baseEnd_4073135 : Nat := 2091476025651026574280499

theorem tailTrace_4073135 : CollatzResearch.WordTrace tailWord_4073135 prefixEnd_4073135 2091476025651026574280499 := by
  unfold tailWord_4073135
  simp only [CollatzResearch.WordTrace]
  refine ⟨148559438098735005920692859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99039625399156670613795239 148559438098735005920692859)
  ·
    refine ⟨222839157148102508881039289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148559438098735005920692859 222839157148102508881039289)
    ·
      refine ⟨167129367861076881660779467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222839157148102508881039289 167129367861076881660779467)
      ·
        refine ⟨250694051791615322491169201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167129367861076881660779467 250694051791615322491169201)
        ·
          refine ⟨188020538843711491868376901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250694051791615322491169201 188020538843711491868376901)
          ·
            refine ⟨35253851033195904725320669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188020538843711491868376901 35253851033195904725320669)
            ·
              refine ⟨13220194137448464271995251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35253851033195904725320669 13220194137448464271995251)
              ·
                refine ⟨19830291206172696407992877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220194137448464271995251 19830291206172696407992877)
                ·
                  refine ⟨7436359202314761152997329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19830291206172696407992877 7436359202314761152997329)
                  ·
                    refine ⟨5577269401736070864747997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7436359202314761152997329 5577269401736070864747997)
                    ·
                      refine ⟨2091476025651026574280499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5577269401736070864747997 2091476025651026574280499)
                      ·
                        rfl

theorem cell23_4073135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_4073135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073135 prefixEnd_4073135 := by exact prefixLift 4073135
  have htrace : WordTrace (prefixWord ++ tailWord_4073135) baseStart_4073135 baseEnd_4073135 := by
    simpa [prefixWord, tailWord_4073135, baseEnd_4073135] using wordTrace_append hprefix tailTrace_4073135
  have hstable : (prefixWord ++ tailWord_4073135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073135).length < 2 ^ (prefixWord ++ tailWord_4073135).sum := by decide
  have hdescent : baseEnd_4073135 < baseStart_4073135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073138 : List Nat := [3, 2, 1, 1, 1, 2, 4, 9]
def baseStart_4073138 : Nat := 118140960795 + 4073138 * 2 ^ 59
def prefixEnd_4073138 : Nat := 4983230072969 + 3 ^ 40 * 4073138 * 2
def baseEnd_4073138 : Nat := 77462132077518150464555

theorem tailTrace_4073138 : CollatzResearch.WordTrace tailWord_4073138 prefixEnd_4073138 77462132077518150464555 := by
  unfold tailWord_4073138
  simp only [CollatzResearch.WordTrace]
  refine ⟨37139886879431034358263017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99039698345149424955368045 37139886879431034358263017)
  ·
    refine ⟨27854915159573275768697263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37139886879431034358263017 27854915159573275768697263)
    ·
      refine ⟨41782372739359913653045895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27854915159573275768697263 41782372739359913653045895)
      ·
        refine ⟨62673559109039870479568843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41782372739359913653045895 62673559109039870479568843)
        ·
          refine ⟨94010338663559805719353265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62673559109039870479568843 94010338663559805719353265)
          ·
            refine ⟨70507753997669854289514949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94010338663559805719353265 70507753997669854289514949)
            ·
              refine ⟨13220203874563097679284053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70507753997669854289514949 13220203874563097679284053)
              ·
                refine ⟨77462132077518150464555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13220203874563097679284053 77462132077518150464555)
                ·
                  rfl

theorem cell23_4073138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_4073138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073138 prefixEnd_4073138 := by exact prefixLift 4073138
  have htrace : WordTrace (prefixWord ++ tailWord_4073138) baseStart_4073138 baseEnd_4073138 := by
    simpa [prefixWord, tailWord_4073138, baseEnd_4073138] using wordTrace_append hprefix tailTrace_4073138
  have hstable : (prefixWord ++ tailWord_4073138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073138).length < 2 ^ (prefixWord ++ tailWord_4073138).sum := by decide
  have hdescent : baseEnd_4073138 < baseStart_4073138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073142 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4073142 : Nat := 118140960795 + 4073142 * 2 ^ 59
def prefixEnd_4073142 : Nat := 4983230072969 + 3 ^ 40 * 4073142 * 2
def baseEnd_4073142 : Nat := 697159873338536015630989

theorem tailTrace_4073142 : CollatzResearch.WordTrace tailWord_4073142 prefixEnd_4073142 697159873338536015630989 := by
  unfold tailWord_4073142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284980838106852882262355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99039795606473097410798453 9284980838106852882262355)
  ·
    refine ⟨13927471257160279323393533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9284980838106852882262355 13927471257160279323393533)
    ·
      refine ⟨5222801721435104746272575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13927471257160279323393533 5222801721435104746272575)
      ·
        refine ⟨7834202582152657119408863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222801721435104746272575 7834202582152657119408863)
        ·
          refine ⟨11751303873228985679113295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7834202582152657119408863 11751303873228985679113295)
          ·
            refine ⟨17626955809843478518669943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11751303873228985679113295 17626955809843478518669943)
            ·
              refine ⟨26440433714765217778004915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626955809843478518669943 26440433714765217778004915)
              ·
                refine ⟨39660650572147826667007373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26440433714765217778004915 39660650572147826667007373)
                ·
                  refine ⟨14872743964555435000127765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39660650572147826667007373 14872743964555435000127765)
                  ·
                    refine ⟨697159873338536015630989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14872743964555435000127765 697159873338536015630989)
                    ·
                      rfl

theorem cell23_4073142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4073142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073142 prefixEnd_4073142 := by exact prefixLift 4073142
  have htrace : WordTrace (prefixWord ++ tailWord_4073142) baseStart_4073142 baseEnd_4073142 := by
    simpa [prefixWord, tailWord_4073142, baseEnd_4073142] using wordTrace_append hprefix tailTrace_4073142
  have hstable : (prefixWord ++ tailWord_4073142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073142).length < 2 ^ (prefixWord ++ tailWord_4073142).sum := by decide
  have hdescent : baseEnd_4073142 < baseStart_4073142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073166 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_4073166 : Nat := 118140960795 + 4073166 * 2 ^ 59
def prefixEnd_4073166 : Nat := 4983230072969 + 3 ^ 40 * 4073166 * 2
def baseEnd_4073166 : Nat := 2091491943551315952992857

theorem tailTrace_4073166 : CollatzResearch.WordTrace tailWord_4073166 prefixEnd_4073166 2091491943551315952992857 := by
  unfold tailWord_4073166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18570071095202837276883919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99040379174415132143380901 18570071095202837276883919)
  ·
    refine ⟨27855106642804255915325879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18570071095202837276883919 27855106642804255915325879)
    ·
      refine ⟨41782659964206383872988819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27855106642804255915325879 41782659964206383872988819)
      ·
        refine ⟨62673989946309575809483229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41782659964206383872988819 62673989946309575809483229)
        ·
          refine ⟨23502746229866090928556211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62673989946309575809483229 23502746229866090928556211)
          ·
            refine ⟨35254119344799136392834317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23502746229866090928556211 35254119344799136392834317)
            ·
              refine ⟨13220294754299676147312869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35254119344799136392834317 13220294754299676147312869)
              ·
                refine ⟨2478805266431189277621163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13220294754299676147312869 2478805266431189277621163)
                ·
                  refine ⟨3718207899646783916431745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478805266431189277621163 3718207899646783916431745)
                  ·
                    refine ⟨2788655924735087937323809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3718207899646783916431745 2788655924735087937323809)
                    ·
                      refine ⟨2091491943551315952992857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788655924735087937323809 2091491943551315952992857)
                      ·
                        rfl

theorem cell23_4073166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_4073166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073166 prefixEnd_4073166 := by exact prefixLift 4073166
  have htrace : WordTrace (prefixWord ++ tailWord_4073166) baseStart_4073166 baseEnd_4073166 := by
    simpa [prefixWord, tailWord_4073166, baseEnd_4073166] using wordTrace_append hprefix tailTrace_4073166
  have hstable : (prefixWord ++ tailWord_4073166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073166).length < 2 ^ (prefixWord ++ tailWord_4073166).sum := by decide
  have hdescent : baseEnd_4073166 < baseStart_4073166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073172 : List Nat := [2, 4, 1, 3, 1, 3, 1, 8]
def baseStart_4073172 : Nat := 118140960795 + 4073172 * 2 ^ 59
def prefixEnd_4073172 : Nat := 4983230072969 + 3 ^ 40 * 4073172 * 2
def baseEnd_4073172 : Nat := 77462778682786775167327

theorem tailTrace_4073172 : CollatzResearch.WordTrace tailWord_4073172 prefixEnd_4073172 77462778682786775167327 := by
  unfold tailWord_4073172
  simp only [CollatzResearch.WordTrace]
  refine ⟨74280393799800480619894885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99040525066400640826526513 74280393799800480619894885)
  ·
    refine ⟨13927573837462590116230291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74280393799800480619894885 13927573837462590116230291)
    ·
      refine ⟨20891360756193885174345437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13927573837462590116230291 20891360756193885174345437)
      ·
        refine ⟨7834260283572706940379539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20891360756193885174345437 7834260283572706940379539)
        ·
          refine ⟨11751390425359060410569309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7834260283572706940379539 11751390425359060410569309)
          ·
            refine ⟨4406771409509647653963491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11751390425359060410569309 4406771409509647653963491)
            ·
              refine ⟨6610157114264471480945237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406771409509647653963491 6610157114264471480945237)
              ·
                refine ⟨77462778682786775167327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6610157114264471480945237 77462778682786775167327)
                ·
                  rfl

theorem cell23_4073172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 8].length) (baseStart_4073172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073172 prefixEnd_4073172 := by exact prefixLift 4073172
  have htrace : WordTrace (prefixWord ++ tailWord_4073172) baseStart_4073172 baseEnd_4073172 := by
    simpa [prefixWord, tailWord_4073172, baseEnd_4073172] using wordTrace_append hprefix tailTrace_4073172
  have hstable : (prefixWord ++ tailWord_4073172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073172).length < 2 ^ (prefixWord ++ tailWord_4073172).sum := by decide
  have hdescent : baseEnd_4073172 < baseStart_4073172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073239 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 1, 4, 2]
def baseStart_4073239 : Nat := 118140960795 + 4073239 * 2 ^ 59
def prefixEnd_4073239 : Nat := 4983230072969 + 3 ^ 40 * 4073239 * 2
def baseEnd_4073239 : Nat := 2091529427639094167380021

theorem tailTrace_4073239 : CollatzResearch.WordTrace tailWord_4073239 prefixEnd_4073239 2091529427639094167380021 := by
  unfold tailWord_4073239
  simp only [CollatzResearch.WordTrace]
  refine ⟨148563231290358231682478771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99042154193572154454985847 148563231290358231682478771)
  ·
    refine ⟨222844846935537347523718157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148563231290358231682478771 222844846935537347523718157)
    ·
      refine ⟨83566817600826505321394309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222844846935537347523718157 83566817600826505321394309)
      ·
        refine ⟨15668778300154969747761433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83566817600826505321394309 15668778300154969747761433)
        ·
          refine ⟨11751583725116227310821075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15668778300154969747761433 11751583725116227310821075)
          ·
            refine ⟨17627375587674340966231613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11751583725116227310821075 17627375587674340966231613)
            ·
              refine ⟨6610265845377877862336855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17627375587674340966231613 6610265845377877862336855)
              ·
                refine ⟨9915398768066816793505283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610265845377877862336855 9915398768066816793505283)
                ·
                  refine ⟨14873098152100225190257925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915398768066816793505283 14873098152100225190257925)
                  ·
                    refine ⟨2788705903518792223173361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14873098152100225190257925 2788705903518792223173361)
                    ·
                      refine ⟨2091529427639094167380021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788705903518792223173361 2091529427639094167380021)
                      ·
                        rfl

theorem cell23_4073239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_4073239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073239 prefixEnd_4073239 := by exact prefixLift 4073239
  have htrace : WordTrace (prefixWord ++ tailWord_4073239) baseStart_4073239 baseEnd_4073239 := by
    simpa [prefixWord, tailWord_4073239, baseEnd_4073239] using wordTrace_append hprefix tailTrace_4073239
  have hstable : (prefixWord ++ tailWord_4073239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073239).length < 2 ^ (prefixWord ++ tailWord_4073239).sum := by decide
  have hdescent : baseEnd_4073239 < baseStart_4073239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073279 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 7]
def baseStart_4073279 : Nat := 118140960795 + 4073279 * 2 ^ 59
def prefixEnd_4073279 : Nat := 4983230072969 + 3 ^ 40 * 4073279 * 2
def baseEnd_4073279 : Nat := 232394440762808223431093

theorem tailTrace_4073279 : CollatzResearch.WordTrace tailWord_4073279 prefixEnd_4073279 232394440762808223431093 := by
  unfold tailWord_4073279
  simp only [CollatzResearch.WordTrace]
  refine ⟨148564690210213318513934891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99043126806808879009289927 148564690210213318513934891)
  ·
    refine ⟨222847035315319977770902337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148564690210213318513934891 222847035315319977770902337)
    ·
      refine ⟨167135276486489983328176753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222847035315319977770902337 167135276486489983328176753)
      ·
        refine ⟨125351457364867487496132565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167135276486489983328176753 125351457364867487496132565)
        ·
          refine ⟨2937924781989081738190607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125351457364867487496132565 2937924781989081738190607)
          ·
            refine ⟨4406887172983622607285911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937924781989081738190607 4406887172983622607285911)
            ·
              refine ⟨6610330759475433910928867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406887172983622607285911 6610330759475433910928867)
              ·
                refine ⟨9915496139213150866393301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610330759475433910928867 9915496139213150866393301)
                ·
                  refine ⟨232394440762808223431093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9915496139213150866393301 232394440762808223431093)
                  ·
                    rfl

theorem cell23_4073279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 7].length) (baseStart_4073279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073279 prefixEnd_4073279 := by exact prefixLift 4073279
  have htrace : WordTrace (prefixWord ++ tailWord_4073279) baseStart_4073279 baseEnd_4073279 := by
    simpa [prefixWord, tailWord_4073279, baseEnd_4073279] using wordTrace_append hprefix tailTrace_4073279
  have hstable : (prefixWord ++ tailWord_4073279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073279).length < 2 ^ (prefixWord ++ tailWord_4073279).sum := by decide
  have hdescent : baseEnd_4073279 < baseStart_4073279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073285 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_4073285 : Nat := 118140960795 + 4073285 * 2 ^ 59
def prefixEnd_4073285 : Nat := 4983230072969 + 3 ^ 40 * 4073285 * 2
def baseEnd_4073285 : Nat := 2091553047749200987404809

theorem tailTrace_4073285 : CollatzResearch.WordTrace tailWord_4073285 prefixEnd_4073285 2091553047749200987404809 := by
  unfold tailWord_4073285
  simp only [CollatzResearch.WordTrace]
  refine ⟨148564909048191581538653309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99043272698794387692435539 148564909048191581538653309)
  ·
    refine ⟨55711840893071843076994991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148564909048191581538653309 55711840893071843076994991)
    ·
      refine ⟨83567761339607764615492487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55711840893071843076994991 83567761339607764615492487)
      ·
        refine ⟨125351642009411646923238731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83567761339607764615492487 125351642009411646923238731)
        ·
          refine ⟨188027463014117470384858097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125351642009411646923238731 188027463014117470384858097)
          ·
            refine ⟨141020597260588102788643573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188027463014117470384858097 141020597260588102788643573)
            ·
              refine ⟨13220680993180134636435335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141020597260588102788643573 13220680993180134636435335)
              ·
                refine ⟨19831021489770201954653003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220680993180134636435335 19831021489770201954653003)
                ·
                  refine ⟨29746532234655302931979505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19831021489770201954653003 29746532234655302931979505)
                  ·
                    refine ⟨22309899175991477198984629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29746532234655302931979505 22309899175991477198984629)
                    ·
                      refine ⟨2091553047749200987404809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22309899175991477198984629 2091553047749200987404809)
                      ·
                        rfl

theorem cell23_4073285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_4073285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073285 prefixEnd_4073285 := by exact prefixLift 4073285
  have htrace : WordTrace (prefixWord ++ tailWord_4073285) baseStart_4073285 baseEnd_4073285 := by
    simpa [prefixWord, tailWord_4073285, baseEnd_4073285] using wordTrace_append hprefix tailTrace_4073285
  have hstable : (prefixWord ++ tailWord_4073285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073285).length < 2 ^ (prefixWord ++ tailWord_4073285).sum := by decide
  have hdescent : baseEnd_4073285 < baseStart_4073285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073312 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_4073312 : Nat := 118140960795 + 4073312 * 2 ^ 59
def prefixEnd_4073312 : Nat := 4983230072969 + 3 ^ 40 * 4073312 * 2
def baseEnd_4073312 : Nat := 2091566911726872381767185

theorem tailTrace_4073312 : CollatzResearch.WordTrace tailWord_4073312 prefixEnd_4073312 2091566911726872381767185 := by
  unfold tailWord_4073312
  simp only [CollatzResearch.WordTrace]
  refine ⟨74282946909546882574943095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99043929212729176766590793 74282946909546882574943095)
  ·
    refine ⟨111424420364320323862414643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74282946909546882574943095 111424420364320323862414643)
    ·
      refine ⟨167136630546480485793621965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111424420364320323862414643 167136630546480485793621965)
      ·
        refine ⟨62676236454930182172608237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167136630546480485793621965 62676236454930182172608237)
        ·
          refine ⟨23503588670598818314728089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62676236454930182172608237 23503588670598818314728089)
          ·
            refine ⟨17627691502949113736046067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23503588670598818314728089 17627691502949113736046067)
            ·
              refine ⟨26441537254423670604069101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17627691502949113736046067 26441537254423670604069101)
              ·
                refine ⟨9915576470408876476525913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26441537254423670604069101 9915576470408876476525913)
                ·
                  refine ⟨7436682352806657357394435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9915576470408876476525913 7436682352806657357394435)
                  ·
                    refine ⟨11155023529209986036091653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436682352806657357394435 11155023529209986036091653)
                    ·
                      refine ⟨2091566911726872381767185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11155023529209986036091653 2091566911726872381767185)
                      ·
                        rfl

theorem cell23_4073312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_4073312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073312 prefixEnd_4073312 := by exact prefixLift 4073312
  have htrace : WordTrace (prefixWord ++ tailWord_4073312) baseStart_4073312 baseEnd_4073312 := by
    simpa [prefixWord, tailWord_4073312, baseEnd_4073312] using wordTrace_append hprefix tailTrace_4073312
  have hstable : (prefixWord ++ tailWord_4073312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073312).length < 2 ^ (prefixWord ++ tailWord_4073312).sum := by decide
  have hdescent : baseEnd_4073312 < baseStart_4073312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073390 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4073390 : Nat := 118140960795 + 4073390 * 2 ^ 59
def prefixEnd_4073390 : Nat := 4983230072969 + 3 ^ 40 * 4073390 * 2
def baseEnd_4073390 : Nat := 697202321072641025530609

theorem tailTrace_4073390 : CollatzResearch.WordTrace tailWord_4073390 prefixEnd_4073390 697202321072641025530609 := by
  unfold tailWord_4073390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571092339101398058903203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99045825808540789647483749 18571092339101398058903203)
  ·
    refine ⟨27856638508652097088354805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18571092339101398058903203 27856638508652097088354805)
    ·
      refine ⟨2611559860186134102033263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27856638508652097088354805 2611559860186134102033263)
      ·
        refine ⟨3917339790279201153049895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611559860186134102033263 3917339790279201153049895)
        ·
          refine ⟨5876009685418801729574843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917339790279201153049895 5876009685418801729574843)
          ·
            refine ⟨8814014528128202594362265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876009685418801729574843 8814014528128202594362265)
            ·
              refine ⟨6610510896096151945771699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814014528128202594362265 6610510896096151945771699)
              ·
                refine ⟨9915766344144227918657549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610510896096151945771699 9915766344144227918657549)
                ·
                  refine ⟨3718412379054085469496581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9915766344144227918657549 3718412379054085469496581)
                  ·
                    refine ⟨697202321072641025530609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3718412379054085469496581 697202321072641025530609)
                    ·
                      rfl

theorem cell23_4073390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4073390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073390 prefixEnd_4073390 := by exact prefixLift 4073390
  have htrace : WordTrace (prefixWord ++ tailWord_4073390) baseStart_4073390 baseEnd_4073390 := by
    simpa [prefixWord, tailWord_4073390, baseEnd_4073390] using wordTrace_append hprefix tailTrace_4073390
  have hstable : (prefixWord ++ tailWord_4073390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073390).length < 2 ^ (prefixWord ++ tailWord_4073390).sum := by decide
  have hdescent : baseEnd_4073390 < baseStart_4073390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073402 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_4073402 : Nat := 118140960795 + 4073402 * 2 ^ 59
def prefixEnd_4073402 : Nat := 4983230072969 + 3 ^ 40 * 4073402 * 2
def baseEnd_4073402 : Nat := 2091613124985777029641771

theorem tailTrace_4073402 : CollatzResearch.WordTrace tailWord_4073402 prefixEnd_4073402 2091613124985777029641771 := by
  unfold tailWord_4073402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37142294097191927630165615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99046117592511807013774973 37142294097191927630165615)
  ·
    refine ⟨55713441145787891445248423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37142294097191927630165615 55713441145787891445248423)
    ·
      refine ⟨83570161718681837167872635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55713441145787891445248423 83570161718681837167872635)
      ·
        refine ⟨125355242578022755751808953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83570161718681837167872635 125355242578022755751808953)
        ·
          refine ⟨94016431933517066813856715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125355242578022755751808953 94016431933517066813856715)
          ·
            refine ⟨141024647900275600220785073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94016431933517066813856715 141024647900275600220785073)
            ·
              refine ⟨105768485925206700165588805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141024647900275600220785073 105768485925206700165588805)
              ·
                refine ⟨19831591110976256281047901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105768485925206700165588805 19831591110976256281047901)
                ·
                  refine ⟨7436846666616096105392963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19831591110976256281047901 7436846666616096105392963)
                  ·
                    refine ⟨11155269999924144158089445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436846666616096105392963 11155269999924144158089445)
                    ·
                      refine ⟨2091613124985777029641771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11155269999924144158089445 2091613124985777029641771)
                      ·
                        rfl

theorem cell23_4073402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_4073402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073402 prefixEnd_4073402 := by exact prefixLift 4073402
  have htrace : WordTrace (prefixWord ++ tailWord_4073402) baseStart_4073402 baseEnd_4073402 := by
    simpa [prefixWord, tailWord_4073402, baseEnd_4073402] using wordTrace_append hprefix tailTrace_4073402
  have hstable : (prefixWord ++ tailWord_4073402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073402).length < 2 ^ (prefixWord ++ tailWord_4073402).sum := by decide
  have hdescent : baseEnd_4073402 < baseStart_4073402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073419 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 4]
def baseStart_4073419 : Nat := 118140960795 + 4073419 * 2 ^ 59
def prefixEnd_4073419 : Nat := 4983230072969 + 3 ^ 40 * 4073419 * 2
def baseEnd_4073419 : Nat := 2091621854156903463129193

theorem tailTrace_4073419 : CollatzResearch.WordTrace tailWord_4073419 prefixEnd_4073419 2091621854156903463129193 := by
  unfold tailWord_4073419
  simp only [CollatzResearch.WordTrace]
  refine ⟨148569796429706122424031311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99046530953137414949354207 148569796429706122424031311)
  ·
    refine ⟨222854694644559183636046967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148569796429706122424031311 222854694644559183636046967)
    ·
      refine ⟨334282041966838775454070451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222854694644559183636046967 334282041966838775454070451)
      ·
        refine ⟨501423062950258163181105677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334282041966838775454070451 501423062950258163181105677)
        ·
          refine ⟨188033648606346811192914629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501423062950258163181105677 188033648606346811192914629)
          ·
            refine ⟨35256309113690027098671493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188033648606346811192914629 35256309113690027098671493)
            ·
              refine ⟨6610557958816880081000905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35256309113690027098671493 6610557958816880081000905)
              ·
                refine ⟨4957918469112660060750679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6610557958816880081000905 4957918469112660060750679)
                ·
                  refine ⟨7436877703668990091126019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957918469112660060750679 7436877703668990091126019)
                  ·
                    refine ⟨11155316555503485136689029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436877703668990091126019 11155316555503485136689029)
                    ·
                      refine ⟨2091621854156903463129193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11155316555503485136689029 2091621854156903463129193)
                      ·
                        rfl

theorem cell23_4073419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 4].length) (baseStart_4073419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073419 prefixEnd_4073419 := by exact prefixLift 4073419
  have htrace : WordTrace (prefixWord ++ tailWord_4073419) baseStart_4073419 baseEnd_4073419 := by
    simpa [prefixWord, tailWord_4073419, baseEnd_4073419] using wordTrace_append hprefix tailTrace_4073419
  have hstable : (prefixWord ++ tailWord_4073419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073419).length < 2 ^ (prefixWord ++ tailWord_4073419).sum := by decide
  have hdescent : baseEnd_4073419 < baseStart_4073419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073422 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_4073422 : Nat := 118140960795 + 4073422 * 2 ^ 59
def prefixEnd_4073422 : Nat := 4983230072969 + 3 ^ 40 * 4073422 * 2
def baseEnd_4073422 : Nat := 2091623394598866951391679

theorem tailTrace_4073422 : CollatzResearch.WordTrace tailWord_4073422 prefixEnd_4073422 2091623394598866951391679 := by
  unfold tailWord_4073422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571238231086906742048815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99046603899130169290927013 18571238231086906742048815)
  ·
    refine ⟨27856857346630360113073223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18571238231086906742048815 27856857346630360113073223)
    ·
      refine ⟨41785286019945540169609835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27856857346630360113073223 41785286019945540169609835)
      ·
        refine ⟨62677929029918310254414753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41785286019945540169609835 62677929029918310254414753)
        ·
          refine ⟨47008446772438732690811065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62677929029918310254414753 47008446772438732690811065)
          ·
            refine ⟨35256335079329049518108299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47008446772438732690811065 35256335079329049518108299)
            ·
              refine ⟨52884502618993574277162449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35256335079329049518108299 52884502618993574277162449)
              ·
                refine ⟨39663376964245180707871837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52884502618993574277162449 39663376964245180707871837)
                ·
                  refine ⟨14873766361591942765451939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39663376964245180707871837 14873766361591942765451939)
                  ·
                    refine ⟨22310649542387914148177909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14873766361591942765451939 22310649542387914148177909)
                    ·
                      refine ⟨2091623394598866951391679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22310649542387914148177909 2091623394598866951391679)
                      ·
                        rfl

theorem cell23_4073422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_4073422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073422 prefixEnd_4073422 := by exact prefixLift 4073422
  have htrace : WordTrace (prefixWord ++ tailWord_4073422) baseStart_4073422 baseEnd_4073422 := by
    simpa [prefixWord, tailWord_4073422, baseEnd_4073422] using wordTrace_append hprefix tailTrace_4073422
  have hstable : (prefixWord ++ tailWord_4073422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073422).length < 2 ^ (prefixWord ++ tailWord_4073422).sum := by decide
  have hdescent : baseEnd_4073422 < baseStart_4073422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073429 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_4073429 : Nat := 118140960795 + 4073429 * 2 ^ 59
def prefixEnd_4073429 : Nat := 4983230072969 + 3 ^ 40 * 4073429 * 2
def baseEnd_4073429 : Nat := 697208996321149474668049

theorem tailTrace_4073429 : CollatzResearch.WordTrace tailWord_4073429 prefixEnd_4073429 697208996321149474668049 := by
  unfold tailWord_4073429
  simp only [CollatzResearch.WordTrace]
  refine ⟨148570161159669894131895341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99046774106446596087930227 148570161159669894131895341)
  ·
    refine ⟨55713810434876210299460753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148570161159669894131895341 55713810434876210299460753)
    ·
      refine ⟨41785357826157157724595565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55713810434876210299460753 41785357826157157724595565)
      ·
        refine ⟨15669509184808934146723337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41785357826157157724595565 15669509184808934146723337)
        ·
          refine ⟨11752131888606700610042503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15669509184808934146723337 11752131888606700610042503)
          ·
            refine ⟨17628197832910050915063755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752131888606700610042503 17628197832910050915063755)
            ·
              refine ⟨26442296749365076372595633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17628197832910050915063755 26442296749365076372595633)
              ·
                refine ⟨19831722562023807279446725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26442296749365076372595633 19831722562023807279446725)
                ·
                  refine ⟨3718447980379463864896261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19831722562023807279446725 3718447980379463864896261)
                  ·
                    refine ⟨697208996321149474668049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3718447980379463864896261 697208996321149474668049)
                    ·
                      rfl

theorem cell23_4073429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_4073429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073429 prefixEnd_4073429 := by exact prefixLift 4073429
  have htrace : WordTrace (prefixWord ++ tailWord_4073429) baseStart_4073429 baseEnd_4073429 := by
    simpa [prefixWord, tailWord_4073429, baseEnd_4073429] using wordTrace_append hprefix tailTrace_4073429
  have hstable : (prefixWord ++ tailWord_4073429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073429).length < 2 ^ (prefixWord ++ tailWord_4073429).sum := by decide
  have hdescent : baseEnd_4073429 < baseStart_4073429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073432 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_4073432 : Nat := 118140960795 + 4073432 * 2 ^ 59
def prefixEnd_4073432 : Nat := 4983230072969 + 3 ^ 40 * 4073432 * 2
def baseEnd_4073432 : Nat := 2091628529405411912266633

theorem tailTrace_4073432 : CollatzResearch.WordTrace tailWord_4073432 prefixEnd_4073432 2091628529405411912266633 := by
  unfold tailWord_4073432
  simp only [CollatzResearch.WordTrace]
  refine ⟨74285135289329512822127275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99046847052439350429503033 74285135289329512822127275)
  ·
    refine ⟨111427702933994269233190913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74285135289329512822127275 111427702933994269233190913)
    ·
      refine ⟨83570777200495701924893185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111427702933994269233190913 83570777200495701924893185)
      ·
        refine ⟨62678082900371776443669889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83570777200495701924893185 62678082900371776443669889)
        ·
          refine ⟨47008562175278832332752417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62678082900371776443669889 47008562175278832332752417)
          ·
            refine ⟨35256421631459124249564313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47008562175278832332752417 35256421631459124249564313)
            ·
              refine ⟨26442316223594343187173235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35256421631459124249564313 26442316223594343187173235)
              ·
                refine ⟨39663474335391514780759853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26442316223594343187173235 39663474335391514780759853)
                ·
                  refine ⟨14873802875771818042784945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39663474335391514780759853 14873802875771818042784945)
                  ·
                    refine ⟨11155352156828863532088709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14873802875771818042784945 11155352156828863532088709)
                    ·
                      refine ⟨2091628529405411912266633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11155352156828863532088709 2091628529405411912266633)
                      ·
                        rfl

theorem cell23_4073432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_4073432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073432 prefixEnd_4073432 := by exact prefixLift 4073432
  have htrace : WordTrace (prefixWord ++ tailWord_4073432) baseStart_4073432 baseEnd_4073432 := by
    simpa [prefixWord, tailWord_4073432, baseEnd_4073432] using wordTrace_append hprefix tailTrace_4073432
  have hstable : (prefixWord ++ tailWord_4073432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073432).length < 2 ^ (prefixWord ++ tailWord_4073432).sum := by decide
  have hdescent : baseEnd_4073432 < baseStart_4073432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073439 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_4073439 : Nat := 118140960795 + 4073439 * 2 ^ 59
def prefixEnd_4073439 : Nat := 4983230072969 + 3 ^ 40 * 4073439 * 2
def baseEnd_4073439 : Nat := 2091632123769993384879101

theorem tailTrace_4073439 : CollatzResearch.WordTrace tailWord_4073439 prefixEnd_4073439 2091632123769993384879101 := by
  unfold tailWord_4073439
  simp only [CollatzResearch.WordTrace]
  refine ⟨148570525889633665839759371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99047017259755777226506247 148570525889633665839759371)
  ·
    refine ⟨222855788834450498759639057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148570525889633665839759371 222855788834450498759639057)
    ·
      refine ⟨167141841625837874069729293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222855788834450498759639057 167141841625837874069729293)
      ·
        refine ⟨62678190609689202776148485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167141841625837874069729293 62678190609689202776148485)
        ·
          refine ⟨11752160739316725520527841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62678190609689202776148485 11752160739316725520527841)
          ·
            refine ⟨8814120554487544140395881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11752160739316725520527841 8814120554487544140395881)
            ·
              refine ⟨6610590415865658105296911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814120554487544140395881 6610590415865658105296911)
              ·
                refine ⟨9915885623798487157945367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610590415865658105296911 9915885623798487157945367)
                ·
                  refine ⟨14873828435697730736918051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915885623798487157945367 14873828435697730736918051)
                  ·
                    refine ⟨22310742653546596105377077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14873828435697730736918051 22310742653546596105377077)
                    ·
                      refine ⟨2091632123769993384879101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22310742653546596105377077 2091632123769993384879101)
                      ·
                        rfl

theorem cell23_4073439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_4073439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073439 prefixEnd_4073439 := by exact prefixLift 4073439
  have htrace : WordTrace (prefixWord ++ tailWord_4073439) baseStart_4073439 baseEnd_4073439 := by
    simpa [prefixWord, tailWord_4073439, baseEnd_4073439] using wordTrace_append hprefix tailTrace_4073439
  have hstable : (prefixWord ++ tailWord_4073439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073439).length < 2 ^ (prefixWord ++ tailWord_4073439).sum := by decide
  have hdescent : baseEnd_4073439 < baseStart_4073439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073549 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4073549 : Nat := 118140960795 + 4073549 * 2 ^ 59
def prefixEnd_4073549 : Nat := 4983230072969 + 3 ^ 40 * 4073549 * 2
def baseEnd_4073549 : Nat := 232409845182443106055955

theorem tailTrace_4073549 : CollatzResearch.WordTrace tailWord_4073549 prefixEnd_4073549 232409845182443106055955 := by
  unfold tailWord_4073549
  simp only [CollatzResearch.WordTrace]
  refine ⟨148574537919235154626263701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99049691946156769750842467 148574537919235154626263701)
  ·
    refine ⟨6964431464964147873106111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148574537919235154626263701 6964431464964147873106111)
    ·
      refine ⟨10446647197446221809659167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6964431464964147873106111 10446647197446221809659167)
      ·
        refine ⟨15669970796169332714488751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446647197446221809659167 15669970796169332714488751)
        ·
          refine ⟨23504956194253999071733127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15669970796169332714488751 23504956194253999071733127)
          ·
            refine ⟨35257434291380998607599691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23504956194253999071733127 35257434291380998607599691)
            ·
              refine ⟨52886151437071497911399537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35257434291380998607599691 52886151437071497911399537)
              ·
                refine ⟨39664613577803623433549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52886151437071497911399537 39664613577803623433549653)
                ·
                  refine ⟨232409845182443106055955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39664613577803623433549653 232409845182443106055955)
                  ·
                    rfl

theorem cell23_4073549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4073549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073549 prefixEnd_4073549 := by exact prefixLift 4073549
  have htrace : WordTrace (prefixWord ++ tailWord_4073549) baseStart_4073549 baseEnd_4073549 := by
    simpa [prefixWord, tailWord_4073549, baseEnd_4073549] using wordTrace_append hprefix tailTrace_4073549
  have hstable : (prefixWord ++ tailWord_4073549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073549).length < 2 ^ (prefixWord ++ tailWord_4073549).sum := by decide
  have hdescent : baseEnd_4073549 < baseStart_4073549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073559 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_4073559 : Nat := 118140960795 + 4073559 * 2 ^ 59
def prefixEnd_4073559 : Nat := 4983230072969 + 3 ^ 40 * 4073559 * 2
def baseEnd_4073559 : Nat := 2091693741448532915378549

theorem tailTrace_4073559 : CollatzResearch.WordTrace tailWord_4073559 prefixEnd_4073559 2091693741448532915378549 := by
  unfold tailWord_4073559
  simp only [CollatzResearch.WordTrace]
  refine ⟨148574902649198926334127731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99049935099465950889418487 148574902649198926334127731)
  ·
    refine ⟨222862353973798389501191597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148574902649198926334127731 222862353973798389501191597)
    ·
      refine ⟨83573382740174396062946849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222862353973798389501191597 83573382740174396062946849)
      ·
        refine ⟨62680037055130797047210137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83573382740174396062946849 62680037055130797047210137)
        ·
          refine ⟨47010027791348097785407603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62680037055130797047210137 47010027791348097785407603)
          ·
            refine ⟨70515041687022146678111405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47010027791348097785407603 70515041687022146678111405)
            ·
              refine ⟨26443140632633305004291777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70515041687022146678111405 26443140632633305004291777)
              ·
                refine ⟨19832355474474978753218833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26443140632633305004291777 19832355474474978753218833)
                ·
                  refine ⟨14874266605856234064914125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19832355474474978753218833 14874266605856234064914125)
                  ·
                    refine ⟨5577849977196087774342797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14874266605856234064914125 5577849977196087774342797)
                    ·
                      refine ⟨2091693741448532915378549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5577849977196087774342797 2091693741448532915378549)
                      ·
                        rfl

theorem cell23_4073559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_4073559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073559 prefixEnd_4073559 := by exact prefixLift 4073559
  have htrace : WordTrace (prefixWord ++ tailWord_4073559) baseStart_4073559 baseEnd_4073559 := by
    simpa [prefixWord, tailWord_4073559, baseEnd_4073559] using wordTrace_append hprefix tailTrace_4073559
  have hstable : (prefixWord ++ tailWord_4073559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073559).length < 2 ^ (prefixWord ++ tailWord_4073559).sum := by decide
  have hdescent : baseEnd_4073559 < baseStart_4073559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073560 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 2, 2, 2]
def baseStart_4073560 : Nat := 118140960795 + 4073560 * 2 ^ 59
def prefixEnd_4073560 : Nat := 4983230072969 + 3 ^ 40 * 4073560 * 2
def baseEnd_4073560 : Nat := 2091694254929187411466045

theorem tailTrace_4073560 : CollatzResearch.WordTrace tailWord_4073560 prefixEnd_4073560 2091694254929187411466045 := by
  unfold tailWord_4073560
  simp only [CollatzResearch.WordTrace]
  refine ⟨74287469561097651752457067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99049959414796869003276089 74287469561097651752457067)
  ·
    refine ⟨111431204341646477628685601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74287469561097651752457067 111431204341646477628685601)
    ·
      refine ⟨83573403256234858221514201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111431204341646477628685601 83573403256234858221514201)
      ·
        refine ⟨62680052442176143666135651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83573403256234858221514201 62680052442176143666135651)
        ·
          refine ⟨94020078663264215499203477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62680052442176143666135651 94020078663264215499203477)
          ·
            refine ⟨4407191187340510101525163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94020078663264215499203477 4407191187340510101525163)
            ·
              refine ⟨6610786781010765152287745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407191187340510101525163 6610786781010765152287745)
              ·
                refine ⟨4958090085758073864215809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6610786781010765152287745 4958090085758073864215809)
                ·
                  refine ⟨3718567564318555398161857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4958090085758073864215809 3718567564318555398161857)
                  ·
                    refine ⟨2788925673238916548621393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3718567564318555398161857 2788925673238916548621393)
                    ·
                      refine ⟨2091694254929187411466045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2788925673238916548621393 2091694254929187411466045)
                      ·
                        rfl

theorem cell23_4073560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_4073560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073560 prefixEnd_4073560 := by exact prefixLift 4073560
  have htrace : WordTrace (prefixWord ++ tailWord_4073560) baseStart_4073560 baseEnd_4073560 := by
    simpa [prefixWord, tailWord_4073560, baseEnd_4073560] using wordTrace_append hprefix tailTrace_4073560
  have hstable : (prefixWord ++ tailWord_4073560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073560).length < 2 ^ (prefixWord ++ tailWord_4073560).sum := by decide
  have hdescent : baseEnd_4073560 < baseStart_4073560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073592 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_4073592 : Nat := 118140960795 + 4073592 * 2 ^ 59
def prefixEnd_4073592 : Nat := 4983230072969 + 3 ^ 40 * 4073592 * 2
def baseEnd_4073592 : Nat := 697236895436710428755299

theorem tailTrace_4073592 : CollatzResearch.WordTrace tailWord_4073592 prefixEnd_4073592 697236895436710428755299 := by
  unfold tailWord_4073592
  simp only [CollatzResearch.WordTrace]
  refine ⟨74288053129039686485039515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99050737505386248646719353 74288053129039686485039515)
  ·
    refine ⟨111432079693559529727559273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74288053129039686485039515 111432079693559529727559273)
    ·
      refine ⟨83574059770169647295669455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111432079693559529727559273 83574059770169647295669455)
      ·
        refine ⟨125361089655254470943504183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83574059770169647295669455 125361089655254470943504183)
        ·
          refine ⟨188041634482881706415256275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125361089655254470943504183 188041634482881706415256275)
          ·
            refine ⟨282062451724322559622884413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188041634482881706415256275 282062451724322559622884413)
            ·
              refine ⟨105773419396620959858581655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282062451724322559622884413 105773419396620959858581655)
              ·
                refine ⟨158660129094931439787872483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105773419396620959858581655 158660129094931439787872483)
                ·
                  refine ⟨237990193642397159681808725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158660129094931439787872483 237990193642397159681808725)
                  ·
                    refine ⟨697236895436710428755299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 237990193642397159681808725 697236895436710428755299)
                    ·
                      rfl

theorem cell23_4073592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_4073592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073592 prefixEnd_4073592 := by exact prefixLift 4073592
  have htrace : WordTrace (prefixWord ++ tailWord_4073592) baseStart_4073592 baseEnd_4073592 := by
    simpa [prefixWord, tailWord_4073592, baseEnd_4073592] using wordTrace_append hprefix tailTrace_4073592
  have hstable : (prefixWord ++ tailWord_4073592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073592).length < 2 ^ (prefixWord ++ tailWord_4073592).sum := by decide
  have hdescent : baseEnd_4073592 < baseStart_4073592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073706 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_4073706 : Nat := 118140960795 + 4073706 * 2 ^ 59
def prefixEnd_4073706 : Nat := 4983230072969 + 3 ^ 40 * 4073706 * 2
def baseEnd_4073706 : Nat := 2091769223104743840240373

theorem tailTrace_4073706 : CollatzResearch.WordTrace tailWord_4073706 prefixEnd_4073706 2091769223104743840240373 := by
  unfold tailWord_4073706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145066044916592609932243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99053509453110913626485981 37145066044916592609932243)
  ·
    refine ⟨55717599067374888914898365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37145066044916592609932243 55717599067374888914898365)
    ·
      refine ⟨20894099650265583343086887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55717599067374888914898365 20894099650265583343086887)
      ·
        refine ⟨31341149475398375014630331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20894099650265583343086887 31341149475398375014630331)
        ·
          refine ⟨47011724213097562521945497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31341149475398375014630331 47011724213097562521945497)
          ·
            refine ⟨35258793159823171891459123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47011724213097562521945497 35258793159823171891459123)
            ·
              refine ⟨52888189739734757837188685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35258793159823171891459123 52888189739734757837188685)
              ·
                refine ⟨19833071152400534188945757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52888189739734757837188685 19833071152400534188945757)
                ·
                  refine ⟨7437401682150200320854659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19833071152400534188945757 7437401682150200320854659)
                  ·
                    refine ⟨11156102523225300481281989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7437401682150200320854659 11156102523225300481281989)
                    ·
                      refine ⟨2091769223104743840240373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11156102523225300481281989 2091769223104743840240373)
                      ·
                        rfl

theorem cell23_4073706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_4073706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073706 prefixEnd_4073706 := by exact prefixLift 4073706
  have htrace : WordTrace (prefixWord ++ tailWord_4073706) baseStart_4073706 baseEnd_4073706 := by
    simpa [prefixWord, tailWord_4073706, baseEnd_4073706] using wordTrace_append hprefix tailTrace_4073706
  have hstable : (prefixWord ++ tailWord_4073706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073706).length < 2 ^ (prefixWord ++ tailWord_4073706).sum := by decide
  have hdescent : baseEnd_4073706 < baseStart_4073706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073729 : List Nat := [1, 2, 4, 1, 1, 2, 12]
def baseStart_4073729 : Nat := 118140960795 + 4073729 * 2 ^ 59
def prefixEnd_4073729 : Nat := 4983230072969 + 3 ^ 40 * 4073729 * 2
def baseEnd_4073729 : Nat := 25824457199503669756207

theorem tailTrace_4073729 : CollatzResearch.WordTrace tailWord_4073729 prefixEnd_4073729 25824457199503669756207 := by
  unfold tailWord_4073729
  simp only [CollatzResearch.WordTrace]
  refine ⟨148581103058583045367816241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99054068705722030245210827 148581103058583045367816241)
  ·
    refine ⟨111435827293937284025862181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148581103058583045367816241 111435827293937284025862181)
    ·
      refine ⟨20894217617613240754849159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111435827293937284025862181 20894217617613240754849159)
      ·
        refine ⟨31341326426419861132273739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20894217617613240754849159 31341326426419861132273739)
        ·
          refine ⟨47011989639629791698410609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31341326426419861132273739 47011989639629791698410609)
          ·
            refine ⟨35258992229722343773807957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47011989639629791698410609 35258992229722343773807957)
            ·
              refine ⟨25824457199503669756207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 35258992229722343773807957 25824457199503669756207)
              ·
                rfl

theorem cell23_4073729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 12].length) (baseStart_4073729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073729 prefixEnd_4073729 := by exact prefixLift 4073729
  have htrace : WordTrace (prefixWord ++ tailWord_4073729) baseStart_4073729 baseEnd_4073729 := by
    simpa [prefixWord, tailWord_4073729, baseEnd_4073729] using wordTrace_append hprefix tailTrace_4073729
  have hstable : (prefixWord ++ tailWord_4073729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073729).length < 2 ^ (prefixWord ++ tailWord_4073729).sum := by decide
  have hdescent : baseEnd_4073729 < baseStart_4073729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073740 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 3, 2, 2]
def baseStart_4073740 : Nat := 118140960795 + 4073740 * 2 ^ 59
def prefixEnd_4073740 : Nat := 4983230072969 + 3 ^ 40 * 4073740 * 2
def baseEnd_4073740 : Nat := 2091786681446996707215217

theorem tailTrace_4073740 : CollatzResearch.WordTrace tailWord_4073740 prefixEnd_4073740 2091786681446996707215217 := by
  unfold tailWord_4073740
  simp only [CollatzResearch.WordTrace]
  refine ⟨74290752130771597123233337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99054336174362129497644449 74290752130771597123233337)
  ·
    refine ⟨55718064098078697842425003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74290752130771597123233337 55718064098078697842425003)
    ·
      refine ⟨83577096147118046763637505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55718064098078697842425003 83577096147118046763637505)
      ·
        refine ⟨62682822110338535072728129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83577096147118046763637505 62682822110338535072728129)
        ·
          refine ⟨47012116582753901304546097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62682822110338535072728129 47012116582753901304546097)
          ·
            refine ⟨35259087437065425978409573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47012116582753901304546097 35259087437065425978409573)
            ·
              refine ⟨6611078894449767370951795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35259087437065425978409573 6611078894449767370951795)
              ·
                refine ⟨9916618341674651056427693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611078894449767370951795 9916618341674651056427693)
                ·
                  refine ⟨3718731878127994146160385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9916618341674651056427693 3718731878127994146160385)
                  ·
                    refine ⟨2789048908595995609620289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3718731878127994146160385 2789048908595995609620289)
                    ·
                      refine ⟨2091786681446996707215217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789048908595995609620289 2091786681446996707215217)
                      ·
                        rfl

theorem cell23_4073740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_4073740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073740 prefixEnd_4073740 := by exact prefixLift 4073740
  have htrace : WordTrace (prefixWord ++ tailWord_4073740) baseStart_4073740 baseEnd_4073740 := by
    simpa [prefixWord, tailWord_4073740, baseEnd_4073740] using wordTrace_append hprefix tailTrace_4073740
  have hstable : (prefixWord ++ tailWord_4073740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073740).length < 2 ^ (prefixWord ++ tailWord_4073740).sum := by decide
  have hdescent : baseEnd_4073740 < baseStart_4073740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073760 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3]
def baseStart_4073760 : Nat := 118140960795 + 4073760 * 2 ^ 59
def prefixEnd_4073760 : Nat := 4983230072969 + 3 ^ 40 * 4073760 * 2
def baseEnd_4073760 : Nat := 2091796951060086628965125

theorem tailTrace_4073760 : CollatzResearch.WordTrace tailWord_4073760 prefixEnd_4073760 2091796951060086628965125 := by
  unfold tailWord_4073760
  simp only [CollatzResearch.WordTrace]
  refine ⟨74291116860735368831097367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99054822480980491774796489 74291116860735368831097367)
  ·
    refine ⟨111436675291103053246646051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74291116860735368831097367 111436675291103053246646051)
    ·
      refine ⟨167155012936654579869969077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111436675291103053246646051 167155012936654579869969077)
      ·
        refine ⟨15670782462811366862809601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167155012936654579869969077 15670782462811366862809601)
        ·
          refine ⟨11753086847108525147107201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15670782462811366862809601 11753086847108525147107201)
          ·
            refine ⟨8814815135331393860330401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11753086847108525147107201 8814815135331393860330401)
            ·
              refine ⟨6611111351498545395247801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814815135331393860330401 6611111351498545395247801)
              ·
                refine ⟨4958333513623909046435851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6611111351498545395247801 4958333513623909046435851)
                ·
                  refine ⟨7437500270435863569653777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958333513623909046435851 7437500270435863569653777)
                  ·
                    refine ⟨5578125202826897677240333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7437500270435863569653777 5578125202826897677240333)
                    ·
                      refine ⟨2091796951060086628965125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578125202826897677240333 2091796951060086628965125)
                      ·
                        rfl

theorem cell23_4073760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_4073760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073760 prefixEnd_4073760 := by exact prefixLift 4073760
  have htrace : WordTrace (prefixWord ++ tailWord_4073760) baseStart_4073760 baseEnd_4073760 := by
    simpa [prefixWord, tailWord_4073760, baseEnd_4073760] using wordTrace_append hprefix tailTrace_4073760
  have hstable : (prefixWord ++ tailWord_4073760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073760).length < 2 ^ (prefixWord ++ tailWord_4073760).sum := by decide
  have hdescent : baseEnd_4073760 < baseStart_4073760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073790 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_4073790 : Nat := 118140960795 + 4073790 * 2 ^ 59
def prefixEnd_4073790 : Nat := 4983230072969 + 3 ^ 40 * 4073790 * 2
def baseEnd_4073790 : Nat := 2091812355479721511589987

theorem tailTrace_4073790 : CollatzResearch.WordTrace tailWord_4073790 prefixEnd_4073790 2091812355479721511589987 := by
  unfold tailWord_4073790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572915988920256598223353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99055551940908035190524549 18572915988920256598223353)
  ·
    refine ⟨13929686991690192448667515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18572915988920256598223353 13929686991690192448667515)
    ·
      refine ⟨20894530487535288673001273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13929686991690192448667515 20894530487535288673001273)
      ·
        refine ⟨15670897865651466504750955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20894530487535288673001273 15670897865651466504750955)
        ·
          refine ⟨23506346798477199757126433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15670897865651466504750955 23506346798477199757126433)
          ·
            refine ⟨17629760098857899817844825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23506346798477199757126433 17629760098857899817844825)
            ·
              refine ⟨13222320074143424863383619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17629760098857899817844825 13222320074143424863383619)
              ·
                refine ⟨19833480111215137295075429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222320074143424863383619 19833480111215137295075429)
                ·
                  refine ⟨3718777520852838242826643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19833480111215137295075429 3718777520852838242826643)
                  ·
                    refine ⟨5578166281279257364239965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3718777520852838242826643 5578166281279257364239965)
                    ·
                      refine ⟨2091812355479721511589987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578166281279257364239965 2091812355479721511589987)
                      ·
                        rfl

theorem cell23_4073790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_4073790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073790 prefixEnd_4073790 := by exact prefixLift 4073790
  have htrace : WordTrace (prefixWord ++ tailWord_4073790) baseStart_4073790 baseEnd_4073790 := by
    simpa [prefixWord, tailWord_4073790, baseEnd_4073790] using wordTrace_append hprefix tailTrace_4073790
  have hstable : (prefixWord ++ tailWord_4073790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073790).length < 2 ^ (prefixWord ++ tailWord_4073790).sum := by decide
  have hdescent : baseEnd_4073790 < baseStart_4073790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073816 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_4073816 : Nat := 118140960795 + 4073816 * 2 ^ 59
def prefixEnd_4073816 : Nat := 4983230072969 + 3 ^ 40 * 4073816 * 2
def baseEnd_4073816 : Nat := 2091825705976738409864867

theorem tailTrace_4073816 : CollatzResearch.WordTrace tailWord_4073816 prefixEnd_4073816 2091825705976738409864867 := by
  unfold tailWord_4073816
  simp only [CollatzResearch.WordTrace]
  refine ⟨74292138104633929613116651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99056184139511906150822201 74292138104633929613116651)
  ·
    refine ⟨111438207156950894419674977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74292138104633929613116651 111438207156950894419674977)
    ·
      refine ⟨83578655367713170814756233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111438207156950894419674977 83578655367713170814756233)
      ·
        refine ⟨62683991525784878111067175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83578655367713170814756233 62683991525784878111067175)
        ·
          refine ⟨94025987288677317166600763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62683991525784878111067175 94025987288677317166600763)
          ·
            refine ⟨141038980933015975749901145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94025987288677317166600763 141038980933015975749901145)
            ·
              refine ⟨105779235699761981812425859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141038980933015975749901145 105779235699761981812425859)
              ·
                refine ⟨158668853549642972718638789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105779235699761981812425859 158668853549642972718638789)
                ·
                  refine ⟨29750410040558057384744773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158668853549642972718638789 29750410040558057384744773)
                  ·
                    refine ⟨5578201882604635759639645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29750410040558057384744773 5578201882604635759639645)
                    ·
                      refine ⟨2091825705976738409864867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578201882604635759639645 2091825705976738409864867)
                      ·
                        rfl

theorem cell23_4073816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_4073816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073816 prefixEnd_4073816 := by exact prefixLift 4073816
  have htrace : WordTrace (prefixWord ++ tailWord_4073816) baseStart_4073816 baseEnd_4073816 := by
    simpa [prefixWord, tailWord_4073816, baseEnd_4073816] using wordTrace_append hprefix tailTrace_4073816
  have hstable : (prefixWord ++ tailWord_4073816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073816).length < 2 ^ (prefixWord ++ tailWord_4073816).sum := by decide
  have hdescent : baseEnd_4073816 < baseStart_4073816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073834 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4073834 : Nat := 118140960795 + 4073834 * 2 ^ 59
def prefixEnd_4073834 : Nat := 4983230072969 + 3 ^ 40 * 4073834 * 2
def baseEnd_4073834 : Nat := 2091834948628519339439785

theorem tailTrace_4073834 : CollatzResearch.WordTrace tailWord_4073834 prefixEnd_4073834 2091834948628519339439785 := by
  unfold tailWord_4073834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37146233180800662075097139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99056621815468432200259037 37146233180800662075097139)
  ·
    refine ⟨55719349771200993112645709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37146233180800662075097139 55719349771200993112645709)
    ·
      refine ⟨20894756164200372417242141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55719349771200993112645709 20894756164200372417242141)
      ·
        refine ⟨7835533561575139656465803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20894756164200372417242141 7835533561575139656465803)
        ·
          refine ⟨11753300342362709484698705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835533561575139656465803 11753300342362709484698705)
          ·
            refine ⟨8814975256772032113524029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11753300342362709484698705 8814975256772032113524029)
            ·
              refine ⟨3305615721289512042571511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8814975256772032113524029 3305615721289512042571511)
              ·
                refine ⟨4958423581934268063857267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305615721289512042571511 4958423581934268063857267)
                ·
                  refine ⟨7437635372901402095785901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958423581934268063857267 7437635372901402095785901)
                  ·
                    refine ⟨2789113264838025785919713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7437635372901402095785901 2789113264838025785919713)
                    ·
                      refine ⟨2091834948628519339439785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789113264838025785919713 2091834948628519339439785)
                      ·
                        rfl

theorem cell23_4073834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4073834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073834 prefixEnd_4073834 := by exact prefixLift 4073834
  have htrace : WordTrace (prefixWord ++ tailWord_4073834) baseStart_4073834 baseEnd_4073834 := by
    simpa [prefixWord, tailWord_4073834, baseEnd_4073834] using wordTrace_append hprefix tailTrace_4073834
  have hstable : (prefixWord ++ tailWord_4073834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073834).length < 2 ^ (prefixWord ++ tailWord_4073834).sum := by decide
  have hdescent : baseEnd_4073834 < baseStart_4073834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073863 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_4073863 : Nat := 118140960795 + 4073863 * 2 ^ 59
def prefixEnd_4073863 : Nat := 4983230072969 + 3 ^ 40 * 4073863 * 2
def baseEnd_4073863 : Nat := 2091849839567499725977151

theorem tailTrace_4073863 : CollatzResearch.WordTrace tailWord_4073863 prefixEnd_4073863 2091849839567499725977151 := by
  unfold tailWord_4073863
  simp only [CollatzResearch.WordTrace]
  refine ⟨148585990440097586253194243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99057326960065057502129495 148585990440097586253194243)
  ·
    refine ⟨222878985660146379379791365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148585990440097586253194243 222878985660146379379791365)
    ·
      refine ⟨41789809811277446133710881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222878985660146379379791365 41789809811277446133710881)
      ·
        refine ⟨31342357358458084600283161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41789809811277446133710881 31342357358458084600283161)
        ·
          refine ⟨23506768018843563450212371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31342357358458084600283161 23506768018843563450212371)
          ·
            refine ⟨35260152028265345175318557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23506768018843563450212371 35260152028265345175318557)
            ·
              refine ⟨13222557010599504440744459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35260152028265345175318557 13222557010599504440744459)
              ·
                refine ⟨19833835515899256661116689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222557010599504440744459 19833835515899256661116689)
                ·
                  refine ⟨14875376636924442495837517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19833835515899256661116689 14875376636924442495837517)
                  ·
                    refine ⟨5578266238846665935939069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14875376636924442495837517 5578266238846665935939069)
                    ·
                      refine ⟨2091849839567499725977151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578266238846665935939069 2091849839567499725977151)
                      ·
                        rfl

theorem cell23_4073863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_4073863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073863 prefixEnd_4073863 := by exact prefixLift 4073863
  have htrace : WordTrace (prefixWord ++ tailWord_4073863) baseStart_4073863 baseEnd_4073863 := by
    simpa [prefixWord, tailWord_4073863, baseEnd_4073863] using wordTrace_append hprefix tailTrace_4073863
  have hstable : (prefixWord ++ tailWord_4073863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073863).length < 2 ^ (prefixWord ++ tailWord_4073863).sum := by decide
  have hdescent : baseEnd_4073863 < baseStart_4073863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073940 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4073940 : Nat := 118140960795 + 4073940 * 2 ^ 59
def prefixEnd_4073940 : Nat := 4983230072969 + 3 ^ 40 * 4073940 * 2
def baseEnd_4073940 : Nat := 2091889377577895924714297

theorem tailTrace_4073940 : CollatzResearch.WordTrace tailWord_4073940 prefixEnd_4073940 2091889377577895924714297 := by
  unfold tailWord_4073940
  simp only [CollatzResearch.WordTrace]
  refine ⟨74294399430409314201873637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99059199240545752269164849 74294399430409314201873637)
  ·
    refine ⟨13930199893201746412851307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74294399430409314201873637 13930199893201746412851307)
    ·
      refine ⟨20895299839802619619276961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13930199893201746412851307 20895299839802619619276961)
      ·
        refine ⟨15671474879851964714457721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20895299839802619619276961 15671474879851964714457721)
        ·
          refine ⟨11753606159888973535843291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15671474879851964714457721 11753606159888973535843291)
          ·
            refine ⟨17630409239833460303764937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11753606159888973535843291 17630409239833460303764937)
            ·
              refine ⟨13222806929875095227823703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17630409239833460303764937 13222806929875095227823703)
              ·
                refine ⟨19834210394812642841735555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222806929875095227823703 19834210394812642841735555)
                ·
                  refine ⟨29751315592218964262603333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19834210394812642841735555 29751315592218964262603333)
                  ·
                    refine ⟨5578371673541055799238125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29751315592218964262603333 5578371673541055799238125)
                    ·
                      refine ⟨2091889377577895924714297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578371673541055799238125 2091889377577895924714297)
                      ·
                        rfl

theorem cell23_4073940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4073940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073940 prefixEnd_4073940 := by exact prefixLift 4073940
  have htrace : WordTrace (prefixWord ++ tailWord_4073940) baseStart_4073940 baseEnd_4073940 := by
    simpa [prefixWord, tailWord_4073940, baseEnd_4073940] using wordTrace_append hprefix tailTrace_4073940
  have hstable : (prefixWord ++ tailWord_4073940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073940).length < 2 ^ (prefixWord ++ tailWord_4073940).sum := by decide
  have hdescent : baseEnd_4073940 < baseStart_4073940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073954 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4073954 : Nat := 118140960795 + 4073954 * 2 ^ 59
def prefixEnd_4073954 : Nat := 4983230072969 + 3 ^ 40 * 4073954 * 2
def baseEnd_4073954 : Nat := 2091896566307058869939233

theorem tailTrace_4073954 : CollatzResearch.WordTrace tailWord_4073954 prefixEnd_4073954 2091896566307058869939233 := by
  unfold tailWord_4073954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37147327370691977198689229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99059539655178605863171277 37147327370691977198689229)
  ·
    refine ⟨13930247764009491449508461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37147327370691977198689229 13930247764009491449508461)
    ·
      refine ⟨5223842911503559293565673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13930247764009491449508461 5223842911503559293565673)
      ·
        refine ⟨3917882183627669470174255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5223842911503559293565673 3917882183627669470174255)
        ·
          refine ⟨5876823275441504205261383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917882183627669470174255 5876823275441504205261383)
          ·
            refine ⟨8815234913162256307892075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876823275441504205261383 8815234913162256307892075)
            ·
              refine ⟨13222852369743384461838113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815234913162256307892075 13222852369743384461838113)
              ·
                refine ⟨9917139277307538346378585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222852369743384461838113 9917139277307538346378585)
                ·
                  refine ⟨7437854457980653759783939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917139277307538346378585 7437854457980653759783939)
                  ·
                    refine ⟨11156781686970980639675909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7437854457980653759783939 11156781686970980639675909)
                    ·
                      refine ⟨2091896566307058869939233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11156781686970980639675909 2091896566307058869939233)
                      ·
                        rfl

theorem cell23_4073954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4073954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073954 prefixEnd_4073954 := by exact prefixLift 4073954
  have htrace : WordTrace (prefixWord ++ tailWord_4073954) baseStart_4073954 baseEnd_4073954 := by
    simpa [prefixWord, tailWord_4073954, baseEnd_4073954] using wordTrace_append hprefix tailTrace_4073954
  have hstable : (prefixWord ++ tailWord_4073954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073954).length < 2 ^ (prefixWord ++ tailWord_4073954).sum := by decide
  have hdescent : baseEnd_4073954 < baseStart_4073954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073957 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4073957 : Nat := 118140960795 + 4073957 * 2 ^ 59
def prefixEnd_4073957 : Nat := 4983230072969 + 3 ^ 40 * 4073957 * 2
def baseEnd_4073957 : Nat := 2091898106749022358201719

theorem tailTrace_4073957 : CollatzResearch.WordTrace tailWord_4073957 prefixEnd_4073957 2091898106749022358201719 := by
  unfold tailWord_4073957
  simp only [CollatzResearch.WordTrace]
  refine ⟨148589418901757040307116125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99059612601171360204744083 148589418901757040307116125)
  ·
    refine ⟨55721032088158890115168547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148589418901757040307116125 55721032088158890115168547)
    ·
      refine ⟨83581548132238335172752821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55721032088158890115168547 83581548132238335172752821)
      ·
        refine ⟨7835770137397343922445577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83581548132238335172752821 7835770137397343922445577)
        ·
          refine ⟨5876827603048007941834183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7835770137397343922445577 5876827603048007941834183)
          ·
            refine ⟨8815241404572011912751275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876827603048007941834183 8815241404572011912751275)
            ·
              refine ⟨13222862106858017869126913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815241404572011912751275 13222862106858017869126913)
              ·
                refine ⟨9917146580143513401845185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222862106858017869126913 9917146580143513401845185)
                ·
                  refine ⟨7437859935107635051383889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917146580143513401845185 7437859935107635051383889)
                  ·
                    refine ⟨5578394951330726288537917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7437859935107635051383889 5578394951330726288537917)
                    ·
                      refine ⟨2091898106749022358201719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578394951330726288537917 2091898106749022358201719)
                      ·
                        rfl

theorem cell23_4073957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4073957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073957 prefixEnd_4073957 := by exact prefixLift 4073957
  have htrace : WordTrace (prefixWord ++ tailWord_4073957) baseStart_4073957 baseEnd_4073957 := by
    simpa [prefixWord, tailWord_4073957, baseEnd_4073957] using wordTrace_append hprefix tailTrace_4073957
  have hstable : (prefixWord ++ tailWord_4073957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073957).length < 2 ^ (prefixWord ++ tailWord_4073957).sum := by decide
  have hdescent : baseEnd_4073957 < baseStart_4073957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073980 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_4073980 : Nat := 118140960795 + 4073980 * 2 ^ 59
def prefixEnd_4073980 : Nat := 4983230072969 + 3 ^ 40 * 4073980 * 2
def baseEnd_4073980 : Nat := 2091909916804075768214113

theorem tailTrace_4073980 : CollatzResearch.WordTrace tailWord_4073980 prefixEnd_4073980 2091909916804075768214113 := by
  unfold tailWord_4073980
  simp only [CollatzResearch.WordTrace]
  refine ⟨74295128890336857617601697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99060171853782476823468929 74295128890336857617601697)
  ·
    refine ⟨55721346667752643213201273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74295128890336857617601697 55721346667752643213201273)
    ·
      refine ⟨41791010000814482409900955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55721346667752643213201273 41791010000814482409900955)
      ·
        refine ⟨62686515001221723614851433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41791010000814482409900955 62686515001221723614851433)
        ·
          refine ⟨47014886250916292711138575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62686515001221723614851433 47014886250916292711138575)
          ·
            refine ⟨70522329376374439066707863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47014886250916292711138575 70522329376374439066707863)
            ·
              refine ⟨105783494064561658600061795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70522329376374439066707863 105783494064561658600061795)
              ·
                refine ⟨158675241096842487900092693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105783494064561658600061795 158675241096842487900092693)
                ·
                  refine ⟨7437901926414491620316845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158675241096842487900092693 7437901926414491620316845)
                  ·
                    refine ⟨2789213222405434357618817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7437901926414491620316845 2789213222405434357618817)
                    ·
                      refine ⟨2091909916804075768214113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789213222405434357618817 2091909916804075768214113)
                      ·
                        rfl

theorem cell23_4073980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_4073980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4073980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4073980 prefixEnd_4073980 := by exact prefixLift 4073980
  have htrace : WordTrace (prefixWord ++ tailWord_4073980) baseStart_4073980 baseEnd_4073980 := by
    simpa [prefixWord, tailWord_4073980, baseEnd_4073980] using wordTrace_append hprefix tailTrace_4073980
  have hstable : (prefixWord ++ tailWord_4073980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073980).length < 2 ^ (prefixWord ++ tailWord_4073980).sum := by decide
  have hdescent : baseEnd_4073980 < baseStart_4073980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074003 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 1, 6]
def baseStart_4074003 : Nat := 118140960795 + 4074003 * 2 ^ 59
def prefixEnd_4074003 : Nat := 4983230072969 + 3 ^ 40 * 4074003 * 2
def baseEnd_4074003 : Nat := 697307242286376392742169

theorem tailTrace_4074003 : CollatzResearch.WordTrace tailWord_4074003 prefixEnd_4074003 697307242286376392742169 := by
  unfold tailWord_4074003
  simp only [CollatzResearch.WordTrace]
  refine ⟨148591096659590390163290663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99060731106393593442193775 148591096659590390163290663)
  ·
    refine ⟨222886644989385585244935995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148591096659590390163290663 222886644989385585244935995)
    ·
      refine ⟨334329967484078377867403993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222886644989385585244935995 334329967484078377867403993)
      ·
        refine ⟨250747475613058783400552995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334329967484078377867403993 250747475613058783400552995)
        ·
          refine ⟨376121213419588175100829493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250747475613058783400552995 376121213419588175100829493)
          ·
            refine ⟨35261363758086391415702765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376121213419588175100829493 35261363758086391415702765)
            ·
              refine ⟨13223011409282396780888537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35261363758086391415702765 13223011409282396780888537)
              ·
                refine ⟨9917258556961797585666403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13223011409282396780888537 9917258556961797585666403)
                ·
                  refine ⟨14875887835442696378499605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917258556961797585666403 14875887835442696378499605)
                  ·
                    refine ⟨697307242286376392742169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14875887835442696378499605 697307242286376392742169)
                    ·
                      rfl

theorem cell23_4074003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 6].length) (baseStart_4074003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074003 prefixEnd_4074003 := by exact prefixLift 4074003
  have htrace : WordTrace (prefixWord ++ tailWord_4074003) baseStart_4074003 baseEnd_4074003 := by
    simpa [prefixWord, tailWord_4074003, baseEnd_4074003] using wordTrace_append hprefix tailTrace_4074003
  have hstable : (prefixWord ++ tailWord_4074003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074003).length < 2 ^ (prefixWord ++ tailWord_4074003).sum := by decide
  have hdescent : baseEnd_4074003 < baseStart_4074003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074010 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_4074010 : Nat := 118140960795 + 4074010 * 2 ^ 59
def prefixEnd_4074010 : Nat := 4983230072969 + 3 ^ 40 * 4074010 * 2
def baseEnd_4074010 : Nat := 2091925321223710650838975

theorem tailTrace_4074010 : CollatzResearch.WordTrace tailWord_4074010 prefixEnd_4074010 2091925321223710650838975 := by
  unfold tailWord_4074010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37147837992641257589698871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99060901313710020239196989 37147837992641257589698871)
  ·
    refine ⟨55721756988961886384548307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37147837992641257589698871 55721756988961886384548307)
    ·
      refine ⟨83582635483442829576822461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55721756988961886384548307 83582635483442829576822461)
      ·
        refine ⟨31343488306291061091308423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83582635483442829576822461 31343488306291061091308423)
        ·
          refine ⟨47015232459436591636962635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31343488306291061091308423 47015232459436591636962635)
          ·
            refine ⟨70522848689154887455443953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47015232459436591636962635 70522848689154887455443953)
            ·
              refine ⟨52892136516866165591582965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70522848689154887455443953 52892136516866165591582965)
              ·
                refine ⟨4958637798456203024210903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52892136516866165591582965 4958637798456203024210903)
                ·
                  refine ⟨7437956697684304536316355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958637798456203024210903 7437956697684304536316355)
                  ·
                    refine ⟨11156935046526456804474533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7437956697684304536316355 11156935046526456804474533)
                    ·
                      refine ⟨2091925321223710650838975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11156935046526456804474533 2091925321223710650838975)
                      ·
                        rfl

theorem cell23_4074010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_4074010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074010 prefixEnd_4074010 := by exact prefixLift 4074010
  have htrace : WordTrace (prefixWord ++ tailWord_4074010) baseStart_4074010 baseEnd_4074010 := by
    simpa [prefixWord, tailWord_4074010, baseEnd_4074010] using wordTrace_append hprefix tailTrace_4074010
  have hstable : (prefixWord ++ tailWord_4074010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074010).length < 2 ^ (prefixWord ++ tailWord_4074010).sum := by decide
  have hdescent : baseEnd_4074010 < baseStart_4074010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074033 : List Nat := [1, 2, 2, 3, 1, 1, 5, 8]
def baseStart_4074033 : Nat := 118140960795 + 4074033 * 2 ^ 59
def prefixEnd_4074033 : Nat := 4983230072969 + 3 ^ 40 * 4074033 * 2
def baseEnd_4074033 : Nat := 77479153010324594846347

theorem tailTrace_4074033 : CollatzResearch.WordTrace tailWord_4074033 prefixEnd_4074033 77479153010324594846347 := by
  unfold tailWord_4074033
  simp only [CollatzResearch.WordTrace]
  refine ⟨148592190849481705286882753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99061460566321136857921835 148592190849481705286882753)
  ·
    refine ⟨111444143137111278965162065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148592190849481705286882753 111444143137111278965162065)
    ·
      refine ⟨83583107352833459223871549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111444143137111278965162065 83583107352833459223871549)
      ·
        refine ⟨31343665257312547208951831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83583107352833459223871549 31343665257312547208951831)
        ·
          refine ⟨47015497885968820813427747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31343665257312547208951831 47015497885968820813427747)
          ·
            refine ⟨70523246828953231220141621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47015497885968820813427747 70523246828953231220141621)
            ·
              refine ⟨6611554390214365426888277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70523246828953231220141621 6611554390214365426888277)
              ·
                refine ⟨77479153010324594846347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6611554390214365426888277 77479153010324594846347)
                ·
                  rfl

theorem cell23_4074033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 8].length) (baseStart_4074033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074033 prefixEnd_4074033 := by exact prefixLift 4074033
  have htrace : WordTrace (prefixWord ++ tailWord_4074033) baseStart_4074033 baseEnd_4074033 := by
    simpa [prefixWord, tailWord_4074033, baseEnd_4074033] using wordTrace_append hprefix tailTrace_4074033
  have hstable : (prefixWord ++ tailWord_4074033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074033).length < 2 ^ (prefixWord ++ tailWord_4074033).sum := by decide
  have hdescent : baseEnd_4074033 < baseStart_4074033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074040 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_4074040 : Nat := 118140960795 + 4074040 * 2 ^ 59
def prefixEnd_4074040 : Nat := 4983230072969 + 3 ^ 40 * 4074040 * 2
def baseEnd_4074040 : Nat := 2091940725643345533463837

theorem tailTrace_4074040 : CollatzResearch.WordTrace tailWord_4074040 prefixEnd_4074040 2091940725643345533463837 := by
  unfold tailWord_4074040
  simp only [CollatzResearch.WordTrace]
  refine ⟨74296223080228172741193787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99061630773637563654925049 74296223080228172741193787)
  ·
    refine ⟨111444334620342259111790681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74296223080228172741193787 111444334620342259111790681)
    ·
      refine ⟨83583250965256694333843011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111444334620342259111790681 83583250965256694333843011)
      ·
        refine ⟨125374876447885041500764517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83583250965256694333843011 125374876447885041500764517)
        ·
          refine ⟨23507789333978445281393347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125374876447885041500764517 23507789333978445281393347)
          ·
            refine ⟨35261684000967667922090021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23507789333978445281393347 35261684000967667922090021)
            ·
              refine ⟨6611565750181437735391879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35261684000967667922090021 6611565750181437735391879)
              ·
                refine ⟨9917348625272156603087819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611565750181437735391879 9917348625272156603087819)
                ·
                  refine ⟨14876022937908234904631729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917348625272156603087819 14876022937908234904631729)
                  ·
                    refine ⟨11157017203431176178473797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14876022937908234904631729 11157017203431176178473797)
                    ·
                      refine ⟨2091940725643345533463837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11157017203431176178473797 2091940725643345533463837)
                      ·
                        rfl

theorem cell23_4074040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_4074040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074040 prefixEnd_4074040 := by exact prefixLift 4074040
  have htrace : WordTrace (prefixWord ++ tailWord_4074040) baseStart_4074040 baseEnd_4074040 := by
    simpa [prefixWord, tailWord_4074040, baseEnd_4074040] using wordTrace_append hprefix tailTrace_4074040
  have hstable : (prefixWord ++ tailWord_4074040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074040).length < 2 ^ (prefixWord ++ tailWord_4074040).sum := by decide
  have hdescent : baseEnd_4074040 < baseStart_4074040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074044 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_4074044 : Nat := 118140960795 + 4074044 * 2 ^ 59
def prefixEnd_4074044 : Nat := 4983230072969 + 3 ^ 40 * 4074044 * 2
def baseEnd_4074044 : Nat := 2091942779565963517813819

theorem tailTrace_4074044 : CollatzResearch.WordTrace tailWord_4074044 prefixEnd_4074044 2091942779565963517813819 := by
  unfold tailWord_4074044
  simp only [CollatzResearch.WordTrace]
  refine ⟨74296296026220927082766593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99061728034961236110355457 74296296026220927082766593)
  ·
    refine ⟨55722222019665695312074945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74296296026220927082766593 55722222019665695312074945)
    ·
      refine ⟨41791666514749271484056209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55722222019665695312074945 41791666514749271484056209)
      ·
        refine ⟨31343749886061953613042157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41791666514749271484056209 31343749886061953613042157)
        ·
          refine ⟨11753906207273232604890809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31343749886061953613042157 11753906207273232604890809)
          ·
            refine ⟨8815429655454924453668107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11753906207273232604890809 8815429655454924453668107)
            ·
              refine ⟨13223144483182386680502161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815429655454924453668107 13223144483182386680502161)
              ·
                refine ⟨9917358362386790010376621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13223144483182386680502161 9917358362386790010376621)
                ·
                  refine ⟨3719009385895046253891233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9917358362386790010376621 3719009385895046253891233)
                  ·
                    refine ⟨2789257039421284690418425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3719009385895046253891233 2789257039421284690418425)
                    ·
                      refine ⟨2091942779565963517813819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789257039421284690418425 2091942779565963517813819)
                      ·
                        rfl

theorem cell23_4074044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_4074044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074044 prefixEnd_4074044 := by exact prefixLift 4074044
  have htrace : WordTrace (prefixWord ++ tailWord_4074044) baseStart_4074044 baseEnd_4074044 := by
    simpa [prefixWord, tailWord_4074044, baseEnd_4074044] using wordTrace_append hprefix tailTrace_4074044
  have hstable : (prefixWord ++ tailWord_4074044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074044).length < 2 ^ (prefixWord ++ tailWord_4074044).sum := by decide
  have hdescent : baseEnd_4074044 < baseStart_4074044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074060 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4074060 : Nat := 118140960795 + 4074060 * 2 ^ 59
def prefixEnd_4074060 : Nat := 4983230072969 + 3 ^ 40 * 4074060 * 2
def baseEnd_4074060 : Nat := 2091950995256435455213745

theorem tailTrace_4074060 : CollatzResearch.WordTrace tailWord_4074060 prefixEnd_4074060 2091950995256435455213745 := by
  unfold tailWord_4074060
  simp only [CollatzResearch.WordTrace]
  refine ⟨74296587810191944449057817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99062117080255925932077089 74296587810191944449057817)
  ·
    refine ⟨55722440857643958336793363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74296587810191944449057817 55722440857643958336793363)
    ·
      refine ⟨83583661286465937505190045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55722440857643958336793363 83583661286465937505190045)
      ·
        refine ⟨31343872982424726564446267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83583661286465937505190045 31343872982424726564446267)
        ·
          refine ⟨47015809473637089846669401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31343872982424726564446267 47015809473637089846669401)
          ·
            refine ⟨35261857105227817385002051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47015809473637089846669401 35261857105227817385002051)
            ·
              refine ⟨52892785657841726077503077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35261857105227817385002051 52892785657841726077503077)
              ·
                refine ⟨9917397310845323639531827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52892785657841726077503077 9917397310845323639531827)
                ·
                  refine ⟨14876095966267985459297741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917397310845323639531827 14876095966267985459297741)
                  ·
                    refine ⟨5578535987350494547236653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14876095966267985459297741 5578535987350494547236653)
                    ·
                      refine ⟨2091950995256435455213745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578535987350494547236653 2091950995256435455213745)
                      ·
                        rfl

theorem cell23_4074060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4074060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074060 prefixEnd_4074060 := by exact prefixLift 4074060
  have htrace : WordTrace (prefixWord ++ tailWord_4074060) baseStart_4074060 baseEnd_4074060 := by
    simpa [prefixWord, tailWord_4074060, baseEnd_4074060] using wordTrace_append hprefix tailTrace_4074060
  have hstable : (prefixWord ++ tailWord_4074060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074060).length < 2 ^ (prefixWord ++ tailWord_4074060).sum := by decide
  have hdescent : baseEnd_4074060 < baseStart_4074060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074061 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4074061 : Nat := 118140960795 + 4074061 * 2 ^ 59
def prefixEnd_4074061 : Nat := 4983230072969 + 3 ^ 40 * 4074061 * 2
def baseEnd_4074061 : Nat := 2091951508737089951301241

theorem tailTrace_4074061 : CollatzResearch.WordTrace tailWord_4074061 prefixEnd_4074061 2091951508737089951301241 := by
  unfold tailWord_4074061
  simp only [CollatzResearch.WordTrace]
  refine ⟨148593212093380266068902037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99062141395586844045934691 148593212093380266068902037)
  ·
    refine ⟨6965306816877199971979783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148593212093380266068902037 6965306816877199971979783)
    ·
      refine ⟨10447960225315799957969675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6965306816877199971979783 10447960225315799957969675)
      ·
        refine ⟨15671940337973699936954513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10447960225315799957969675 15671940337973699936954513)
        ·
          refine ⟨11753955253480274952715885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15671940337973699936954513 11753955253480274952715885)
          ·
            refine ⟨4407733220055103107268457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11753955253480274952715885 4407733220055103107268457)
            ·
              refine ⟨3305799915041327330451343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4407733220055103107268457 3305799915041327330451343)
              ·
                refine ⟨4958699872561990995677015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305799915041327330451343 4958699872561990995677015)
                ·
                  refine ⟨7438049808842986493515523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958699872561990995677015 7438049808842986493515523)
                  ·
                    refine ⟨11157074713264479740273285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7438049808842986493515523 11157074713264479740273285)
                    ·
                      refine ⟨2091951508737089951301241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11157074713264479740273285 2091951508737089951301241)
                      ·
                        rfl

theorem cell23_4074061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4074061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074061 prefixEnd_4074061 := by exact prefixLift 4074061
  have htrace : WordTrace (prefixWord ++ tailWord_4074061) baseStart_4074061 baseEnd_4074061 := by
    simpa [prefixWord, tailWord_4074061, baseEnd_4074061] using wordTrace_append hprefix tailTrace_4074061
  have hstable : (prefixWord ++ tailWord_4074061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074061).length < 2 ^ (prefixWord ++ tailWord_4074061).sum := by decide
  have hdescent : baseEnd_4074061 < baseStart_4074061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074094 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_4074094 : Nat := 118140960795 + 4074094 * 2 ^ 59
def prefixEnd_4074094 : Nat := 4983230072969 + 3 ^ 40 * 4074094 * 2
def baseEnd_4074094 : Nat := 2091968453598688322188589

theorem tailTrace_4074094 : CollatzResearch.WordTrace tailWord_4074094 prefixEnd_4074094 2091968453598688322188589 := by
  unfold tailWord_4074094
  simp only [CollatzResearch.WordTrace]
  refine ⟨18574301962782589088106667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99062943801507141803235557 18574301962782589088106667)
  ·
    refine ⟨27861452944173883632160001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18574301962782589088106667 27861452944173883632160001)
    ·
      refine ⟨20896089708130412724120001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27861452944173883632160001 20896089708130412724120001)
      ·
        refine ⟨15672067281097809543090001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20896089708130412724120001 15672067281097809543090001)
        ·
          refine ⟨11754050460823357157317501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15672067281097809543090001 11754050460823357157317501)
          ·
            refine ⟨4407768922808758933994063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11754050460823357157317501 4407768922808758933994063)
            ·
              refine ⟨6611653384213138400991095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407768922808758933994063 6611653384213138400991095)
              ·
                refine ⟨9917480076319707601486643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611653384213138400991095 9917480076319707601486643)
                ·
                  refine ⟨14876220114479561402229965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917480076319707601486643 14876220114479561402229965)
                  ·
                    refine ⟨5578582542929835525836237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14876220114479561402229965 5578582542929835525836237)
                    ·
                      refine ⟨2091968453598688322188589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578582542929835525836237 2091968453598688322188589)
                      ·
                        rfl

theorem cell23_4074094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_4074094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074094 prefixEnd_4074094 := by exact prefixLift 4074094
  have htrace : WordTrace (prefixWord ++ tailWord_4074094) baseStart_4074094 baseEnd_4074094 := by
    simpa [prefixWord, tailWord_4074094, baseEnd_4074094] using wordTrace_append hprefix tailTrace_4074094
  have hstable : (prefixWord ++ tailWord_4074094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074094).length < 2 ^ (prefixWord ++ tailWord_4074094).sum := by decide
  have hdescent : baseEnd_4074094 < baseStart_4074094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074207 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 6, 2]
def baseStart_4074207 : Nat := 118140960795 + 4074207 * 2 ^ 59
def prefixEnd_4074207 : Nat := 4983230072969 + 3 ^ 40 * 4074207 * 2
def baseEnd_4074207 : Nat := 2092026476912646380075569

theorem tailTrace_4074207 : CollatzResearch.WordTrace tailWord_4074207 prefixEnd_4074207 2092026476912646380075569 := by
  unfold tailWord_4074207
  simp only [CollatzResearch.WordTrace]
  refine ⟨148598537150851333003716875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99065691433900888669144583 148598537150851333003716875)
  ·
    refine ⟨222897805726276999505575313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148598537150851333003716875 222897805726276999505575313)
    ·
      refine ⟨167173354294707749629181485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222897805726276999505575313 167173354294707749629181485)
      ·
        refine ⟨62690007860515406110943057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167173354294707749629181485 62690007860515406110943057)
        ·
          refine ⟨47017505895386554583207293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62690007860515406110943057 47017505895386554583207293)
          ·
            refine ⟨17631564710769957968702735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47017505895386554583207293 17631564710769957968702735)
            ·
              refine ⟨26447347066154936953054103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17631564710769957968702735 26447347066154936953054103)
              ·
                refine ⟨39671020599232405429581155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26447347066154936953054103 39671020599232405429581155)
                ·
                  refine ⟨59506530898848608144371733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39671020599232405429581155 59506530898848608144371733)
                  ·
                    refine ⟨2789368635883528506767425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59506530898848608144371733 2789368635883528506767425)
                    ·
                      refine ⟨2092026476912646380075569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789368635883528506767425 2092026476912646380075569)
                      ·
                        rfl

theorem cell23_4074207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_4074207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074207 prefixEnd_4074207 := by exact prefixLift 4074207
  have htrace : WordTrace (prefixWord ++ tailWord_4074207) baseStart_4074207 baseEnd_4074207 := by
    simpa [prefixWord, tailWord_4074207, baseEnd_4074207] using wordTrace_append hprefix tailTrace_4074207
  have hstable : (prefixWord ++ tailWord_4074207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074207).length < 2 ^ (prefixWord ++ tailWord_4074207).sum := by decide
  have hdescent : baseEnd_4074207 < baseStart_4074207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074234 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_4074234 : Nat := 118140960795 + 4074234 * 2 ^ 59
def prefixEnd_4074234 : Nat := 4983230072969 + 3 ^ 40 * 4074234 * 2
def baseEnd_4074234 : Nat := 697346780296772591479315

theorem tailTrace_4074234 : CollatzResearch.WordTrace tailWord_4074234 prefixEnd_4074234 697346780296772591479315 := by
  unfold tailWord_4074234
  simp only [CollatzResearch.WordTrace]
  refine ⟨37149880480438379153737439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99066347947835677743299837 37149880480438379153737439)
  ·
    refine ⟨55724820720657568730606159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37149880480438379153737439 55724820720657568730606159)
    ·
      refine ⟨83587231080986353095909239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55724820720657568730606159 83587231080986353095909239)
      ·
        refine ⟨125380846621479529643863859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83587231080986353095909239 125380846621479529643863859)
        ·
          refine ⟨188071269932219294465795789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125380846621479529643863859 188071269932219294465795789)
          ·
            refine ⟨70526726224582235424673421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188071269932219294465795789 70526726224582235424673421)
            ·
              refine ⟨26447522334218338284252533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70526726224582235424673421 26447522334218338284252533)
              ·
                refine ⟨2479455218832969214148675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26447522334218338284252533 2479455218832969214148675)
                ·
                  refine ⟨3719182828249453821223013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479455218832969214148675 3719182828249453821223013)
                  ·
                    refine ⟨697346780296772591479315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3719182828249453821223013 697346780296772591479315)
                    ·
                      rfl

theorem cell23_4074234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_4074234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074234 prefixEnd_4074234 := by exact prefixLift 4074234
  have htrace : WordTrace (prefixWord ++ tailWord_4074234) baseStart_4074234 baseEnd_4074234 := by
    simpa [prefixWord, tailWord_4074234, baseEnd_4074234] using wordTrace_append hprefix tailTrace_4074234
  have hstable : (prefixWord ++ tailWord_4074234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074234).length < 2 ^ (prefixWord ++ tailWord_4074234).sum := by decide
  have hdescent : baseEnd_4074234 < baseStart_4074234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074247 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 8]
def baseStart_4074247 : Nat := 118140960795 + 4074247 * 2 ^ 59
def prefixEnd_4074247 : Nat := 4983230072969 + 3 ^ 40 * 4074247 * 2
def baseEnd_4074247 : Nat := 232449668459869580397265

theorem tailTrace_4074247 : CollatzResearch.WordTrace tailWord_4074247 prefixEnd_4074247 232449668459869580397265 := by
  unfold tailWord_4074247
  simp only [CollatzResearch.WordTrace]
  refine ⟨148599996070706419835172995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99066664047137613223448663 148599996070706419835172995)
  ·
    refine ⟨222899994106059629752759493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148599996070706419835172995 222899994106059629752759493)
    ·
      refine ⟨41793748894886180578642405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222899994106059629752759493 41793748894886180578642405)
      ·
        refine ⟨7836327917791158858495451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41793748894886180578642405 7836327917791158858495451)
        ·
          refine ⟨11754491876686738287743177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836327917791158858495451 11754491876686738287743177)
          ·
            refine ⟨8815868907515053715807383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11754491876686738287743177 8815868907515053715807383)
            ·
              refine ⟨13223803361272580573711075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815868907515053715807383 13223803361272580573711075)
              ·
                refine ⟨19835705041908870860566613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13223803361272580573711075 19835705041908870860566613)
                ·
                  refine ⟨232449668459869580397265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19835705041908870860566613 232449668459869580397265)
                  ·
                    rfl

theorem cell23_4074247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 8].length) (baseStart_4074247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074247 prefixEnd_4074247 := by exact prefixLift 4074247
  have htrace : WordTrace (prefixWord ++ tailWord_4074247) baseStart_4074247 baseEnd_4074247 := by
    simpa [prefixWord, tailWord_4074247, baseEnd_4074247] using wordTrace_append hprefix tailTrace_4074247
  have hstable : (prefixWord ++ tailWord_4074247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074247).length < 2 ^ (prefixWord ++ tailWord_4074247).sum := by decide
  have hdescent : baseEnd_4074247 < baseStart_4074247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074250 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4074250 : Nat := 118140960795 + 4074250 * 2 ^ 59
def prefixEnd_4074250 : Nat := 4983230072969 + 3 ^ 40 * 4074250 * 2
def baseEnd_4074250 : Nat := 2092048556580789711837871

theorem tailTrace_4074250 : CollatzResearch.WordTrace tailWord_4074250 prefixEnd_4074250 2092048556580789711837871 := by
  unfold tailWord_4074250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37150026372423887836883051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99066736993130367565021469 37150026372423887836883051)
  ·
    refine ⟨55725039558635831755324577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37150026372423887836883051 55725039558635831755324577)
    ·
      refine ⟨41793779668976873816493433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55725039558635831755324577 41793779668976873816493433)
      ·
        refine ⟨31345334751732655362370075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41793779668976873816493433 31345334751732655362370075)
        ·
          refine ⟨47018002127598983043555113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31345334751732655362370075 47018002127598983043555113)
          ·
            refine ⟨35263501595699237282666335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47018002127598983043555113 35263501595699237282666335)
            ·
              refine ⟨52895252393548855923999503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35263501595699237282666335 52895252393548855923999503)
              ·
                refine ⟨79342878590323283885999255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52895252393548855923999503 79342878590323283885999255)
                ·
                  refine ⟨119014317885484925828998883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79342878590323283885999255 119014317885484925828998883)
                  ·
                    refine ⟨178521476828227388743498325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119014317885484925828998883 178521476828227388743498325)
                    ·
                      refine ⟨2092048556580789711837871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 178521476828227388743498325 2092048556580789711837871)
                      ·
                        rfl

theorem cell23_4074250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4074250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074250 prefixEnd_4074250 := by exact prefixLift 4074250
  have htrace : WordTrace (prefixWord ++ tailWord_4074250) baseStart_4074250 baseEnd_4074250 := by
    simpa [prefixWord, tailWord_4074250, baseEnd_4074250] using wordTrace_append hprefix tailTrace_4074250
  have hstable : (prefixWord ++ tailWord_4074250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074250).length < 2 ^ (prefixWord ++ tailWord_4074250).sum := by decide
  have hdescent : baseEnd_4074250 < baseStart_4074250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074284 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 2, 3, 2]
def baseStart_4074284 : Nat := 118140960795 + 4074284 * 2 ^ 59
def prefixEnd_4074284 : Nat := 4983230072969 + 3 ^ 40 * 4074284 * 2
def baseEnd_4074284 : Nat := 2092066014923042578812715

theorem tailTrace_4074284 : CollatzResearch.WordTrace tailWord_4074284 prefixEnd_4074284 2092066014923042578812715 := by
  unfold tailWord_4074284
  simp only [CollatzResearch.WordTrace]
  refine ⟨74300672785786187577134953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99067563714381583436179937 74300672785786187577134953)
  ·
    refine ⟨55725504589339640682851215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74300672785786187577134953 55725504589339640682851215)
    ·
      refine ⟨83588256884009461024276823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55725504589339640682851215 83588256884009461024276823)
      ·
        refine ⟨125382385326014191536415235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83588256884009461024276823 125382385326014191536415235)
        ·
          refine ⟨188073577989021287304622853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125382385326014191536415235 188073577989021287304622853)
          ·
            refine ⟨35263795872941491369616785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188073577989021287304622853 35263795872941491369616785)
            ·
              refine ⟨26447846904706118527212589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35263795872941491369616785 26447846904706118527212589)
              ·
                refine ⟨9917942589264794447704721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26447846904706118527212589 9917942589264794447704721)
                ·
                  refine ⟨7438456941948595835778541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917942589264794447704721 7438456941948595835778541)
                  ·
                    refine ⟨2789421353230723438416953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7438456941948595835778541 2789421353230723438416953)
                    ·
                      refine ⟨2092066014923042578812715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789421353230723438416953 2092066014923042578812715)
                      ·
                        rfl

theorem cell23_4074284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_4074284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074284 prefixEnd_4074284 := by exact prefixLift 4074284
  have htrace : WordTrace (prefixWord ++ tailWord_4074284) baseStart_4074284 baseEnd_4074284 := by
    simpa [prefixWord, tailWord_4074284, baseEnd_4074284] using wordTrace_append hprefix tailTrace_4074284
  have hstable : (prefixWord ++ tailWord_4074284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074284).length < 2 ^ (prefixWord ++ tailWord_4074284).sum := by decide
  have hdescent : baseEnd_4074284 < baseStart_4074284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074307 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 4, 4]
def baseStart_4074307 : Nat := 118140960795 + 4074307 * 2 ^ 59
def prefixEnd_4074307 : Nat := 4983230072969 + 3 ^ 40 * 4074307 * 2
def baseEnd_4074307 : Nat := 697359274992698662941703

theorem tailTrace_4074307 : CollatzResearch.WordTrace tailWord_4074307 prefixEnd_4074307 697359274992698662941703 := by
  unfold tailWord_4074307
  simp only [CollatzResearch.WordTrace]
  refine ⟨148602184450489050082357175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99068122966992700054904783 148602184450489050082357175)
  ·
    refine ⟨222903276675733575123535763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148602184450489050082357175 222903276675733575123535763)
    ·
      refine ⟨334354915013600362685303645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222903276675733575123535763 334354915013600362685303645)
      ·
        refine ⟨125383093130100136006988867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334354915013600362685303645 125383093130100136006988867)
        ·
          refine ⟨188074639695150204010483301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125383093130100136006988867 188074639695150204010483301)
          ·
            refine ⟨35263994942840663251965619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188074639695150204010483301 35263994942840663251965619)
            ·
              refine ⟨52895992414260994877948429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35263994942840663251965619 52895992414260994877948429)
              ·
                refine ⟨19835997155347873079230661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52895992414260994877948429 19835997155347873079230661)
                ·
                  refine ⟨3719249466627726202355749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19835997155347873079230661 3719249466627726202355749)
                  ·
                    refine ⟨697359274992698662941703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3719249466627726202355749 697359274992698662941703)
                    ·
                      rfl

theorem cell23_4074307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 4].length) (baseStart_4074307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074307 prefixEnd_4074307 := by exact prefixLift 4074307
  have htrace : WordTrace (prefixWord ++ tailWord_4074307) baseStart_4074307 baseEnd_4074307 := by
    simpa [prefixWord, tailWord_4074307, baseEnd_4074307] using wordTrace_append hprefix tailTrace_4074307
  have hstable : (prefixWord ++ tailWord_4074307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074307).length < 2 ^ (prefixWord ++ tailWord_4074307).sum := by decide
  have hdescent : baseEnd_4074307 < baseStart_4074307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074320 : List Nat := [2, 1, 1, 1, 1, 4, 3, 10]
def baseStart_4074320 : Nat := 118140960795 + 4074320 * 2 ^ 59
def prefixEnd_4074320 : Nat := 4983230072969 + 3 ^ 40 * 4074320 * 2
def baseEnd_4074320 : Nat := 77484611119503868072687

theorem tailTrace_4074320 : CollatzResearch.WordTrace tailWord_4074320 prefixEnd_4074320 77484611119503868072687 := by
  unfold tailWord_4074320
  simp only [CollatzResearch.WordTrace]
  refine ⟨74301329299720976651290207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99068439066294635535053609 74301329299720976651290207)
  ·
    refine ⟨111451993949581464976935311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74301329299720976651290207 111451993949581464976935311)
    ·
      refine ⟨167177990924372197465402967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111451993949581464976935311 167177990924372197465402967)
      ·
        refine ⟨250766986386558296198104451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167177990924372197465402967 250766986386558296198104451)
        ·
          refine ⟨376150479579837444297156677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250766986386558296198104451 376150479579837444297156677)
          ·
            refine ⟨70528214921219520805716877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376150479579837444297156677 70528214921219520805716877)
            ·
              refine ⟨26448080595457320302143829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70528214921219520805716877 26448080595457320302143829)
              ·
                refine ⟨77484611119503868072687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26448080595457320302143829 77484611119503868072687)
                ·
                  rfl

theorem cell23_4074320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 10].length) (baseStart_4074320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074320 prefixEnd_4074320 := by exact prefixLift 4074320
  have htrace : WordTrace (prefixWord ++ tailWord_4074320) baseStart_4074320 baseEnd_4074320 := by
    simpa [prefixWord, tailWord_4074320, baseEnd_4074320] using wordTrace_append hprefix tailTrace_4074320
  have hstable : (prefixWord ++ tailWord_4074320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074320).length < 2 ^ (prefixWord ++ tailWord_4074320).sum := by decide
  have hdescent : baseEnd_4074320 < baseStart_4074320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074327 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_4074327 : Nat := 118140960795 + 4074327 * 2 ^ 59
def prefixEnd_4074327 : Nat := 4983230072969 + 3 ^ 40 * 4074327 * 2
def baseEnd_4074327 : Nat := 2092088094591185910575017

theorem tailTrace_4074327 : CollatzResearch.WordTrace tailWord_4074327 prefixEnd_4074327 2092088094591185910575017 := by
  unfold tailWord_4074327
  simp only [CollatzResearch.WordTrace]
  refine ⟨148602913910416593498085235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99068609273611062332056823 148602913910416593498085235)
  ·
    refine ⟨222904370865624890247127853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148602913910416593498085235 222904370865624890247127853)
    ·
      refine ⟨83589139074609333842672945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222904370865624890247127853 83589139074609333842672945)
      ·
        refine ⟨62691854305957000382004709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83589139074609333842672945 62691854305957000382004709)
        ·
          refine ⟨11754722682366937571625883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62691854305957000382004709 11754722682366937571625883)
          ·
            refine ⟨17632084023550406357438825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11754722682366937571625883 17632084023550406357438825)
            ·
              refine ⟨13224063017662804768079119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17632084023550406357438825 13224063017662804768079119)
              ·
                refine ⟨19836094526494207152118679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13224063017662804768079119 19836094526494207152118679)
                ·
                  refine ⟨29754141789741310728178019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19836094526494207152118679 29754141789741310728178019)
                  ·
                    refine ⟨44631212684611966092267029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29754141789741310728178019 44631212684611966092267029)
                    ·
                      refine ⟨2092088094591185910575017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44631212684611966092267029 2092088094591185910575017)
                      ·
                        rfl

theorem cell23_4074327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_4074327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074327 prefixEnd_4074327 := by exact prefixLift 4074327
  have htrace : WordTrace (prefixWord ++ tailWord_4074327) baseStart_4074327 baseEnd_4074327 := by
    simpa [prefixWord, tailWord_4074327, baseEnd_4074327] using wordTrace_append hprefix tailTrace_4074327
  have hstable : (prefixWord ++ tailWord_4074327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074327).length < 2 ^ (prefixWord ++ tailWord_4074327).sum := by decide
  have hdescent : baseEnd_4074327 < baseStart_4074327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074344 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4074344 : Nat := 118140960795 + 4074344 * 2 ^ 59
def prefixEnd_4074344 : Nat := 4983230072969 + 3 ^ 40 * 4074344 * 2
def baseEnd_4074344 : Nat := 2092096823762312344062439

theorem tailTrace_4074344 : CollatzResearch.WordTrace tailWord_4074344 prefixEnd_4074344 2092096823762312344062439 := by
  unfold tailWord_4074344
  simp only [CollatzResearch.WordTrace]
  refine ⟨74301766975677502700727043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99069022634236670267636057 74301766975677502700727043)
  ·
    refine ⟨111452650463516254051090565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74301766975677502700727043 111452650463516254051090565)
    ·
      refine ⟨20897371961909297634579481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111452650463516254051090565 20897371961909297634579481)
      ·
        refine ⟨15673028971431973225934611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20897371961909297634579481 15673028971431973225934611)
        ·
          refine ⟨23509543457147959838901917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15673028971431973225934611 23509543457147959838901917)
          ·
            refine ⟨8816078796430484939588219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23509543457147959838901917 8816078796430484939588219)
            ·
              refine ⟨13224118194645727409382329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816078796430484939588219 13224118194645727409382329)
              ·
                refine ⟨9918088645984295557036747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13224118194645727409382329 9918088645984295557036747)
                ·
                  refine ⟨14877132968976443335555121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918088645984295557036747 14877132968976443335555121)
                  ·
                    refine ⟨11157849726732332501666341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14877132968976443335555121 11157849726732332501666341)
                    ·
                      refine ⟨2092096823762312344062439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11157849726732332501666341 2092096823762312344062439)
                      ·
                        rfl

theorem cell23_4074344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4074344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074344 prefixEnd_4074344 := by exact prefixLift 4074344
  have htrace : WordTrace (prefixWord ++ tailWord_4074344) baseStart_4074344 baseEnd_4074344 := by
    simpa [prefixWord, tailWord_4074344, baseEnd_4074344] using wordTrace_append hprefix tailTrace_4074344
  have hstable : (prefixWord ++ tailWord_4074344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074344).length < 2 ^ (prefixWord ++ tailWord_4074344).sum := by decide
  have hdescent : baseEnd_4074344 < baseStart_4074344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074347 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 3]
def baseStart_4074347 : Nat := 118140960795 + 4074347 * 2 ^ 59
def prefixEnd_4074347 : Nat := 4983230072969 + 3 ^ 40 * 4074347 * 2
def baseEnd_4074347 : Nat := 2092098364204275832324925

theorem tailTrace_4074347 : CollatzResearch.WordTrace tailWord_4074347 prefixEnd_4074347 2092098364204275832324925 := by
  unfold tailWord_4074347
  simp only [CollatzResearch.WordTrace]
  refine ⟨148603643370344136913813295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99069095580229424609208863 148603643370344136913813295)
  ·
    refine ⟨222905465055516205370719943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148603643370344136913813295 222905465055516205370719943)
    ·
      refine ⟨334358197583274308056079915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222905465055516205370719943 334358197583274308056079915)
      ·
        refine ⟨501537296374911462084119873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334358197583274308056079915 501537296374911462084119873)
        ·
          refine ⟨376152972281183596563089905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501537296374911462084119873 376152972281183596563089905)
          ·
            refine ⟨282114729210887697422317429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376152972281183596563089905 282114729210887697422317429)
            ·
              refine ⟨26448255863520721633342259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282114729210887697422317429 26448255863520721633342259)
              ·
                refine ⟨39672383795281082450013389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26448255863520721633342259 39672383795281082450013389)
                ·
                  refine ⟨14877143923230405918755021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39672383795281082450013389 14877143923230405918755021)
                  ·
                    refine ⟨5578928971211402219533133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14877143923230405918755021 5578928971211402219533133)
                    ·
                      refine ⟨2092098364204275832324925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578928971211402219533133 2092098364204275832324925)
                      ·
                        rfl

theorem cell23_4074347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 3].length) (baseStart_4074347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074347 prefixEnd_4074347 := by exact prefixLift 4074347
  have htrace : WordTrace (prefixWord ++ tailWord_4074347) baseStart_4074347 baseEnd_4074347 := by
    simpa [prefixWord, tailWord_4074347, baseEnd_4074347] using wordTrace_append hprefix tailTrace_4074347
  have hstable : (prefixWord ++ tailWord_4074347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074347).length < 2 ^ (prefixWord ++ tailWord_4074347).sum := by decide
  have hdescent : baseEnd_4074347 < baseStart_4074347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074348 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 1, 2, 2]
def baseStart_4074348 : Nat := 118140960795 + 4074348 * 2 ^ 59
def prefixEnd_4074348 : Nat := 4983230072969 + 3 ^ 40 * 4074348 * 2
def baseEnd_4074348 : Nat := 2092098877684930328412421

theorem tailTrace_4074348 : CollatzResearch.WordTrace tailWord_4074348 prefixEnd_4074348 2092098877684930328412421 := by
  unfold tailWord_4074348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74301839921670257042299849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99069119895560342723066465 74301839921670257042299849)
  ·
    refine ⟨55726379941252692781724887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74301839921670257042299849 55726379941252692781724887)
    ·
      refine ⟨83589569911879039172587331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55726379941252692781724887 83589569911879039172587331)
      ·
        refine ⟨125384354867818558758880997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83589569911879039172587331 125384354867818558758880997)
        ·
          refine ⟨23509566537715979767290187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125384354867818558758880997 23509566537715979767290187)
          ·
            refine ⟨35264349806573969650935281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23509566537715979767290187 35264349806573969650935281)
            ·
              refine ⟨26448262354930477238201461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35264349806573969650935281 26448262354930477238201461)
              ·
                refine ⟨2479524595774732241081387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26448262354930477238201461 2479524595774732241081387)
                ·
                  refine ⟨3719286893662098361622081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479524595774732241081387 3719286893662098361622081)
                  ·
                    refine ⟨2789465170246573771216561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3719286893662098361622081 2789465170246573771216561)
                    ·
                      refine ⟨2092098877684930328412421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789465170246573771216561 2092098877684930328412421)
                      ·
                        rfl

theorem cell23_4074348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_4074348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074348 prefixEnd_4074348 := by exact prefixLift 4074348
  have htrace : WordTrace (prefixWord ++ tailWord_4074348) baseStart_4074348 baseEnd_4074348 := by
    simpa [prefixWord, tailWord_4074348, baseEnd_4074348] using wordTrace_append hprefix tailTrace_4074348
  have hstable : (prefixWord ++ tailWord_4074348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074348).length < 2 ^ (prefixWord ++ tailWord_4074348).sum := by decide
  have hdescent : baseEnd_4074348 < baseStart_4074348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074358 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_4074358 : Nat := 118140960795 + 4074358 * 2 ^ 59
def prefixEnd_4074358 : Nat := 4983230072969 + 3 ^ 40 * 4074358 * 2
def baseEnd_4074358 : Nat := 697368004163825096429125

theorem tailTrace_4074358 : CollatzResearch.WordTrace tailWord_4074358 prefixEnd_4074358 697368004163825096429125 := by
  unfold tailWord_4074358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287752785831517862028983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99069363048869523861642485 9287752785831517862028983)
  ·
    refine ⟨13931629178747276793043475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9287752785831517862028983 13931629178747276793043475)
    ·
      refine ⟨20897443768120915189565213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13931629178747276793043475 20897443768120915189565213)
      ·
        refine ⟨7836541413045343196086955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20897443768120915189565213 7836541413045343196086955)
        ·
          refine ⟨11754812119568014794130433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836541413045343196086955 11754812119568014794130433)
          ·
            refine ⟨8816109089676011095597825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11754812119568014794130433 8816109089676011095597825)
            ·
              refine ⟨6612081817257008321698369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816109089676011095597825 6612081817257008321698369)
              ·
                refine ⟨4959061362942756241273777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612081817257008321698369 4959061362942756241273777)
                ·
                  refine ⟨3719296022207067180955333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4959061362942756241273777 3719296022207067180955333)
                  ·
                    refine ⟨697368004163825096429125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3719296022207067180955333 697368004163825096429125)
                    ·
                      rfl

theorem cell23_4074358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_4074358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074358 prefixEnd_4074358 := by exact prefixLift 4074358
  have htrace : WordTrace (prefixWord ++ tailWord_4074358) baseStart_4074358 baseEnd_4074358 := by
    simpa [prefixWord, tailWord_4074358, baseEnd_4074358] using wordTrace_append hprefix tailTrace_4074358
  have hstable : (prefixWord ++ tailWord_4074358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074358).length < 2 ^ (prefixWord ++ tailWord_4074358).sum := by decide
  have hdescent : baseEnd_4074358 < baseStart_4074358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074364 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_4074364 : Nat := 118140960795 + 4074364 * 2 ^ 59
def prefixEnd_4074364 : Nat := 4983230072969 + 3 ^ 40 * 4074364 * 2
def baseEnd_4074364 : Nat := 2092107093375402265812347

theorem tailTrace_4074364 : CollatzResearch.WordTrace tailWord_4074364 prefixEnd_4074364 2092107093375402265812347 := by
  unfold tailWord_4074364
  simp only [CollatzResearch.WordTrace]
  refine ⟨74302131705641274408591073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99069508940855032544788097 74302131705641274408591073)
  ·
    refine ⟨55726598779230955806443305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74302131705641274408591073 55726598779230955806443305)
    ·
      refine ⟨41794949084423216854832479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55726598779230955806443305 41794949084423216854832479)
      ·
        refine ⟨62692423626634825282248719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41794949084423216854832479 62692423626634825282248719)
        ·
          refine ⟨94038635439952237923373079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62692423626634825282248719 94038635439952237923373079)
          ·
            refine ⟨141057953159928356885059619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94038635439952237923373079 141057953159928356885059619)
            ·
              refine ⟨211586929739892535327589429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141057953159928356885059619 211586929739892535327589429)
              ·
                refine ⟨19836274663114925186961509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211586929739892535327589429 19836274663114925186961509)
                ·
                  refine ⟨3719301499334048472555283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19836274663114925186961509 3719301499334048472555283)
                  ·
                    refine ⟨5578952249001072708832925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3719301499334048472555283 5578952249001072708832925)
                    ·
                      refine ⟨2092107093375402265812347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5578952249001072708832925 2092107093375402265812347)
                      ·
                        rfl

theorem cell23_4074364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_4074364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074364 prefixEnd_4074364 := by exact prefixLift 4074364
  have htrace : WordTrace (prefixWord ++ tailWord_4074364) baseStart_4074364 baseEnd_4074364 := by
    simpa [prefixWord, tailWord_4074364, baseEnd_4074364] using wordTrace_append hprefix tailTrace_4074364
  have hstable : (prefixWord ++ tailWord_4074364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074364).length < 2 ^ (prefixWord ++ tailWord_4074364).sum := by decide
  have hdescent : baseEnd_4074364 < baseStart_4074364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074365 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_4074365 : Nat := 118140960795 + 4074365 * 2 ^ 59
def prefixEnd_4074365 : Nat := 4983230072969 + 3 ^ 40 * 4074365 * 2
def baseEnd_4074365 : Nat := 2092107606856056761899843

theorem tailTrace_4074365 : CollatzResearch.WordTrace tailWord_4074365 prefixEnd_4074365 2092107606856056761899843 := by
  unfold tailWord_4074365
  simp only [CollatzResearch.WordTrace]
  refine ⟨148604299884278925987968549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99069533256185950658645699 148604299884278925987968549)
  ·
    refine ⟨27863306228302298622744103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148604299884278925987968549 27863306228302298622744103)
    ·
      refine ⟨41794959342453447934116155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27863306228302298622744103 41794959342453447934116155)
      ·
        refine ⟨62692439013680171901174233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41794959342453447934116155 62692439013680171901174233)
        ·
          refine ⟨47019329260260128925880675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62692439013680171901174233 47019329260260128925880675)
          ·
            refine ⟨70528993890390193388821013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47019329260260128925880675 70528993890390193388821013)
            ·
              refine ⟨3306046588612040315100985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70528993890390193388821013 3306046588612040315100985)
              ·
                refine ⟨2479534941459030236325739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306046588612040315100985 2479534941459030236325739)
                ·
                  refine ⟨3719302412188545354488609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479534941459030236325739 3719302412188545354488609)
                  ·
                    refine ⟨2789476809141409015866457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3719302412188545354488609 2789476809141409015866457)
                    ·
                      refine ⟨2092107606856056761899843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789476809141409015866457 2092107606856056761899843)
                      ·
                        rfl

theorem cell23_4074365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_4074365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074365 prefixEnd_4074365 := by exact prefixLift 4074365
  have htrace : WordTrace (prefixWord ++ tailWord_4074365) baseStart_4074365 baseEnd_4074365 := by
    simpa [prefixWord, tailWord_4074365, baseEnd_4074365] using wordTrace_append hprefix tailTrace_4074365
  have hstable : (prefixWord ++ tailWord_4074365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074365).length < 2 ^ (prefixWord ++ tailWord_4074365).sum := by decide
  have hdescent : baseEnd_4074365 < baseStart_4074365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074391 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 1, 3, 2]
def baseStart_4074391 : Nat := 118140960795 + 4074391 * 2 ^ 59
def prefixEnd_4074391 : Nat := 4983230072969 + 3 ^ 40 * 4074391 * 2
def baseEnd_4074391 : Nat := 2092120957353073660174723

theorem tailTrace_4074391 : CollatzResearch.WordTrace tailWord_4074391 prefixEnd_4074391 2092120957353073660174723 := by
  unfold tailWord_4074391
  simp only [CollatzResearch.WordTrace]
  refine ⟨148605248182184732428415027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99070165454789821618943351 148605248182184732428415027)
  ·
    refine ⟨222907872273277098642622541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148605248182184732428415027 222907872273277098642622541)
    ·
      refine ⟨83590452102478911990983453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222907872273277098642622541 83590452102478911990983453)
      ·
        refine ⟨31346419538429591996618795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83590452102478911990983453 31346419538429591996618795)
        ·
          refine ⟨47019629307644387994928193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31346419538429591996618795 47019629307644387994928193)
          ·
            refine ⟨35264721980733290996196145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47019629307644387994928193 35264721980733290996196145)
            ·
              refine ⟨26448541485549968247147109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35264721980733290996196145 26448541485549968247147109)
              ·
                refine ⟨4959101528540619046340083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26448541485549968247147109 4959101528540619046340083)
                ·
                  refine ⟨7438652292810928569510125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959101528540619046340083 7438652292810928569510125)
                  ·
                    refine ⟨2789494609804098213566297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7438652292810928569510125 2789494609804098213566297)
                    ·
                      refine ⟨2092120957353073660174723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789494609804098213566297 2092120957353073660174723)
                      ·
                        rfl

theorem cell23_4074391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_4074391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074391 prefixEnd_4074391 := by exact prefixLift 4074391
  have htrace : WordTrace (prefixWord ++ tailWord_4074391) baseStart_4074391 baseEnd_4074391 := by
    simpa [prefixWord, tailWord_4074391, baseEnd_4074391] using wordTrace_append hprefix tailTrace_4074391
  have hstable : (prefixWord ++ tailWord_4074391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074391).length < 2 ^ (prefixWord ++ tailWord_4074391).sum := by decide
  have hdescent : baseEnd_4074391 < baseStart_4074391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
