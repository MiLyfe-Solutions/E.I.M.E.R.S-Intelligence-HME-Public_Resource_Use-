import V185TrunkScan23Chunk0508

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3010733 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3010733 : Nat := 118140960795 + 3010733 * 2 ^ 59
def prefixEnd_3010733 : Nat := 4983230072969 + 3 ^ 40 * 3010733 * 2
def baseEnd_3010733 : Nat := 1545953151353074226991397

theorem tailTrace_3010733 : CollatzResearch.WordTrace tailWord_3010733 prefixEnd_3010733 1545953151353074226991397 := by
  unfold tailWord_3010733
  simp only [CollatzResearch.WordTrace]
  refine ⟨109810453801636008104572853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73206969201090672069715235 109810453801636008104572853)
  ·
    refine ⟨10294730043903375759803705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109810453801636008104572853 10294730043903375759803705)
    ·
      refine ⟨7721047532927531819852779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10294730043903375759803705 7721047532927531819852779)
      ·
        refine ⟨11581571299391297729779169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7721047532927531819852779 11581571299391297729779169)
        ·
          refine ⟨8686178474543473297334377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11581571299391297729779169 8686178474543473297334377)
          ·
            refine ⟨6514633855907604973000783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8686178474543473297334377 6514633855907604973000783)
            ·
              refine ⟨9771950783861407459501175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514633855907604973000783 9771950783861407459501175)
              ·
                refine ⟨14657926175792111189251763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771950783861407459501175 14657926175792111189251763)
                ·
                  refine ⟨21986889263688166783877645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14657926175792111189251763 21986889263688166783877645)
                  ·
                    refine ⟨8245083473883062543954117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21986889263688166783877645 8245083473883062543954117)
                    ·
                      refine ⟨1545953151353074226991397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8245083473883062543954117 1545953151353074226991397)
                      ·
                        rfl

theorem cell23_3010733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3010733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010733 prefixEnd_3010733 := by exact prefixLift 3010733
  have htrace : WordTrace (prefixWord ++ tailWord_3010733) baseStart_3010733 baseEnd_3010733 := by
    simpa [prefixWord, tailWord_3010733, baseEnd_3010733] using wordTrace_append hprefix tailTrace_3010733
  have hstable : (prefixWord ++ tailWord_3010733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010733).length < 2 ^ (prefixWord ++ tailWord_3010733).sum := by decide
  have hdescent : baseEnd_3010733 < baseStart_3010733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010739 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 8]
def baseStart_3010739 : Nat := 118140960795 + 3010739 * 2 ^ 59
def prefixEnd_3010739 : Nat := 4983230072969 + 3 ^ 40 * 3010739 * 2
def baseEnd_3010739 : Nat := 171772914693000133724041

theorem tailTrace_3010739 : CollatzResearch.WordTrace tailWord_3010739 prefixEnd_3010739 171772914693000133724041 := by
  unfold tailWord_3010739
  simp only [CollatzResearch.WordTrace]
  refine ⟨109810672639614271129291271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73207115093076180752860847 109810672639614271129291271)
  ·
    refine ⟨164716008959421406693936907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109810672639614271129291271 164716008959421406693936907)
    ·
      refine ⟨247074013439132110040905361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164716008959421406693936907 247074013439132110040905361)
      ·
        refine ⟨185305510079349082530679021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247074013439132110040905361 185305510079349082530679021)
        ·
          refine ⟨69489566279755905949004633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185305510079349082530679021 69489566279755905949004633)
          ·
            refine ⟨52117174709816929461753475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69489566279755905949004633 52117174709816929461753475)
            ·
              refine ⟨78175762064725394192630213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52117174709816929461753475 78175762064725394192630213)
              ·
                refine ⟨14657955387136011411118165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78175762064725394192630213 14657955387136011411118165)
                ·
                  refine ⟨171772914693000133724041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14657955387136011411118165 171772914693000133724041)
                  ·
                    rfl

theorem cell23_3010739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 8].length) (baseStart_3010739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010739 prefixEnd_3010739 := by exact prefixLift 3010739
  have htrace : WordTrace (prefixWord ++ tailWord_3010739) baseStart_3010739 baseEnd_3010739 := by
    simpa [prefixWord, tailWord_3010739, baseEnd_3010739] using wordTrace_append hprefix tailTrace_3010739
  have hstable : (prefixWord ++ tailWord_3010739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010739).length < 2 ^ (prefixWord ++ tailWord_3010739).sum := by decide
  have hdescent : baseEnd_3010739 < baseStart_3010739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010779 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_3010779 : Nat := 118140960795 + 3010779 * 2 ^ 59
def prefixEnd_3010779 : Nat := 4983230072969 + 3 ^ 40 * 3010779 * 2
def baseEnd_3010779 : Nat := 1545976771463181047016185

theorem tailTrace_3010779 : CollatzResearch.WordTrace tailWord_3010779 prefixEnd_3010779 1545976771463181047016185 := by
  unfold tailWord_3010779
  simp only [CollatzResearch.WordTrace]
  refine ⟨109812131559469357960747391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73208087706312905307164927 109812131559469357960747391)
  ·
    refine ⟨164718197339204036941121087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109812131559469357960747391 164718197339204036941121087)
    ·
      refine ⟨247077296008806055411681631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164718197339204036941121087 247077296008806055411681631)
      ·
        refine ⟨370615944013209083117522447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247077296008806055411681631 370615944013209083117522447)
        ·
          refine ⟨555923916019813624676283671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370615944013209083117522447 555923916019813624676283671)
          ·
            refine ⟨833885874029720437014425507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555923916019813624676283671 833885874029720437014425507)
            ·
              refine ⟨1250828811044580655521638261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833885874029720437014425507 1250828811044580655521638261)
              ·
                refine ⟨117265201035429436455153587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250828811044580655521638261 117265201035429436455153587)
                ·
                  refine ⟨175897801553144154682730381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117265201035429436455153587 175897801553144154682730381)
                  ·
                    refine ⟨65961675582429058006023893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175897801553144154682730381 65961675582429058006023893)
                    ·
                      refine ⟨1545976771463181047016185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65961675582429058006023893 1545976771463181047016185)
                      ·
                        rfl

theorem cell23_3010779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_3010779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010779 prefixEnd_3010779 := by exact prefixLift 3010779
  have htrace : WordTrace (prefixWord ++ tailWord_3010779) baseStart_3010779 baseEnd_3010779 := by
    simpa [prefixWord, tailWord_3010779, baseEnd_3010779] using wordTrace_append hprefix tailTrace_3010779
  have hstable : (prefixWord ++ tailWord_3010779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010779).length < 2 ^ (prefixWord ++ tailWord_3010779).sum := by decide
  have hdescent : baseEnd_3010779 < baseStart_3010779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010810 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2]
def baseStart_3010810 : Nat := 118140960795 + 3010810 * 2 ^ 59
def prefixEnd_3010810 : Nat := 4983230072969 + 3 ^ 40 * 3010810 * 2
def baseEnd_3010810 : Nat := 1545992689363470425728543

theorem tailTrace_3010810 : CollatzResearch.WordTrace tailWord_3010810 prefixEnd_3010810 1545992689363470425728543 := by
  unfold tailWord_3010810
  simp only [CollatzResearch.WordTrace]
  refine ⟨27453315555589262563781471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73208841481571366836750589 27453315555589262563781471)
  ·
    refine ⟨41179973333383893845672207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27453315555589262563781471 41179973333383893845672207)
    ·
      refine ⟨61769960000075840768508311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41179973333383893845672207 61769960000075840768508311)
      ·
        refine ⟨92654940000113761152762467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61769960000075840768508311 92654940000113761152762467)
        ·
          refine ⟨138982410000170641729143701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92654940000113761152762467 138982410000170641729143701)
          ·
            refine ⟨6514800468757998831053611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138982410000170641729143701 6514800468757998831053611)
            ·
              refine ⟨9772200703136998246580417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514800468757998831053611 9772200703136998246580417)
              ·
                refine ⟨7329150527352748684935313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9772200703136998246580417 7329150527352748684935313)
                ·
                  refine ⟨5496862895514561513701485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7329150527352748684935313 5496862895514561513701485)
                  ·
                    refine ⟨2061323585817960567638057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5496862895514561513701485 2061323585817960567638057)
                    ·
                      refine ⟨1545992689363470425728543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061323585817960567638057 1545992689363470425728543)
                      ·
                        rfl

theorem cell23_3010810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_3010810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010810 prefixEnd_3010810 := by exact prefixLift 3010810
  have htrace : WordTrace (prefixWord ++ tailWord_3010810) baseStart_3010810 baseEnd_3010810 := by
    simpa [prefixWord, tailWord_3010810, baseEnd_3010810] using wordTrace_append hprefix tailTrace_3010810
  have hstable : (prefixWord ++ tailWord_3010810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010810).length < 2 ^ (prefixWord ++ tailWord_3010810).sum := by decide
  have hdescent : baseEnd_3010810 < baseStart_3010810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010840 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3010840 : Nat := 118140960795 + 3010840 * 2 ^ 59
def prefixEnd_3010840 : Nat := 4983230072969 + 3 ^ 40 * 3010840 * 2
def baseEnd_3010840 : Nat := 1546008093783105308353405

theorem tailTrace_3010840 : CollatzResearch.WordTrace tailWord_3010840 prefixEnd_3010840 1546008093783105308353405 := by
  unfold tailWord_3010840
  simp only [CollatzResearch.WordTrace]
  refine ⟨54907178206124182689358987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73209570941498910252478649 54907178206124182689358987)
  ·
    refine ⟨82360767309186274034038481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54907178206124182689358987 82360767309186274034038481)
    ·
      refine ⟨61770575481889705525528861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82360767309186274034038481 61770575481889705525528861)
      ·
        refine ⟨23163965805708639572073323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61770575481889705525528861 23163965805708639572073323)
        ·
          refine ⟨34745948708562959358109985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23163965805708639572073323 34745948708562959358109985)
          ·
            refine ⟨26059461531422219518582489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34745948708562959358109985 26059461531422219518582489)
            ·
              refine ⟨19544596148566664638936867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26059461531422219518582489 19544596148566664638936867)
              ·
                refine ⟨29316894222849996958405301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19544596148566664638936867 29316894222849996958405301)
                ·
                  refine ⟨2748458833392187214850497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29316894222849996958405301 2748458833392187214850497)
                  ·
                    refine ⟨2061344125044140411137873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2748458833392187214850497 2061344125044140411137873)
                    ·
                      refine ⟨1546008093783105308353405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061344125044140411137873 1546008093783105308353405)
                      ·
                        rfl

theorem cell23_3010840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3010840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010840 prefixEnd_3010840 := by exact prefixLift 3010840
  have htrace : WordTrace (prefixWord ++ tailWord_3010840) baseStart_3010840 baseEnd_3010840 := by
    simpa [prefixWord, tailWord_3010840, baseEnd_3010840] using wordTrace_append hprefix tailTrace_3010840
  have hstable : (prefixWord ++ tailWord_3010840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010840).length < 2 ^ (prefixWord ++ tailWord_3010840).sum := by decide
  have hdescent : baseEnd_3010840 < baseStart_3010840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010874 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2]
def baseStart_3010874 : Nat := 118140960795 + 3010874 * 2 ^ 59
def prefixEnd_3010874 : Nat := 4983230072969 + 3 ^ 40 * 3010874 * 2
def baseEnd_3010874 : Nat := 1546025552125358175328249

theorem tailTrace_3010874 : CollatzResearch.WordTrace tailWord_3010874 prefixEnd_3010874 1546025552125358175328249 := by
  unfold tailWord_3010874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27453899123531297296363919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73210397662750126123637117 27453899123531297296363919)
  ·
    refine ⟨41180848685296945944545879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27453899123531297296363919 41180848685296945944545879)
    ·
      refine ⟨61771273027945418916818819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41180848685296945944545879 61771273027945418916818819)
      ·
        refine ⟨92656909541918128375228229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61771273027945418916818819 92656909541918128375228229)
        ·
          refine ⟨17373170539109649070355293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92656909541918128375228229 17373170539109649070355293)
          ·
            refine ⟨6514938952166118401383235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17373170539109649070355293 6514938952166118401383235)
            ·
              refine ⟨9772408428249177602074853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514938952166118401383235 9772408428249177602074853)
              ·
                refine ⟨1832326580296720800389035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9772408428249177602074853 1832326580296720800389035)
                ·
                  refine ⟨2748489870445081200583553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832326580296720800389035 2748489870445081200583553)
                  ·
                    refine ⟨2061367402833810900437665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2748489870445081200583553 2061367402833810900437665)
                    ·
                      refine ⟨1546025552125358175328249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061367402833810900437665 1546025552125358175328249)
                      ·
                        rfl

theorem cell23_3010874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_3010874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010874 prefixEnd_3010874 := by exact prefixLift 3010874
  have htrace : WordTrace (prefixWord ++ tailWord_3010874) baseStart_3010874 baseEnd_3010874 := by
    simpa [prefixWord, tailWord_3010874, baseEnd_3010874] using wordTrace_append hprefix tailTrace_3010874
  have hstable : (prefixWord ++ tailWord_3010874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010874).length < 2 ^ (prefixWord ++ tailWord_3010874).sum := by decide
  have hdescent : baseEnd_3010874 < baseStart_3010874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010876 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_3010876 : Nat := 118140960795 + 3010876 * 2 ^ 59
def prefixEnd_3010876 : Nat := 4983230072969 + 3 ^ 40 * 3010876 * 2
def baseEnd_3010876 : Nat := 515342193028889055834413

theorem tailTrace_3010876 : CollatzResearch.WordTrace tailWord_3010876 prefixEnd_3010876 515342193028889055834413 := by
  unfold tailWord_3010876
  simp only [CollatzResearch.WordTrace]
  refine ⟨54907834720058971763514241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73210446293411962351352321 54907834720058971763514241)
  ·
    refine ⟨41180876040044228822635681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54907834720058971763514241 41180876040044228822635681)
    ·
      refine ⟨30885657030033171616976761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41180876040044228822635681 30885657030033171616976761)
      ·
        refine ⟨23164242772524878712732571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30885657030033171616976761 23164242772524878712732571)
        ·
          refine ⟨34746364158787318069098857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23164242772524878712732571 34746364158787318069098857)
          ·
            refine ⟨26059773119090488551824143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34746364158787318069098857 26059773119090488551824143)
            ·
              refine ⟨39089659678635732827736215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26059773119090488551824143 39089659678635732827736215)
              ·
                refine ⟨58634489517953599241604323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39089659678635732827736215 58634489517953599241604323)
                ·
                  refine ⟨87951734276930398862406485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58634489517953599241604323 87951734276930398862406485)
                  ·
                    refine ⟨515342193028889055834413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87951734276930398862406485 515342193028889055834413)
                    ·
                      rfl

theorem cell23_3010876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_3010876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010876 prefixEnd_3010876 := by exact prefixLift 3010876
  have htrace : WordTrace (prefixWord ++ tailWord_3010876) baseStart_3010876 baseEnd_3010876 := by
    simpa [prefixWord, tailWord_3010876, baseEnd_3010876] using wordTrace_append hprefix tailTrace_3010876
  have hstable : (prefixWord ++ tailWord_3010876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010876).length < 2 ^ (prefixWord ++ tailWord_3010876).sum := by decide
  have hdescent : baseEnd_3010876 < baseStart_3010876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010906 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_3010906 : Nat := 118140960795 + 3010906 * 2 ^ 59
def prefixEnd_3010906 : Nat := 4983230072969 + 3 ^ 40 * 3010906 * 2
def baseEnd_3010906 : Nat := 515347327835434016709367

theorem tailTrace_3010906 : CollatzResearch.WordTrace tailWord_3010906 prefixEnd_3010906 515347327835434016709367 := by
  unfold tailWord_3010906
  simp only [CollatzResearch.WordTrace]
  refine ⟨27454190907502314662655143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73211175753339505767080381 27454190907502314662655143)
  ·
    refine ⟨41181286361253471993982715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27454190907502314662655143 41181286361253471993982715)
    ·
      refine ⟨61771929541880207990974073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41181286361253471993982715 61771929541880207990974073)
      ·
        refine ⟨46328947156410155993230555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61771929541880207990974073 46328947156410155993230555)
        ·
          refine ⟨69493420734615233989845833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46328947156410155993230555 69493420734615233989845833)
          ·
            refine ⟨52120065550961425492384375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69493420734615233989845833 52120065550961425492384375)
            ·
              refine ⟨78180098326442138238576563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52120065550961425492384375 78180098326442138238576563)
              ·
                refine ⟨117270147489663207357864845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78180098326442138238576563 117270147489663207357864845)
                ·
                  refine ⟨43976305308623702759199317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117270147489663207357864845 43976305308623702759199317)
                  ·
                    refine ⟨515347327835434016709367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43976305308623702759199317 515347327835434016709367)
                    ·
                      rfl

theorem cell23_3010906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_3010906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010906 prefixEnd_3010906 := by exact prefixLift 3010906
  have htrace : WordTrace (prefixWord ++ tailWord_3010906) baseStart_3010906 baseEnd_3010906 := by
    simpa [prefixWord, tailWord_3010906, baseEnd_3010906] using wordTrace_append hprefix tailTrace_3010906
  have hstable : (prefixWord ++ tailWord_3010906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010906).length < 2 ^ (prefixWord ++ tailWord_3010906).sum := by decide
  have hdescent : baseEnd_3010906 < baseStart_3010906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010908 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3010908 : Nat := 118140960795 + 3010908 * 2 ^ 59
def prefixEnd_3010908 : Nat := 4983230072969 + 3 ^ 40 * 3010908 * 2
def baseEnd_3010908 : Nat := 1546043010467611042303093

theorem tailTrace_3010908 : CollatzResearch.WordTrace tailWord_3010908 prefixEnd_3010908 1546043010467611042303093 := by
  unfold tailWord_3010908
  simp only [CollatzResearch.WordTrace]
  refine ⟨54908418288001006496096689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73211224384001341994795585 54908418288001006496096689)
  ·
    refine ⟨41181313716000754872072517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54908418288001006496096689 41181313716000754872072517)
    ·
      refine ⟨7721496321750141538513597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41181313716000754872072517 7721496321750141538513597)
      ·
        refine ⟨2895561120656303076942599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7721496321750141538513597 2895561120656303076942599)
        ·
          refine ⟨4343341680984454615413899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895561120656303076942599 4343341680984454615413899)
          ·
            refine ⟨6515012521476681923120849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343341680984454615413899 6515012521476681923120849)
            ·
              refine ⟨4886259391107511442340637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6515012521476681923120849 4886259391107511442340637)
              ·
                refine ⟨1832347271665316790877739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4886259391107511442340637 1832347271665316790877739)
                ·
                  refine ⟨2748520907497975186316609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832347271665316790877739 2748520907497975186316609)
                  ·
                    refine ⟨2061390680623481389737457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2748520907497975186316609 2061390680623481389737457)
                    ·
                      refine ⟨1546043010467611042303093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061390680623481389737457 1546043010467611042303093)
                      ·
                        rfl

theorem cell23_3010908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3010908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010908 prefixEnd_3010908 := by exact prefixLift 3010908
  have htrace : WordTrace (prefixWord ++ tailWord_3010908) baseStart_3010908 baseEnd_3010908 := by
    simpa [prefixWord, tailWord_3010908, baseEnd_3010908] using wordTrace_append hprefix tailTrace_3010908
  have hstable : (prefixWord ++ tailWord_3010908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010908).length < 2 ^ (prefixWord ++ tailWord_3010908).sum := by decide
  have hdescent : baseEnd_3010908 < baseStart_3010908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010917 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 1, 3, 2]
def baseStart_3010917 : Nat := 118140960795 + 3010917 * 2 ^ 59
def prefixEnd_3010917 : Nat := 4983230072969 + 3 ^ 40 * 3010917 * 2
def baseEnd_3010917 : Nat := 1546047631793501507090551

theorem tailTrace_3010917 : CollatzResearch.WordTrace tailWord_3010917 prefixEnd_3010917 1546047631793501507090551 := by
  unfold tailWord_3010917
  simp only [CollatzResearch.WordTrace]
  refine ⟨109817164832969407529271005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73211443221979605019514003 109817164832969407529271005)
  ·
    refine ⟨41181436812363527823476627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109817164832969407529271005 41181436812363527823476627)
    ·
      refine ⟨61772155218545291735214941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41181436812363527823476627 61772155218545291735214941)
      ·
        refine ⟨23164558206954484400705603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61772155218545291735214941 23164558206954484400705603)
        ·
          refine ⟨34746837310431726601058405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23164558206954484400705603 34746837310431726601058405)
          ·
            refine ⟨6515031995705948737698451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34746837310431726601058405 6515031995705948737698451)
            ·
              refine ⟨9772547993558923106547677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515031995705948737698451 9772547993558923106547677)
              ·
                refine ⟨3664705497584596164955379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9772547993558923106547677 3664705497584596164955379)
                ·
                  refine ⟨5497058246376894247433069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664705497584596164955379 5497058246376894247433069)
                  ·
                    refine ⟨2061396842391335342787401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5497058246376894247433069 2061396842391335342787401)
                    ·
                      refine ⟨1546047631793501507090551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061396842391335342787401 1546047631793501507090551)
                      ·
                        rfl

theorem cell23_3010917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_3010917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010917 prefixEnd_3010917 := by exact prefixLift 3010917
  have htrace : WordTrace (prefixWord ++ tailWord_3010917) baseStart_3010917 baseEnd_3010917 := by
    simpa [prefixWord, tailWord_3010917, baseEnd_3010917] using wordTrace_append hprefix tailTrace_3010917
  have hstable : (prefixWord ++ tailWord_3010917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010917).length < 2 ^ (prefixWord ++ tailWord_3010917).sum := by decide
  have hdescent : baseEnd_3010917 < baseStart_3010917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010924 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_3010924 : Nat := 118140960795 + 3010924 * 2 ^ 59
def prefixEnd_3010924 : Nat := 4983230072969 + 3 ^ 40 * 3010924 * 2
def baseEnd_3010924 : Nat := 1546051226158082979703019

theorem tailTrace_3010924 : CollatzResearch.WordTrace tailWord_3010924 prefixEnd_3010924 1546051226158082979703019 := by
  unfold tailWord_3010924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54908710071972023862387913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73211613429296031816517217 54908710071972023862387913)
  ·
    refine ⟨41181532553979017896790935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54908710071972023862387913 41181532553979017896790935)
    ·
      refine ⟨61772298830968526845186403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41181532553979017896790935 61772298830968526845186403)
      ·
        refine ⟨92658448246452790267779605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61772298830968526845186403 92658448246452790267779605)
        ·
          refine ⟨4343364761552474543802169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92658448246452790267779605 4343364761552474543802169)
          ·
            refine ⟨3257523571164355907851627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4343364761552474543802169 3257523571164355907851627)
            ·
              refine ⟨4886285356746533861777441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257523571164355907851627 4886285356746533861777441)
              ·
                refine ⟨3664714017559900396333081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886285356746533861777441 3664714017559900396333081)
                ·
                  refine ⟨2748535513169925297249811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3664714017559900396333081 2748535513169925297249811)
                  ·
                    refine ⟨4122803269754887945874717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2748535513169925297249811 4122803269754887945874717)
                    ·
                      refine ⟨1546051226158082979703019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4122803269754887945874717 1546051226158082979703019)
                      ·
                        rfl

theorem cell23_3010924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_3010924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010924 prefixEnd_3010924 := by exact prefixLift 3010924
  have htrace : WordTrace (prefixWord ++ tailWord_3010924) baseStart_3010924 baseEnd_3010924 := by
    simpa [prefixWord, tailWord_3010924, baseEnd_3010924] using wordTrace_append hprefix tailTrace_3010924
  have hstable : (prefixWord ++ tailWord_3010924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010924).length < 2 ^ (prefixWord ++ tailWord_3010924).sum := by decide
  have hdescent : baseEnd_3010924 < baseStart_3010924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010953 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 7]
def baseStart_3010953 : Nat := 118140960795 + 3010953 * 2 ^ 59
def prefixEnd_3010953 : Nat := 4983230072969 + 3 ^ 40 * 3010953 * 2
def baseEnd_3010953 : Nat := 171785124121895929582265

theorem tailTrace_3010953 : CollatzResearch.WordTrace tailWord_3010953 prefixEnd_3010953 171785124121895929582265 := by
  unfold tailWord_3010953
  simp only [CollatzResearch.WordTrace]
  refine ⟨109818477860838985677581513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73212318573892657118387675 109818477860838985677581513)
  ·
    refine ⟨82363858395629239258186135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109818477860838985677581513 82363858395629239258186135)
    ·
      refine ⟨123545787593443858887279203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82363858395629239258186135 123545787593443858887279203)
      ·
        refine ⟨185318681390165788330918805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123545787593443858887279203 185318681390165788330918805)
        ·
          refine ⟨8686813190164021328011819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185318681390165788330918805 8686813190164021328011819)
          ·
            refine ⟨13030219785246031992017729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8686813190164021328011819 13030219785246031992017729)
            ·
              refine ⟨9772664838934523994013297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13030219785246031992017729 9772664838934523994013297)
              ·
                refine ⟨7329498629200892995509973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9772664838934523994013297 7329498629200892995509973)
                ·
                  refine ⟨171785124121895929582265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7329498629200892995509973 171785124121895929582265)
                  ·
                    rfl

theorem cell23_3010953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_3010953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010953 prefixEnd_3010953 := by exact prefixLift 3010953
  have htrace : WordTrace (prefixWord ++ tailWord_3010953) baseStart_3010953 baseEnd_3010953 := by
    simpa [prefixWord, tailWord_3010953, baseEnd_3010953] using wordTrace_append hprefix tailTrace_3010953
  have hstable : (prefixWord ++ tailWord_3010953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010953).length < 2 ^ (prefixWord ++ tailWord_3010953).sum := by decide
  have hdescent : baseEnd_3010953 < baseStart_3010953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010993 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3010993 : Nat := 118140960795 + 3010993 * 2 ^ 59
def prefixEnd_3010993 : Nat := 4983230072969 + 3 ^ 40 * 3010993 * 2
def baseEnd_3010993 : Nat := 1546086656323243209740201

theorem tailTrace_3010993 : CollatzResearch.WordTrace tailWord_3010993 prefixEnd_3010993 1546086656323243209740201 := by
  unfold tailWord_3010993
  simp only [CollatzResearch.WordTrace]
  refine ⟨109819936780694072509037633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73213291187129381672691755 109819936780694072509037633)
  ·
    refine ⟨82364952585520554381778225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109819936780694072509037633 82364952585520554381778225)
    ·
      refine ⟨61773714439140415786333669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82364952585520554381778225 61773714439140415786333669)
      ·
        refine ⟨11582571457338827959937563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61773714439140415786333669 11582571457338827959937563)
        ·
          refine ⟨17373857186008241939906345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11582571457338827959937563 17373857186008241939906345)
          ·
            refine ⟨13030392889506181454929759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17373857186008241939906345 13030392889506181454929759)
            ·
              refine ⟨19545589334259272182394639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13030392889506181454929759 19545589334259272182394639)
              ·
                refine ⟨29318384001388908273591959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19545589334259272182394639 29318384001388908273591959)
                ·
                  refine ⟨43977576002083362410387939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29318384001388908273591959 43977576002083362410387939)
                  ·
                    refine ⟨65966364003125043615581909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43977576002083362410387939 65966364003125043615581909)
                    ·
                      refine ⟨1546086656323243209740201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65966364003125043615581909 1546086656323243209740201)
                      ·
                        rfl

theorem cell23_3010993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3010993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010993 prefixEnd_3010993 := by exact prefixLift 3010993
  have htrace : WordTrace (prefixWord ++ tailWord_3010993) baseStart_3010993 baseEnd_3010993 := by
    simpa [prefixWord, tailWord_3010993, baseEnd_3010993] using wordTrace_append hprefix tailTrace_3010993
  have hstable : (prefixWord ++ tailWord_3010993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010993).length < 2 ^ (prefixWord ++ tailWord_3010993).sum := by decide
  have hdescent : baseEnd_3010993 < baseStart_3010993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011033 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_3011033 : Nat := 118140960795 + 3011033 * 2 ^ 59
def prefixEnd_3011033 : Nat := 4983230072969 + 3 ^ 40 * 3011033 * 2
def baseEnd_3011033 : Nat := 1546107195549423053240017

theorem tailTrace_3011033 : CollatzResearch.WordTrace tailWord_3011033 prefixEnd_3011033 1546107195549423053240017 := by
  unfold tailWord_3011033
  simp only [CollatzResearch.WordTrace]
  refine ⟨109821395700549159340493753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73214263800366106226995835 109821395700549159340493753)
  ·
    refine ⟨82366046775411869505370315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109821395700549159340493753 82366046775411869505370315)
    ·
      refine ⟨123549070163117804258055473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82366046775411869505370315 123549070163117804258055473)
      ·
        refine ⟨92661802622338353193541605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123549070163117804258055473 92661802622338353193541605)
        ·
          refine ⟨17374087991688441223789051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92661802622338353193541605 17374087991688441223789051)
          ·
            refine ⟨26061131987532661835683577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17374087991688441223789051 26061131987532661835683577)
            ·
              refine ⟨19545848990649496376762683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26061131987532661835683577 19545848990649496376762683)
              ·
                refine ⟨29318773485974244565144025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19545848990649496376762683 29318773485974244565144025)
                ·
                  refine ⟨21989080114480683423858019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29318773485974244565144025 21989080114480683423858019)
                  ·
                    refine ⟨32983620171721025135787029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21989080114480683423858019 32983620171721025135787029)
                    ·
                      refine ⟨1546107195549423053240017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32983620171721025135787029 1546107195549423053240017)
                      ·
                        rfl

theorem cell23_3011033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_3011033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011033 prefixEnd_3011033 := by exact prefixLift 3011033
  have htrace : WordTrace (prefixWord ++ tailWord_3011033) baseStart_3011033 baseEnd_3011033 := by
    simpa [prefixWord, tailWord_3011033, baseEnd_3011033] using wordTrace_append hprefix tailTrace_3011033
  have hstable : (prefixWord ++ tailWord_3011033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011033).length < 2 ^ (prefixWord ++ tailWord_3011033).sum := by decide
  have hdescent : baseEnd_3011033 < baseStart_3011033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011037 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_3011037 : Nat := 118140960795 + 3011037 * 2 ^ 59
def prefixEnd_3011037 : Nat := 4983230072969 + 3 ^ 40 * 3011037 * 2
def baseEnd_3011037 : Nat := 1546109249472041037589999

theorem tailTrace_3011037 : CollatzResearch.WordTrace tailWord_3011037 prefixEnd_3011037 1546109249472041037589999 := by
  unfold tailWord_3011037
  simp only [CollatzResearch.WordTrace]
  refine ⟨109821541592534668023639365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73214361061689778682426243 109821541592534668023639365)
  ·
    refine ⟨20591539048600250254432381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109821541592534668023639365 20591539048600250254432381)
    ·
      refine ⟨7721827143225093845412143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20591539048600250254432381 7721827143225093845412143)
      ·
        refine ⟨11582740714837640768118215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7721827143225093845412143 11582740714837640768118215)
        ·
          refine ⟨17374111072256461152177323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11582740714837640768118215 17374111072256461152177323)
          ·
            refine ⟨26061166608384691728265985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17374111072256461152177323 26061166608384691728265985)
            ·
              refine ⟨19545874956288518796199489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26061166608384691728265985 19545874956288518796199489)
              ·
                refine ⟨14659406217216389097149617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19545874956288518796199489 14659406217216389097149617)
                ·
                  refine ⟨10994554662912291822862213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14659406217216389097149617 10994554662912291822862213)
                  ·
                    refine ⟨2061478999296054716786665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10994554662912291822862213 2061478999296054716786665)
                    ·
                      refine ⟨1546109249472041037589999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061478999296054716786665 1546109249472041037589999)
                      ·
                        rfl

theorem cell23_3011037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_3011037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011037 prefixEnd_3011037 := by exact prefixLift 3011037
  have htrace : WordTrace (prefixWord ++ tailWord_3011037) baseStart_3011037 baseEnd_3011037 := by
    simpa [prefixWord, tailWord_3011037, baseEnd_3011037] using wordTrace_append hprefix tailTrace_3011037
  have hstable : (prefixWord ++ tailWord_3011037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011037).length < 2 ^ (prefixWord ++ tailWord_3011037).sum := by decide
  have hdescent : baseEnd_3011037 < baseStart_3011037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011040 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_3011040 : Nat := 118140960795 + 3011040 * 2 ^ 59
def prefixEnd_3011040 : Nat := 4983230072969 + 3 ^ 40 * 3011040 * 2
def baseEnd_3011040 : Nat := 1546110789914004525852485

theorem tailTrace_3011040 : CollatzResearch.WordTrace tailWord_3011040 prefixEnd_3011040 1546110789914004525852485 := by
  unfold tailWord_3011040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54910825505761899767999287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73214434007682533023999049 54910825505761899767999287)
  ·
    refine ⟨82366238258642849651998931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54910825505761899767999287 82366238258642849651998931)
    ·
      refine ⟨123549357387964274477998397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82366238258642849651998931 123549357387964274477998397)
      ·
        refine ⟨46331009020486602929249399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123549357387964274477998397 46331009020486602929249399)
        ·
          refine ⟨69496513530729904393874099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46331009020486602929249399 69496513530729904393874099)
          ·
            refine ⟨104244770296094856590811149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69496513530729904393874099 104244770296094856590811149)
            ·
              refine ⟨39091788861035571221554181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104244770296094856590811149 39091788861035571221554181)
              ·
                refine ⟨7329710411444169604041409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39091788861035571221554181 7329710411444169604041409)
                ·
                  refine ⟨5497282808583127203031057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7329710411444169604041409 5497282808583127203031057)
                  ·
                    refine ⟨4122962106437345402273293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5497282808583127203031057 4122962106437345402273293)
                    ·
                      refine ⟨1546110789914004525852485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4122962106437345402273293 1546110789914004525852485)
                      ·
                        rfl

theorem cell23_3011040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_3011040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011040 prefixEnd_3011040 := by exact prefixLift 3011040
  have htrace : WordTrace (prefixWord ++ tailWord_3011040) baseStart_3011040 baseEnd_3011040 := by
    simpa [prefixWord, tailWord_3011040, baseEnd_3011040] using wordTrace_append hprefix tailTrace_3011040
  have hstable : (prefixWord ++ tailWord_3011040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011040).length < 2 ^ (prefixWord ++ tailWord_3011040).sum := by decide
  have hdescent : baseEnd_3011040 < baseStart_3011040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011074 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3011074 : Nat := 118140960795 + 3011074 * 2 ^ 59
def prefixEnd_3011074 : Nat := 4983230072969 + 3 ^ 40 * 3011074 * 2
def baseEnd_3011074 : Nat := 1546128248256257392827329

theorem tailTrace_3011074 : CollatzResearch.WordTrace tailWord_3011074 prefixEnd_3011074 1546128248256257392827329 := by
  unfold tailWord_3011074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27455722773350155835684069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73215260728933748895157517 27455722773350155835684069)
  ·
    refine ⟨5147948020003154219190763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27455722773350155835684069 5147948020003154219190763)
    ·
      refine ⟨7721922030004731328786145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5147948020003154219190763 7721922030004731328786145)
      ·
        refine ⟨5791441522503548496589609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7721922030004731328786145 5791441522503548496589609)
        ·
          refine ⟨4343581141877661372442207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5791441522503548496589609 4343581141877661372442207)
          ·
            refine ⟨6515371712816492058663311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343581141877661372442207 6515371712816492058663311)
            ·
              refine ⟨9773057569224738087994967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515371712816492058663311 9773057569224738087994967)
              ·
                refine ⟨14659586353837107131992451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9773057569224738087994967 14659586353837107131992451)
                ·
                  refine ⟨21989379530755660697988677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14659586353837107131992451 21989379530755660697988677)
                  ·
                    refine ⟨4123008662016686380872877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21989379530755660697988677 4123008662016686380872877)
                    ·
                      refine ⟨1546128248256257392827329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4123008662016686380872877 1546128248256257392827329)
                      ·
                        rfl

theorem cell23_3011074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3011074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011074 prefixEnd_3011074 := by exact prefixLift 3011074
  have htrace : WordTrace (prefixWord ++ tailWord_3011074) baseStart_3011074 baseEnd_3011074 := by
    simpa [prefixWord, tailWord_3011074, baseEnd_3011074] using wordTrace_append hprefix tailTrace_3011074
  have hstable : (prefixWord ++ tailWord_3011074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011074).length < 2 ^ (prefixWord ++ tailWord_3011074).sum := by decide
  have hdescent : baseEnd_3011074 < baseStart_3011074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011111 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 6]
def baseStart_3011111 : Nat := 118140960795 + 3011111 * 2 ^ 59
def prefixEnd_3011111 : Nat := 4983230072969 + 3 ^ 40 * 3011111 * 2
def baseEnd_3011111 : Nat := 171794138560052638673851

theorem tailTrace_3011111 : CollatzResearch.WordTrace tailWord_3011111 prefixEnd_3011111 171794138560052638673851 := by
  unfold tailWord_3011111
  simp only [CollatzResearch.WordTrace]
  refine ⟨109824240594266578661833187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73216160396177719107888791 109824240594266578661833187)
  ·
    refine ⟨164736360891399867992749781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109824240594266578661833187 164736360891399867992749781)
    ·
      refine ⟨3861008458392184406080073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 164736360891399867992749781 3861008458392184406080073)
      ·
        refine ⟨2895756343794138304560055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3861008458392184406080073 2895756343794138304560055)
        ·
          refine ⟨4343634515691207456840083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895756343794138304560055 4343634515691207456840083)
          ·
            refine ⟨6515451773536811185260125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343634515691207456840083 6515451773536811185260125)
            ·
              refine ⟨2443294415076304194472547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6515451773536811185260125 2443294415076304194472547)
              ·
                refine ⟨3664941622614456291708821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443294415076304194472547 3664941622614456291708821)
                ·
                  refine ⟨171794138560052638673851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3664941622614456291708821 171794138560052638673851)
                  ·
                    rfl

theorem cell23_3011111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 6].length) (baseStart_3011111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011111 prefixEnd_3011111 := by exact prefixLift 3011111
  have htrace : WordTrace (prefixWord ++ tailWord_3011111) baseStart_3011111 baseEnd_3011111 := by
    simpa [prefixWord, tailWord_3011111, baseEnd_3011111] using wordTrace_append hprefix tailTrace_3011111
  have hstable : (prefixWord ++ tailWord_3011111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011111).length < 2 ^ (prefixWord ++ tailWord_3011111).sum := by decide
  have hdescent : baseEnd_3011111 < baseStart_3011111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011120 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 1, 6]
def baseStart_3011120 : Nat := 118140960795 + 3011120 * 2 ^ 59
def prefixEnd_3011120 : Nat := 4983230072969 + 3 ^ 40 * 3011120 * 2
def baseEnd_3011120 : Nat := 515383956122121404284039

theorem tailTrace_3011120 : CollatzResearch.WordTrace tailWord_3011120 prefixEnd_3011120 515383956122121404284039 := by
  unfold tailWord_3011120
  simp only [CollatzResearch.WordTrace]
  refine ⟨54912284425616986599455407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73216379234155982132607209 54912284425616986599455407)
  ·
    refine ⟨82368426638425479899183111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54912284425616986599455407 82368426638425479899183111)
    ·
      refine ⟨123552639957638219848774667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82368426638425479899183111 123552639957638219848774667)
      ·
        refine ⟨185328959936457329773162001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123552639957638219848774667 185328959936457329773162001)
        ·
          refine ⟨138996719952342997329871501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185328959936457329773162001 138996719952342997329871501)
          ·
            refine ⟨52123769982128623998701813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138996719952342997329871501 52123769982128623998701813)
            ·
              refine ⟨4886603435824558499878295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52123769982128623998701813 4886603435824558499878295)
              ·
                refine ⟨7329905153736837749817443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4886603435824558499878295 7329905153736837749817443)
                ·
                  refine ⟨10994857730605256624726165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7329905153736837749817443 10994857730605256624726165)
                  ·
                    refine ⟨515383956122121404284039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10994857730605256624726165 515383956122121404284039)
                    ·
                      rfl

theorem cell23_3011120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_3011120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011120 prefixEnd_3011120 := by exact prefixLift 3011120
  have htrace : WordTrace (prefixWord ++ tailWord_3011120) baseStart_3011120 baseEnd_3011120 := by
    simpa [prefixWord, tailWord_3011120, baseEnd_3011120] using wordTrace_append hprefix tailTrace_3011120
  have hstable : (prefixWord ++ tailWord_3011120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011120).length < 2 ^ (prefixWord ++ tailWord_3011120).sum := by decide
  have hdescent : baseEnd_3011120 < baseStart_3011120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011127 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_3011127 : Nat := 118140960795 + 3011127 * 2 ^ 59
def prefixEnd_3011127 : Nat := 4983230072969 + 3 ^ 40 * 3011127 * 2
def baseEnd_3011127 : Nat := 1546155462730945685464585

theorem tailTrace_3011127 : CollatzResearch.WordTrace tailWord_3011127 prefixEnd_3011127 1546155462730945685464585 := by
  unfold tailWord_3011127
  simp only [CollatzResearch.WordTrace]
  refine ⟨109824824162208613394415635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73216549441472408929610423 109824824162208613394415635)
  ·
    refine ⟨164737236243312920091623453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109824824162208613394415635 164737236243312920091623453)
    ·
      refine ⟨61776463591242345034358795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164737236243312920091623453 61776463591242345034358795)
      ·
        refine ⟨92664695386863517551538193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61776463591242345034358795 92664695386863517551538193)
        ·
          refine ⟨69498521540147638163653645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92664695386863517551538193 69498521540147638163653645)
          ·
            refine ⟨26061945577555364311370117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69498521540147638163653645 26061945577555364311370117)
            ·
              refine ⟨4886614795791630808381897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26061945577555364311370117 4886614795791630808381897)
              ·
                refine ⟨3664961096843723106286423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886614795791630808381897 3664961096843723106286423)
                ·
                  refine ⟨5497441645265584659429635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664961096843723106286423 5497441645265584659429635)
                  ·
                    refine ⟨8246162467898376989144453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497441645265584659429635 8246162467898376989144453)
                    ·
                      refine ⟨1546155462730945685464585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8246162467898376989144453 1546155462730945685464585)
                      ·
                        rfl

theorem cell23_3011127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_3011127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011127 prefixEnd_3011127 := by exact prefixLift 3011127
  have htrace : WordTrace (prefixWord ++ tailWord_3011127) baseStart_3011127 baseEnd_3011127 := by
    simpa [prefixWord, tailWord_3011127, baseEnd_3011127] using wordTrace_append hprefix tailTrace_3011127
  have hstable : (prefixWord ++ tailWord_3011127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011127).length < 2 ^ (prefixWord ++ tailWord_3011127).sum := by decide
  have hdescent : baseEnd_3011127 < baseStart_3011127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011137 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3011137 : Nat := 118140960795 + 3011137 * 2 ^ 59
def prefixEnd_3011137 : Nat := 4983230072969 + 3 ^ 40 * 3011137 * 2
def baseEnd_3011137 : Nat := 515386865845830215446513

theorem tailTrace_3011137 : CollatzResearch.WordTrace tailWord_3011137 prefixEnd_3011137 515386865845830215446513 := by
  unfold tailWord_3011137
  simp only [CollatzResearch.WordTrace]
  refine ⟨109825188892172385102279665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73216792594781590068186443 109825188892172385102279665)
  ·
    refine ⟨82368891669129288826709749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109825188892172385102279665 82368891669129288826709749)
    ·
      refine ⟨7722083593980870827504039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82368891669129288826709749 7722083593980870827504039)
      ·
        refine ⟨11583125390971306241256059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7722083593980870827504039 11583125390971306241256059)
        ·
          refine ⟨17374688086456959361884089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11583125390971306241256059 17374688086456959361884089)
          ·
            refine ⟨13031016064842719521413067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17374688086456959361884089 13031016064842719521413067)
            ·
              refine ⟨19546524097264079282119601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13031016064842719521413067 19546524097264079282119601)
              ·
                refine ⟨14659893072948059461589701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19546524097264079282119601 14659893072948059461589701)
                ·
                  refine ⟨2748729951177761149048069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14659893072948059461589701 2748729951177761149048069)
                  ·
                    refine ⟨515386865845830215446513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748729951177761149048069 515386865845830215446513)
                    ·
                      rfl

theorem cell23_3011137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3011137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011137 prefixEnd_3011137 := by exact prefixLift 3011137
  have htrace : WordTrace (prefixWord ++ tailWord_3011137) baseStart_3011137 baseEnd_3011137 := by
    simpa [prefixWord, tailWord_3011137, baseEnd_3011137] using wordTrace_append hprefix tailTrace_3011137
  have hstable : (prefixWord ++ tailWord_3011137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011137).length < 2 ^ (prefixWord ++ tailWord_3011137).sum := by decide
  have hdescent : baseEnd_3011137 < baseStart_3011137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011147 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 3]
def baseStart_3011147 : Nat := 118140960795 + 3011147 * 2 ^ 59
def prefixEnd_3011147 : Nat := 4983230072969 + 3 ^ 40 * 3011147 * 2
def baseEnd_3011147 : Nat := 1546165732344035607214493

theorem tailTrace_3011147 : CollatzResearch.WordTrace tailWord_3011147 prefixEnd_3011147 1546165732344035607214493 := by
  unfold tailWord_3011147
  simp only [CollatzResearch.WordTrace]
  refine ⟨109825553622136156810143695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73217035748090771206762463 109825553622136156810143695)
  ·
    refine ⟨164738330433204235215215543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109825553622136156810143695 164738330433204235215215543)
    ·
      refine ⟨247107495649806352822823315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164738330433204235215215543 247107495649806352822823315)
      ·
        refine ⟨370661243474709529234234973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247107495649806352822823315 370661243474709529234234973)
        ·
          refine ⟨138997966303016073462838115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370661243474709529234234973 138997966303016073462838115)
          ·
            refine ⟨208496949454524110194257173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138997966303016073462838115 208496949454524110194257173)
            ·
              refine ⟨9773294505680817665355805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208496949454524110194257173 9773294505680817665355805)
              ·
                refine ⟨3664985439630306624508427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9773294505680817665355805 3664985439630306624508427)
                ·
                  refine ⟨5497478159445459936762641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664985439630306624508427 5497478159445459936762641)
                  ·
                    refine ⟨4123108619584094952571981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5497478159445459936762641 4123108619584094952571981)
                    ·
                      refine ⟨1546165732344035607214493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4123108619584094952571981 1546165732344035607214493)
                      ·
                        rfl

theorem cell23_3011147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 3].length) (baseStart_3011147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011147 prefixEnd_3011147 := by exact prefixLift 3011147
  have htrace : WordTrace (prefixWord ++ tailWord_3011147) baseStart_3011147 baseEnd_3011147 := by
    simpa [prefixWord, tailWord_3011147, baseEnd_3011147] using wordTrace_append hprefix tailTrace_3011147
  have hstable : (prefixWord ++ tailWord_3011147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011147).length < 2 ^ (prefixWord ++ tailWord_3011147).sum := by decide
  have hdescent : baseEnd_3011147 < baseStart_3011147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011181 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3011181 : Nat := 118140960795 + 3011181 * 2 ^ 59
def prefixEnd_3011181 : Nat := 4983230072969 + 3 ^ 40 * 3011181 * 2
def baseEnd_3011181 : Nat := 1546183190686288474189337

theorem tailTrace_3011181 : CollatzResearch.WordTrace tailWord_3011181 prefixEnd_3011181 1546183190686288474189337 := by
  unfold tailWord_3011181
  simp only [CollatzResearch.WordTrace]
  refine ⟨109826793704012980616881397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73217862469341987077920931 109826793704012980616881397)
  ·
    refine ⟨10296261909751216932832631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109826793704012980616881397 10296261909751216932832631)
    ·
      refine ⟨15444392864626825399248947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10296261909751216932832631 15444392864626825399248947)
      ·
        refine ⟨23166589296940238098873421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15444392864626825399248947 23166589296940238098873421)
        ·
          refine ⟨8687470986352589287077533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23166589296940238098873421 8687470986352589287077533)
          ·
            refine ⟨3257801619882220982654075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8687470986352589287077533 3257801619882220982654075)
            ·
              refine ⟨4886702429823331473981113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257801619882220982654075 4886702429823331473981113)
              ·
                refine ⟨3665026822367498605485835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886702429823331473981113 3665026822367498605485835)
                ·
                  refine ⟨5497540233551247908228753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665026822367498605485835 5497540233551247908228753)
                  ·
                    refine ⟨4123155175163435931171565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5497540233551247908228753 4123155175163435931171565)
                    ·
                      refine ⟨1546183190686288474189337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4123155175163435931171565 1546183190686288474189337)
                      ·
                        rfl

theorem cell23_3011181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3011181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011181 prefixEnd_3011181 := by exact prefixLift 3011181
  have htrace : WordTrace (prefixWord ++ tailWord_3011181) baseStart_3011181 baseEnd_3011181 := by
    simpa [prefixWord, tailWord_3011181, baseEnd_3011181] using wordTrace_append hprefix tailTrace_3011181
  have hstable : (prefixWord ++ tailWord_3011181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011181).length < 2 ^ (prefixWord ++ tailWord_3011181).sum := by decide
  have hdescent : baseEnd_3011181 < baseStart_3011181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011250 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3011250 : Nat := 118140960795 + 3011250 * 2 ^ 59
def prefixEnd_3011250 : Nat := 4983230072969 + 3 ^ 40 * 3011250 * 2
def baseEnd_3011250 : Nat := 1546218620851448704226519

theorem tailTrace_3011250 : CollatzResearch.WordTrace tailWord_3011250 prefixEnd_3011250 1546218620851448704226519 := by
  unfold tailWord_3011250
  simp only [CollatzResearch.WordTrace]
  refine ⟨27457327585190751350285801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73219540227175336934095469 27457327585190751350285801)
  ·
    refine ⟨20592995688893063512714351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27457327585190751350285801 20592995688893063512714351)
    ·
      refine ⟨30889493533339595269071527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20592995688893063512714351 30889493533339595269071527)
      ·
        refine ⟨46334240300009392903607291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30889493533339595269071527 46334240300009392903607291)
        ·
          refine ⟨69501360450014089355410937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46334240300009392903607291 69501360450014089355410937)
          ·
            refine ⟨52126020337510567016558203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69501360450014089355410937 52126020337510567016558203)
            ·
              refine ⟨78189030506265850524837305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52126020337510567016558203 78189030506265850524837305)
              ·
                refine ⟨58641772879699387893627979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78189030506265850524837305 58641772879699387893627979)
                ·
                  refine ⟨87962659319549081840441969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58641772879699387893627979 87962659319549081840441969)
                  ·
                    refine ⟨65971994489661811380331477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87962659319549081840441969 65971994489661811380331477)
                    ·
                      refine ⟨1546218620851448704226519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65971994489661811380331477 1546218620851448704226519)
                      ·
                        rfl

theorem cell23_3011250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3011250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011250 prefixEnd_3011250 := by exact prefixLift 3011250
  have htrace : WordTrace (prefixWord ++ tailWord_3011250) baseStart_3011250 baseEnd_3011250 := by
    simpa [prefixWord, tailWord_3011250, baseEnd_3011250] using wordTrace_append hprefix tailTrace_3011250
  have hstable : (prefixWord ++ tailWord_3011250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011250).length < 2 ^ (prefixWord ++ tailWord_3011250).sum := by decide
  have hdescent : baseEnd_3011250 < baseStart_3011250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011255 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 1, 3, 2]
def baseStart_3011255 : Nat := 118140960795 + 3011255 * 2 ^ 59
def prefixEnd_3011255 : Nat := 4983230072969 + 3 ^ 40 * 3011255 * 2
def baseEnd_3011255 : Nat := 1546221188254721184663997

theorem tailTrace_3011255 : CollatzResearch.WordTrace tailWord_3011255 prefixEnd_3011255 1546221188254721184663997 := by
  unfold tailWord_3011255
  simp only [CollatzResearch.WordTrace]
  refine ⟨109829492705744891255075219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73219661803829927503383479 109829492705744891255075219)
  ·
    refine ⟨164744239058617336882612829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109829492705744891255075219 164744239058617336882612829)
    ·
      refine ⟨61779089646981501330979811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164744239058617336882612829 61779089646981501330979811)
      ·
        refine ⟨92668634470472251996469717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61779089646981501330979811 92668634470472251996469717)
        ·
          refine ⟨2171921120401693406167259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92668634470472251996469717 2171921120401693406167259)
          ·
            refine ⟨3257881680602540109250889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171921120401693406167259 3257881680602540109250889)
            ·
              refine ⟨2443411260451905081938167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257881680602540109250889 2443411260451905081938167)
              ·
                refine ⟨3665116890677857622907251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443411260451905081938167 3665116890677857622907251)
                ·
                  refine ⟨5497675336016786434360877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665116890677857622907251 5497675336016786434360877)
                  ·
                    refine ⟨2061628251006294912885329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5497675336016786434360877 2061628251006294912885329)
                    ·
                      refine ⟨1546221188254721184663997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061628251006294912885329 1546221188254721184663997)
                      ·
                        rfl

theorem cell23_3011255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_3011255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011255 prefixEnd_3011255 := by exact prefixLift 3011255
  have htrace : WordTrace (prefixWord ++ tailWord_3011255) baseStart_3011255 baseEnd_3011255 := by
    simpa [prefixWord, tailWord_3011255, baseEnd_3011255] using wordTrace_append hprefix tailTrace_3011255
  have hstable : (prefixWord ++ tailWord_3011255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011255).length < 2 ^ (prefixWord ++ tailWord_3011255).sum := by decide
  have hdescent : baseEnd_3011255 < baseStart_3011255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011268 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3011268 : Nat := 118140960795 + 3011268 * 2 ^ 59
def prefixEnd_3011268 : Nat := 4983230072969 + 3 ^ 40 * 3011268 * 2
def baseEnd_3011268 : Nat := 1546227863503229633801437

theorem tailTrace_3011268 : CollatzResearch.WordTrace tailWord_3011268 prefixEnd_3011268 1546227863503229633801437 := by
  unfold tailWord_3011268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54914983427348897237649229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73219977903131862983532305 54914983427348897237649229)
  ·
    refine ⟨20593118785255836464118461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54914983427348897237649229 20593118785255836464118461)
    ·
      refine ⟨7722419544470938674044423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20593118785255836464118461 7722419544470938674044423)
      ·
        refine ⟨11583629316706408011066635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7722419544470938674044423 11583629316706408011066635)
        ·
          refine ⟨17375443975059612016599953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11583629316706408011066635 17375443975059612016599953)
          ·
            refine ⟨13031582981294709012449965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17375443975059612016599953 13031582981294709012449965)
            ·
              refine ⟨4886843617985515879668737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13031582981294709012449965 4886843617985515879668737)
              ·
                refine ⟨3665132713489136909751553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886843617985515879668737 3665132713489136909751553)
                ·
                  refine ⟨2748849535116852682313665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3665132713489136909751553 2748849535116852682313665)
                  ·
                    refine ⟨2061637151337639511735249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2748849535116852682313665 2061637151337639511735249)
                    ·
                      refine ⟨1546227863503229633801437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061637151337639511735249 1546227863503229633801437)
                      ·
                        rfl

theorem cell23_3011268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3011268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011268 prefixEnd_3011268 := by exact prefixLift 3011268
  have htrace : WordTrace (prefixWord ++ tailWord_3011268) baseStart_3011268 baseEnd_3011268 := by
    simpa [prefixWord, tailWord_3011268, baseEnd_3011268] using wordTrace_append hprefix tailTrace_3011268
  have hstable : (prefixWord ++ tailWord_3011268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011268).length < 2 ^ (prefixWord ++ tailWord_3011268).sum := by decide
  have hdescent : baseEnd_3011268 < baseStart_3011268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011274 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_3011274 : Nat := 118140960795 + 3011274 * 2 ^ 59
def prefixEnd_3011274 : Nat := 4983230072969 + 3 ^ 40 * 3011274 * 2
def baseEnd_3011274 : Nat := 171803438265239623369601

theorem tailTrace_3011274 : CollatzResearch.WordTrace tailWord_3011274 prefixEnd_3011274 171803438265239623369601 := by
  unfold tailWord_3011274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27457546423169014375004219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73220123795117371666677917 27457546423169014375004219)
  ·
    refine ⟨41186319634753521562506329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27457546423169014375004219 41186319634753521562506329)
    ·
      refine ⟨30889739726065141171879747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41186319634753521562506329 30889739726065141171879747)
      ·
        refine ⟨46334609589097711757819621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30889739726065141171879747 46334609589097711757819621)
        ·
          refine ⟨8687739297955820954591179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46334609589097711757819621 8687739297955820954591179)
          ·
            refine ⟨13031608946933731431886769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687739297955820954591179 13031608946933731431886769)
            ·
              refine ⟨9773706710200298573915077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13031608946933731431886769 9773706710200298573915077)
              ·
                refine ⟨1832570008162555982609077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9773706710200298573915077 1832570008162555982609077)
                ·
                  refine ⟨171803438265239623369601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1832570008162555982609077 171803438265239623369601)
                  ·
                    rfl

theorem cell23_3011274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_3011274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011274 prefixEnd_3011274 := by exact prefixLift 3011274
  have htrace : WordTrace (prefixWord ++ tailWord_3011274) baseStart_3011274 baseEnd_3011274 := by
    simpa [prefixWord, tailWord_3011274, baseEnd_3011274] using wordTrace_append hprefix tailTrace_3011274
  have hstable : (prefixWord ++ tailWord_3011274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011274).length < 2 ^ (prefixWord ++ tailWord_3011274).sum := by decide
  have hdescent : baseEnd_3011274 < baseStart_3011274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011280 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_3011280 : Nat := 118140960795 + 3011280 * 2 ^ 59
def prefixEnd_3011280 : Nat := 4983230072969 + 3 ^ 40 * 3011280 * 2
def baseEnd_3011280 : Nat := 1546234025271083586851381

theorem tailTrace_3011280 : CollatzResearch.WordTrace tailWord_3011280 prefixEnd_3011280 1546234025271083586851381 := by
  unfold tailWord_3011280
  simp only [CollatzResearch.WordTrace]
  refine ⟨54915202265327160262367647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73220269687102880349823529 54915202265327160262367647)
  ·
    refine ⟨82372803397990740393551471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54915202265327160262367647 82372803397990740393551471)
    ·
      refine ⟨123559205096986110590327207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82372803397990740393551471 123559205096986110590327207)
      ·
        refine ⟨185338807645479165885490811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123559205096986110590327207 185338807645479165885490811)
        ·
          refine ⟨278008211468218748828236217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185338807645479165885490811 278008211468218748828236217)
          ·
            refine ⟨208506158601164061621177163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278008211468218748828236217 208506158601164061621177163)
            ·
              refine ⟨312759237901746092431765745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208506158601164061621177163 312759237901746092431765745)
              ·
                refine ⟨234569428426309569323824309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312759237901746092431765745 234569428426309569323824309)
                ·
                  refine ⟨21990883914966522124108529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 234569428426309569323824309 21990883914966522124108529)
                  ·
                    refine ⟨16493162936224891593081397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21990883914966522124108529 16493162936224891593081397)
                    ·
                      refine ⟨1546234025271083586851381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16493162936224891593081397 1546234025271083586851381)
                      ·
                        rfl

theorem cell23_3011280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_3011280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011280 prefixEnd_3011280 := by exact prefixLift 3011280
  have htrace : WordTrace (prefixWord ++ tailWord_3011280) baseStart_3011280 baseEnd_3011280 := by
    simpa [prefixWord, tailWord_3011280, baseEnd_3011280] using wordTrace_append hprefix tailTrace_3011280
  have hstable : (prefixWord ++ tailWord_3011280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011280).length < 2 ^ (prefixWord ++ tailWord_3011280).sum := by decide
  have hdescent : baseEnd_3011280 < baseStart_3011280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011285 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3011285 : Nat := 118140960795 + 3011285 * 2 ^ 59
def prefixEnd_3011285 : Nat := 4983230072969 + 3 ^ 40 * 3011285 * 2
def baseEnd_3011285 : Nat := 1546236592674356067288859

theorem tailTrace_3011285 : CollatzResearch.WordTrace tailWord_3011285 prefixEnd_3011285 1546236592674356067288859 := by
  unfold tailWord_3011285
  simp only [CollatzResearch.WordTrace]
  refine ⟨109830586895636206378667309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73220391263757470919111539 109830586895636206378667309)
  ·
    refine ⟨41186470085863577392000241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109830586895636206378667309 41186470085863577392000241)
    ·
      refine ⟨30889852564397683044000181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41186470085863577392000241 30889852564397683044000181)
      ·
        refine ⟨2895923677912282785375017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30889852564397683044000181 2895923677912282785375017)
        ·
          refine ⟨2171942758434212089031263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895923677912282785375017 2171942758434212089031263)
          ·
            refine ⟨3257914137651318133546895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171942758434212089031263 3257914137651318133546895)
            ·
              refine ⟨4886871206476977200320343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257914137651318133546895 4886871206476977200320343)
              ·
                refine ⟨7330306809715465800480515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4886871206476977200320343 7330306809715465800480515)
                ·
                  refine ⟨10995460214573198700720773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7330306809715465800480515 10995460214573198700720773)
                  ·
                    refine ⟨2061648790232474756385145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10995460214573198700720773 2061648790232474756385145)
                    ·
                      refine ⟨1546236592674356067288859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061648790232474756385145 1546236592674356067288859)
                      ·
                        rfl

theorem cell23_3011285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3011285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011285 prefixEnd_3011285 := by exact prefixLift 3011285
  have htrace : WordTrace (prefixWord ++ tailWord_3011285) baseStart_3011285 baseEnd_3011285 := by
    simpa [prefixWord, tailWord_3011285, baseEnd_3011285] using wordTrace_append hprefix tailTrace_3011285
  have hstable : (prefixWord ++ tailWord_3011285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011285).length < 2 ^ (prefixWord ++ tailWord_3011285).sum := by decide
  have hdescent : baseEnd_3011285 < baseStart_3011285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011307 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 4]
def baseStart_3011307 : Nat := 118140960795 + 3011307 * 2 ^ 59
def prefixEnd_3011307 : Nat := 4983230072969 + 3 ^ 40 * 3011307 * 2
def baseEnd_3011307 : Nat := 1546247889248754981213757

theorem tailTrace_3011307 : CollatzResearch.WordTrace tailWord_3011307 prefixEnd_3011307 1546247889248754981213757 := by
  unfold tailWord_3011307
  simp only [CollatzResearch.WordTrace]
  refine ⟨109831389301556504135968175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73220926201037669423978783 109831389301556504135968175)
  ·
    refine ⟨164747083952334756203952263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109831389301556504135968175 164747083952334756203952263)
    ·
      refine ⟨247120625928502134305928395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164747083952334756203952263 247120625928502134305928395)
      ·
        refine ⟨370680938892753201458892593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247120625928502134305928395 370680938892753201458892593)
        ·
          refine ⟨278010704169564901094169445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370680938892753201458892593 278010704169564901094169445)
          ·
            refine ⟨52127007031793418955156771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278010704169564901094169445 52127007031793418955156771)
            ·
              refine ⟨78190510547690128432735157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52127007031793418955156771 78190510547690128432735157)
              ·
                refine ⟨7330360363845949540568921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78190510547690128432735157 7330360363845949540568921)
                ·
                  refine ⟨5497770272884462155426691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7330360363845949540568921 5497770272884462155426691)
                  ·
                    refine ⟨8246655409326693233140037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497770272884462155426691 8246655409326693233140037)
                    ·
                      refine ⟨1546247889248754981213757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8246655409326693233140037 1546247889248754981213757)
                      ·
                        rfl

theorem cell23_3011307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 4].length) (baseStart_3011307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011307 prefixEnd_3011307 := by exact prefixLift 3011307
  have htrace : WordTrace (prefixWord ++ tailWord_3011307) baseStart_3011307 baseEnd_3011307 := by
    simpa [prefixWord, tailWord_3011307, baseEnd_3011307] using wordTrace_append hprefix tailTrace_3011307
  have hstable : (prefixWord ++ tailWord_3011307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011307).length < 2 ^ (prefixWord ++ tailWord_3011307).sum := by decide
  have hdescent : baseEnd_3011307 < baseStart_3011307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011324 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_3011324 : Nat := 118140960795 + 3011324 * 2 ^ 59
def prefixEnd_3011324 : Nat := 4983230072969 + 3 ^ 40 * 3011324 * 2
def baseEnd_3011324 : Nat := 1546256618419881414701179

theorem tailTrace_3011324 : CollatzResearch.WordTrace tailWord_3011324 prefixEnd_3011324 1546256618419881414701179 := by
  unfold tailWord_3011324
  simp only [CollatzResearch.WordTrace]
  refine ⟨54916004671247458019668513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73221339561663277359558017 54916004671247458019668513)
  ·
    refine ⟨41187003503435593514751385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54916004671247458019668513 41187003503435593514751385)
    ·
      refine ⟨30890252627576695136063539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41187003503435593514751385 30890252627576695136063539)
      ·
        refine ⟨46335378941365042704095309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30890252627576695136063539 46335378941365042704095309)
        ·
          refine ⟨17375767103011891014035741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46335378941365042704095309 17375767103011891014035741)
          ·
            refine ⟨6515912663629459130263403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17375767103011891014035741 6515912663629459130263403)
            ·
              refine ⟨9773868995444188695395105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515912663629459130263403 9773868995444188695395105)
              ·
                refine ⟨7330401746583141521546329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9773868995444188695395105 7330401746583141521546329)
                ·
                  refine ⟨5497801309937356141159747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7330401746583141521546329 5497801309937356141159747)
                  ·
                    refine ⟨8246701964906034211739621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497801309937356141159747 8246701964906034211739621)
                    ·
                      refine ⟨1546256618419881414701179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8246701964906034211739621 1546256618419881414701179)
                      ·
                        rfl

theorem cell23_3011324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_3011324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011324 prefixEnd_3011324 := by exact prefixLift 3011324
  have htrace : WordTrace (prefixWord ++ tailWord_3011324) baseStart_3011324 baseEnd_3011324 := by
    simpa [prefixWord, tailWord_3011324, baseEnd_3011324] using wordTrace_append hprefix tailTrace_3011324
  have hstable : (prefixWord ++ tailWord_3011324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011324).length < 2 ^ (prefixWord ++ tailWord_3011324).sum := by decide
  have hdescent : baseEnd_3011324 < baseStart_3011324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011347 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 6]
def baseStart_3011347 : Nat := 118140960795 + 3011347 * 2 ^ 59
def prefixEnd_3011347 : Nat := 4983230072969 + 3 ^ 40 * 3011347 * 2
def baseEnd_3011347 : Nat := 171807603163881647190397

theorem tailTrace_3011347 : CollatzResearch.WordTrace tailWord_3011347 prefixEnd_3011347 171807603163881647190397 := by
  unfold tailWord_3011347
  simp only [CollatzResearch.WordTrace]
  refine ⟨109832848221411590967424295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73221898814274393978282863 109832848221411590967424295)
  ·
    refine ⟨164749272332117386451136443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109832848221411590967424295 164749272332117386451136443)
    ·
      refine ⟨247123908498176079676704665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164749272332117386451136443 247123908498176079676704665)
      ·
        refine ⟨185342931373632059757528499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247123908498176079676704665 185342931373632059757528499)
        ·
          refine ⟨278014397060448089636292749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185342931373632059757528499 278014397060448089636292749)
          ·
            refine ⟨104255398897668033613609781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278014397060448089636292749 104255398897668033613609781)
            ·
              refine ⟨9773943646656378151275917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104255398897668033613609781 9773943646656378151275917)
              ·
                refine ⟨3665228867496141806728469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9773943646656378151275917 3665228867496141806728469)
                ·
                  refine ⟨171807603163881647190397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3665228867496141806728469 171807603163881647190397)
                  ·
                    rfl

theorem cell23_3011347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 6].length) (baseStart_3011347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011347 prefixEnd_3011347 := by exact prefixLift 3011347
  have htrace : WordTrace (prefixWord ++ tailWord_3011347) baseStart_3011347 baseEnd_3011347 := by
    simpa [prefixWord, tailWord_3011347, baseEnd_3011347] using wordTrace_append hprefix tailTrace_3011347
  have hstable : (prefixWord ++ tailWord_3011347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011347).length < 2 ^ (prefixWord ++ tailWord_3011347).sum := by decide
  have hdescent : baseEnd_3011347 < baseStart_3011347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011418 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2]
def baseStart_3011418 : Nat := 118140960795 + 3011418 * 2 ^ 59
def prefixEnd_3011418 : Nat := 4983230072969 + 3 ^ 40 * 3011418 * 2
def baseEnd_3011418 : Nat := 1546304885601404046925747

theorem tailTrace_3011418 : CollatzResearch.WordTrace tailWord_3011418 prefixEnd_3011418 1546304885601404046925747 := by
  unfold tailWord_3011418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27458859451038592523314727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73223625202769580062172605 27458859451038592523314727)
  ·
    refine ⟨41188289176557888784972091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27458859451038592523314727 41188289176557888784972091)
    ·
      refine ⟨61782433764836833177458137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41188289176557888784972091 61782433764836833177458137)
      ·
        refine ⟨46336825323627624883093603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61782433764836833177458137 46336825323627624883093603)
        ·
          refine ⟨69505237985441437324640405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46336825323627624883093603 69505237985441437324640405)
          ·
            refine ⟨3258058030567567374592519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69505237985441437324640405 3258058030567567374592519)
            ·
              refine ⟨4887087045851351061888779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258058030567567374592519 4887087045851351061888779)
              ·
                refine ⟨7330630568777026592833169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4887087045851351061888779 7330630568777026592833169)
                ·
                  refine ⟨5497972926582769944624877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7330630568777026592833169 5497972926582769944624877)
                  ·
                    refine ⟨2061739847468538729234329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5497972926582769944624877 2061739847468538729234329)
                    ·
                      refine ⟨1546304885601404046925747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061739847468538729234329 1546304885601404046925747)
                      ·
                        rfl

theorem cell23_3011418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_3011418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011418 prefixEnd_3011418 := by exact prefixLift 3011418
  have htrace : WordTrace (prefixWord ++ tailWord_3011418) baseStart_3011418 baseEnd_3011418 := by
    simpa [prefixWord, tailWord_3011418, baseEnd_3011418] using wordTrace_append hprefix tailTrace_3011418
  have hstable : (prefixWord ++ tailWord_3011418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011418).length < 2 ^ (prefixWord ++ tailWord_3011418).sum := by decide
  have hdescent : baseEnd_3011418 < baseStart_3011418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011424 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 4, 4]
def baseStart_3011424 : Nat := 118140960795 + 3011424 * 2 ^ 59
def prefixEnd_3011424 : Nat := 4983230072969 + 3 ^ 40 * 3011424 * 2
def baseEnd_3011424 : Nat := 515435988828443674483573

theorem tailTrace_3011424 : CollatzResearch.WordTrace tailWord_3011424 prefixEnd_3011424 515435988828443674483573 := by
  unfold tailWord_3011424
  simp only [CollatzResearch.WordTrace]
  refine ⟨54917828321066316558988663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73223771094755088745318217 54917828321066316558988663)
  ·
    refine ⟨82376742481599474838482995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54917828321066316558988663 82376742481599474838482995)
    ·
      refine ⟨123565113722399212257724493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82376742481599474838482995 123565113722399212257724493)
      ·
        refine ⟨46336917645899704596646685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123565113722399212257724493 46336917645899704596646685)
        ·
          refine ⟨17376344117212389223742507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46336917645899704596646685 17376344117212389223742507)
          ·
            refine ⟨26064516175818583835613761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17376344117212389223742507 26064516175818583835613761)
            ·
              refine ⟨19548387131863937876710321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26064516175818583835613761 19548387131863937876710321)
              ·
                refine ⟨14661290348897953407532741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19548387131863937876710321 14661290348897953407532741)
                ·
                  refine ⟨2748991940418366263912389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14661290348897953407532741 2748991940418366263912389)
                  ·
                    refine ⟨515435988828443674483573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748991940418366263912389 515435988828443674483573)
                    ·
                      rfl

theorem cell23_3011424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_3011424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011424 prefixEnd_3011424 := by exact prefixLift 3011424
  have htrace : WordTrace (prefixWord ++ tailWord_3011424) baseStart_3011424 baseEnd_3011424 := by
    simpa [prefixWord, tailWord_3011424, baseEnd_3011424] using wordTrace_append hprefix tailTrace_3011424
  have hstable : (prefixWord ++ tailWord_3011424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011424).length < 2 ^ (prefixWord ++ tailWord_3011424).sum := by decide
  have hdescent : baseEnd_3011424 < baseStart_3011424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011428 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_3011428 : Nat := 118140960795 + 3011428 * 2 ^ 59
def prefixEnd_3011428 : Nat := 4983230072969 + 3 ^ 40 * 3011428 * 2
def baseEnd_3011428 : Nat := 515436673469316335933567

theorem tailTrace_3011428 : CollatzResearch.WordTrace tailWord_3011428 prefixEnd_3011428 515436673469316335933567 := by
  unfold tailWord_3011428
  simp only [CollatzResearch.WordTrace]
  refine ⟨54917901267059070900561469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73223868356078761200748625 54917901267059070900561469)
  ·
    refine ⟨20594212975147151587710551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54917901267059070900561469 20594212975147151587710551)
    ·
      refine ⟨30891319462720727381565827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20594212975147151587710551 30891319462720727381565827)
      ·
        refine ⟨46336979194081091072348741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30891319462720727381565827 46336979194081091072348741)
        ·
          refine ⟨8688183598890204576065389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46336979194081091072348741 8688183598890204576065389)
          ·
            refine ⟨3258068849583826716024521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8688183598890204576065389 3258068849583826716024521)
            ·
              refine ⟨2443551637187870037018391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3258068849583826716024521 2443551637187870037018391)
              ·
                refine ⟨3665327455781805055527587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443551637187870037018391 3665327455781805055527587)
                ·
                  refine ⟨5497991183672707583291381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665327455781805055527587 5497991183672707583291381)
                  ·
                    refine ⟨515436673469316335933567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5497991183672707583291381 515436673469316335933567)
                    ·
                      rfl

theorem cell23_3011428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_3011428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011428 prefixEnd_3011428 := by exact prefixLift 3011428
  have htrace : WordTrace (prefixWord ++ tailWord_3011428) baseStart_3011428 baseEnd_3011428 := by
    simpa [prefixWord, tailWord_3011428, baseEnd_3011428] using wordTrace_append hprefix tailTrace_3011428
  have hstable : (prefixWord ++ tailWord_3011428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011428).length < 2 ^ (prefixWord ++ tailWord_3011428).sum := by decide
  have hdescent : baseEnd_3011428 < baseStart_3011428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011431 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3011431 : Nat := 118140960795 + 3011431 * 2 ^ 59
def prefixEnd_3011431 : Nat := 4983230072969 + 3 ^ 40 * 3011431 * 2
def baseEnd_3011431 : Nat := 1546311560849912496063187

theorem tailTrace_3011431 : CollatzResearch.WordTrace tailWord_3011431 prefixEnd_3011431 1546311560849912496063187 := by
  unfold tailWord_3011431
  simp only [CollatzResearch.WordTrace]
  refine ⟨109835911953107273313482147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73223941302071515542321431 109835911953107273313482147)
  ·
    refine ⟨164753867929660909970223221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109835911953107273313482147 164753867929660909970223221)
    ·
      refine ⟨15445675118405710309708427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164753867929660909970223221 15445675118405710309708427)
      ·
        refine ⟨23168512677608565464562641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15445675118405710309708427 23168512677608565464562641)
        ·
          refine ⟨17376384508206424098421981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23168512677608565464562641 17376384508206424098421981)
          ·
            refine ⟨6516144190577409036908243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17376384508206424098421981 6516144190577409036908243)
            ·
              refine ⟨9774216285866113555362365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516144190577409036908243 9774216285866113555362365)
              ·
                refine ⟨3665331107199792583260887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9774216285866113555362365 3665331107199792583260887)
                ·
                  refine ⟨5497996660799688874891331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665331107199792583260887 5497996660799688874891331)
                  ·
                    refine ⟨8246994991199533312336997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5497996660799688874891331 8246994991199533312336997)
                    ·
                      refine ⟨1546311560849912496063187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8246994991199533312336997 1546311560849912496063187)
                      ·
                        rfl

theorem cell23_3011431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3011431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011431 prefixEnd_3011431 := by exact prefixLift 3011431
  have htrace : WordTrace (prefixWord ++ tailWord_3011431) baseStart_3011431 baseEnd_3011431 := by
    simpa [prefixWord, tailWord_3011431, baseEnd_3011431] using wordTrace_append hprefix tailTrace_3011431
  have hstable : (prefixWord ++ tailWord_3011431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011431).length < 2 ^ (prefixWord ++ tailWord_3011431).sum := by decide
  have hdescent : baseEnd_3011431 < baseStart_3011431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011441 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 2, 4]
def baseStart_3011441 : Nat := 118140960795 + 3011441 * 2 ^ 59
def prefixEnd_3011441 : Nat := 4983230072969 + 3 ^ 40 * 3011441 * 2
def baseEnd_3011441 : Nat := 515438898552152485646047

theorem tailTrace_3011441 : CollatzResearch.WordTrace tailWord_3011441 prefixEnd_3011441 515438898552152485646047 := by
  unfold tailWord_3011441
  simp only [CollatzResearch.WordTrace]
  refine ⟨109836276683071045021346177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73224184455380696680897451 109836276683071045021346177)
  ·
    refine ⟨82377207512303283766009633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109836276683071045021346177 82377207512303283766009633)
    ·
      refine ⟨61782905634227462824507225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82377207512303283766009633 61782905634227462824507225)
      ·
        refine ⟨46337179225670597118380419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61782905634227462824507225 46337179225670597118380419)
        ·
          refine ⟨69505768838505895677570629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46337179225670597118380419 69505768838505895677570629)
          ·
            refine ⟨13032331657219855439544493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69505768838505895677570629 13032331657219855439544493)
            ·
              refine ⟨4887124371457445789829185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13032331657219855439544493 4887124371457445789829185)
              ·
                refine ⟨3665343278593084342371889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887124371457445789829185 3665343278593084342371889)
                ·
                  refine ⟨2749007458944813256778917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3665343278593084342371889 2749007458944813256778917)
                  ·
                    refine ⟨515438898552152485646047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2749007458944813256778917 515438898552152485646047)
                    ·
                      rfl

theorem cell23_3011441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_3011441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011441 prefixEnd_3011441 := by exact prefixLift 3011441
  have htrace : WordTrace (prefixWord ++ tailWord_3011441) baseStart_3011441 baseEnd_3011441 := by
    simpa [prefixWord, tailWord_3011441, baseEnd_3011441] using wordTrace_append hprefix tailTrace_3011441
  have hstable : (prefixWord ++ tailWord_3011441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011441).length < 2 ^ (prefixWord ++ tailWord_3011441).sum := by decide
  have hdescent : baseEnd_3011441 < baseStart_3011441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011461 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_3011461 : Nat := 118140960795 + 3011461 * 2 ^ 59
def prefixEnd_3011461 : Nat := 4983230072969 + 3 ^ 40 * 3011461 * 2
def baseEnd_3011461 : Nat := 1546326965269547378688049

theorem tailTrace_3011461 : CollatzResearch.WordTrace tailWord_3011461 prefixEnd_3011461 1546326965269547378688049 := by
  unfold tailWord_3011461
  simp only [CollatzResearch.WordTrace]
  refine ⟨109837006142998588437074237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73224670761999058958049491 109837006142998588437074237)
  ·
    refine ⟨41188877303624470663902839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109837006142998588437074237 41188877303624470663902839)
    ·
      refine ⟨61783315955436705995854259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41188877303624470663902839 61783315955436705995854259)
      ·
        refine ⟨92674973933155058993781389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61783315955436705995854259 92674973933155058993781389)
        ·
          refine ⟨34753115224933147122668021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92674973933155058993781389 34753115224933147122668021)
          ·
            refine ⟨3258104552337482542750127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34753115224933147122668021 3258104552337482542750127)
            ·
              refine ⟨4887156828506223814125191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258104552337482542750127 4887156828506223814125191)
              ·
                refine ⟨7330735242759335721187787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4887156828506223814125191 7330735242759335721187787)
                ·
                  refine ⟨10996102864139003581781681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7330735242759335721187787 10996102864139003581781681)
                  ·
                    refine ⟨8247077148104252686336261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10996102864139003581781681 8247077148104252686336261)
                    ·
                      refine ⟨1546326965269547378688049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8247077148104252686336261 1546326965269547378688049)
                      ·
                        rfl

theorem cell23_3011461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_3011461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011461 prefixEnd_3011461 := by exact prefixLift 3011461
  have htrace : WordTrace (prefixWord ++ tailWord_3011461) baseStart_3011461 baseEnd_3011461 := by
    simpa [prefixWord, tailWord_3011461, baseEnd_3011461] using wordTrace_append hprefix tailTrace_3011461
  have hstable : (prefixWord ++ tailWord_3011461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011461).length < 2 ^ (prefixWord ++ tailWord_3011461).sum := by decide
  have hdescent : baseEnd_3011461 < baseStart_3011461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011467 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 2, 7]
def baseStart_3011467 : Nat := 118140960795 + 3011467 * 2 ^ 59
def prefixEnd_3011467 : Nat := 4983230072969 + 3 ^ 40 * 3011467 * 2
def baseEnd_3011467 : Nat := 515443348717824785071007

theorem tailTrace_3011467 : CollatzResearch.WordTrace tailWord_3011467 prefixEnd_3011467 515443348717824785071007 := by
  unfold tailWord_3011467
  simp only [CollatzResearch.WordTrace]
  refine ⟨109837224980976851461792655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73224816653984567641195103 109837224980976851461792655)
  ·
    refine ⟨164755837471465277192688983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109837224980976851461792655 164755837471465277192688983)
    ·
      refine ⟨247133756207197915789033475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164755837471465277192688983 247133756207197915789033475)
      ·
        refine ⟨370700634310796873683550213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247133756207197915789033475 370700634310796873683550213)
        ·
          refine ⟨69506368933274413815665665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370700634310796873683550213 69506368933274413815665665)
          ·
            refine ⟨52129776699955810361749249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69506368933274413815665665 52129776699955810361749249)
            ·
              refine ⟨39097332524966857771311937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52129776699955810361749249 39097332524966857771311937)
              ·
                refine ⟨29322999393725143328483953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39097332524966857771311937 29322999393725143328483953)
                ·
                  refine ⟨21992249545293857496362965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29322999393725143328483953 21992249545293857496362965)
                  ·
                    refine ⟨515443348717824785071007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21992249545293857496362965 515443348717824785071007)
                    ·
                      rfl

theorem cell23_3011467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_3011467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011467 prefixEnd_3011467 := by exact prefixLift 3011467
  have htrace : WordTrace (prefixWord ++ tailWord_3011467) baseStart_3011467 baseEnd_3011467 := by
    simpa [prefixWord, tailWord_3011467, baseEnd_3011467] using wordTrace_append hprefix tailTrace_3011467
  have hstable : (prefixWord ++ tailWord_3011467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011467).length < 2 ^ (prefixWord ++ tailWord_3011467).sum := by decide
  have hdescent : baseEnd_3011467 < baseStart_3011467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011538 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3011538 : Nat := 118140960795 + 3011538 * 2 ^ 59
def prefixEnd_3011538 : Nat := 4983230072969 + 3 ^ 40 * 3011538 * 2
def baseEnd_3011538 : Nat := 1546366503279943577425195

theorem tailTrace_3011538 : CollatzResearch.WordTrace tailWord_3011538 prefixEnd_3011538 1546366503279943577425195 := by
  unfold tailWord_3011538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27459953640929907646906817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73226543042479753725084845 27459953640929907646906817)
  ·
    refine ⟨20594965230697430735180113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27459953640929907646906817 20594965230697430735180113)
    ·
      refine ⟨15446223923023073051385085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20594965230697430735180113 15446223923023073051385085)
      ·
        refine ⟨5792333971133652394269407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15446223923023073051385085 5792333971133652394269407)
        ·
          refine ⟨8688500956700478591404111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792333971133652394269407 8688500956700478591404111)
          ·
            refine ⟨13032751435050717887106167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688500956700478591404111 13032751435050717887106167)
            ·
              refine ⟨19549127152576076830659251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13032751435050717887106167 19549127152576076830659251)
              ·
                refine ⟨29323690728864115245988877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19549127152576076830659251 29323690728864115245988877)
                ·
                  refine ⟨10996384023324043217245829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29323690728864115245988877 10996384023324043217245829)
                  ·
                    refine ⟨2061822004373258103233593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10996384023324043217245829 2061822004373258103233593)
                    ·
                      refine ⟨1546366503279943577425195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061822004373258103233593 1546366503279943577425195)
                      ·
                        rfl

theorem cell23_3011538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3011538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011538 prefixEnd_3011538 := by exact prefixLift 3011538
  have htrace : WordTrace (prefixWord ++ tailWord_3011538) baseStart_3011538 baseEnd_3011538 := by
    simpa [prefixWord, tailWord_3011538, baseEnd_3011538] using wordTrace_append hprefix tailTrace_3011538
  have hstable : (prefixWord ++ tailWord_3011538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011538).length < 2 ^ (prefixWord ++ tailWord_3011538).sum := by decide
  have hdescent : baseEnd_3011538 < baseStart_3011538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011555 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 2, 2, 2]
def baseStart_3011555 : Nat := 118140960795 + 3011555 * 2 ^ 59
def prefixEnd_3011555 : Nat := 4983230072969 + 3 ^ 40 * 3011555 * 2
def baseEnd_3011555 : Nat := 1546375232451070010912617

theorem tailTrace_3011555 : CollatzResearch.WordTrace tailWord_3011555 prefixEnd_3011555 1546375232451070010912617 := by
  unfold tailWord_3011555
  simp only [CollatzResearch.WordTrace]
  refine ⟨109840434604658042490996119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73226956403105361660664079 109840434604658042490996119)
  ·
    refine ⟨164760651906987063736494179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109840434604658042490996119 164760651906987063736494179)
    ·
      refine ⟨247140977860480595604741269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164760651906987063736494179 247140977860480595604741269)
      ·
        refine ⟨11584733337210027918972247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 247140977860480595604741269 11584733337210027918972247)
        ·
          refine ⟨17377100005815041878458371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11584733337210027918972247 17377100005815041878458371)
          ·
            refine ⟨26065650008722562817687557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17377100005815041878458371 26065650008722562817687557)
            ·
              refine ⟨4887309376635480528316417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26065650008722562817687557 4887309376635480528316417)
              ·
                refine ⟨3665482032476610396237313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887309376635480528316417 3665482032476610396237313)
                ·
                  refine ⟨2749111524357457797177985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3665482032476610396237313 2749111524357457797177985)
                  ·
                    refine ⟨2061833643268093347883489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2749111524357457797177985 2061833643268093347883489)
                    ·
                      refine ⟨1546375232451070010912617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061833643268093347883489 1546375232451070010912617)
                      ·
                        rfl

theorem cell23_3011555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_3011555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011555 prefixEnd_3011555 := by exact prefixLift 3011555
  have htrace : WordTrace (prefixWord ++ tailWord_3011555) baseStart_3011555 baseEnd_3011555 := by
    simpa [prefixWord, tailWord_3011555, baseEnd_3011555] using wordTrace_append hprefix tailTrace_3011555
  have hstable : (prefixWord ++ tailWord_3011555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011555).length < 2 ^ (prefixWord ++ tailWord_3011555).sum := by decide
  have hdescent : baseEnd_3011555 < baseStart_3011555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011581 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_3011581 : Nat := 118140960795 + 3011581 * 2 ^ 59
def prefixEnd_3011581 : Nat := 4983230072969 + 3 ^ 40 * 3011581 * 2
def baseEnd_3011581 : Nat := 1546388582948086909187497

theorem tailTrace_3011581 : CollatzResearch.WordTrace tailWord_3011581 prefixEnd_3011581 1546388582948086909187497 := by
  unfold tailWord_3011581
  simp only [CollatzResearch.WordTrace]
  refine ⟨109841382902563848931442597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73227588601709232620961731 109841382902563848931442597)
  ·
    refine ⟨20595259294230721674645487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109841382902563848931442597 20595259294230721674645487)
    ·
      refine ⟨30892888941346082511968231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20595259294230721674645487 30892888941346082511968231)
      ·
        refine ⟨46339333412019123767952347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30892888941346082511968231 46339333412019123767952347)
        ·
          refine ⟨69509000118028685651928521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46339333412019123767952347 69509000118028685651928521)
          ·
            refine ⟨52131750088521514238946391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69509000118028685651928521 52131750088521514238946391)
            ·
              refine ⟨78197625132782271358419587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52131750088521514238946391 78197625132782271358419587)
              ·
                refine ⟨117296437699173407037629381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78197625132782271358419587 117296437699173407037629381)
                ·
                  refine ⟨21993082068595013819555509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117296437699173407037629381 21993082068595013819555509)
                  ·
                    refine ⟨2061851443930782545583329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21993082068595013819555509 2061851443930782545583329)
                    ·
                      refine ⟨1546388582948086909187497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061851443930782545583329 1546388582948086909187497)
                      ·
                        rfl

theorem cell23_3011581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_3011581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011581 prefixEnd_3011581 := by exact prefixLift 3011581
  have htrace : WordTrace (prefixWord ++ tailWord_3011581) baseStart_3011581 baseEnd_3011581 := by
    simpa [prefixWord, tailWord_3011581, baseEnd_3011581] using wordTrace_append hprefix tailTrace_3011581
  have hstable : (prefixWord ++ tailWord_3011581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011581).length < 2 ^ (prefixWord ++ tailWord_3011581).sum := by decide
  have hdescent : baseEnd_3011581 < baseStart_3011581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011655 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 1, 4]
def baseStart_3011655 : Nat := 118140960795 + 3011655 * 2 ^ 59
def prefixEnd_3011655 : Nat := 4983230072969 + 3 ^ 40 * 3011655 * 2
def baseEnd_3011655 : Nat := 515475526838839873220719

theorem tailTrace_3011655 : CollatzResearch.WordTrace tailWord_3011655 prefixEnd_3011655 515475526838839873220719 := by
  unfold tailWord_3011655
  simp only [CollatzResearch.WordTrace]
  refine ⟨109844081904295759569636419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73229387936197173046424279 109844081904295759569636419)
  ·
    refine ⟨164766122856443639354454629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109844081904295759569636419 164766122856443639354454629)
    ·
      refine ⟨30893648035583182378960243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164766122856443639354454629 30893648035583182378960243)
      ·
        refine ⟨46340472053374773568440365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30893648035583182378960243 46340472053374773568440365)
        ·
          refine ⟨17377677020015540088165137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46340472053374773568440365 17377677020015540088165137)
          ·
            refine ⟨13033257765011655066123853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17377677020015540088165137 13033257765011655066123853)
            ·
              refine ⟨4887471661879370649796445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13033257765011655066123853 4887471661879370649796445)
              ·
                refine ⟨1832801873204763993673667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4887471661879370649796445 1832801873204763993673667)
                ·
                  refine ⟨2749202809807145990510501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832801873204763993673667 2749202809807145990510501)
                  ·
                    refine ⟨515475526838839873220719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2749202809807145990510501 515475526838839873220719)
                    ·
                      rfl

theorem cell23_3011655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_3011655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011655 prefixEnd_3011655 := by exact prefixLift 3011655
  have htrace : WordTrace (prefixWord ++ tailWord_3011655) baseStart_3011655 baseEnd_3011655 := by
    simpa [prefixWord, tailWord_3011655, baseEnd_3011655] using wordTrace_append hprefix tailTrace_3011655
  have hstable : (prefixWord ++ tailWord_3011655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011655).length < 2 ^ (prefixWord ++ tailWord_3011655).sum := by decide
  have hdescent : baseEnd_3011655 < baseStart_3011655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011748 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3011748 : Nat := 118140960795 + 3011748 * 2 ^ 59
def prefixEnd_3011748 : Nat := 4983230072969 + 3 ^ 40 * 3011748 * 2
def baseEnd_3011748 : Nat := 1546474334217387755799229

theorem tailTrace_3011748 : CollatzResearch.WordTrace tailWord_3011748 prefixEnd_3011748 1546474334217387755799229 := by
  unfold tailWord_3011748
  simp only [CollatzResearch.WordTrace]
  refine ⟨54923736946479418226385949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73231649261972557635181265 54923736946479418226385949)
  ·
    refine ⟨20596401354929781834894731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54923736946479418226385949 20596401354929781834894731)
    ·
      refine ⟨30894602032394672752342097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20596401354929781834894731 30894602032394672752342097)
      ·
        refine ⟨23170951524296004564256573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30894602032394672752342097 23170951524296004564256573)
        ·
          refine ⟨8689106821611001711596215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23170951524296004564256573 8689106821611001711596215)
          ·
            refine ⟨13033660232416502567394323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689106821611001711596215 13033660232416502567394323)
            ·
              refine ⟨19550490348624753851091485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033660232416502567394323 19550490348624753851091485)
              ·
                refine ⟨7331433880734282694159307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19550490348624753851091485 7331433880734282694159307)
                ·
                  refine ⟨10997150821101424041238961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7331433880734282694159307 10997150821101424041238961)
                  ·
                    refine ⟨8247863115826068030929221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10997150821101424041238961 8247863115826068030929221)
                    ·
                      refine ⟨1546474334217387755799229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8247863115826068030929221 1546474334217387755799229)
                      ·
                        rfl

theorem cell23_3011748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3011748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011748 prefixEnd_3011748 := by exact prefixLift 3011748
  have htrace : WordTrace (prefixWord ++ tailWord_3011748) baseStart_3011748 baseEnd_3011748 := by
    simpa [prefixWord, tailWord_3011748, baseEnd_3011748] using wordTrace_append hprefix tailTrace_3011748
  have hstable : (prefixWord ++ tailWord_3011748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011748).length < 2 ^ (prefixWord ++ tailWord_3011748).sum := by decide
  have hdescent : baseEnd_3011748 < baseStart_3011748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011766 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3011766 : Nat := 118140960795 + 3011766 * 2 ^ 59
def prefixEnd_3011766 : Nat := 4983230072969 + 3 ^ 40 * 3011766 * 2
def baseEnd_3011766 : Nat := 515494525623056228458049

theorem tailTrace_3011766 : CollatzResearch.WordTrace tailWord_3011766 prefixEnd_3011766 515494525623056228458049 := by
  unfold tailWord_3011766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6865508150430851595432947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73232086937929083684618101 6865508150430851595432947)
  ·
    refine ⟨10298262225646277393149421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6865508150430851595432947 10298262225646277393149421)
    ·
      refine ⟨3861848334617354022431033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10298262225646277393149421 3861848334617354022431033)
      ·
        refine ⟨2896386250963015516823275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3861848334617354022431033 2896386250963015516823275)
        ·
          refine ⟨4344579376444523275234913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896386250963015516823275 4344579376444523275234913)
          ·
            refine ⟨3258434532333392456426185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4344579376444523275234913 3258434532333392456426185)
            ·
              refine ⟨2443825899250044342319639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3258434532333392456426185 2443825899250044342319639)
              ·
                refine ⟨3665738848875066513479459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443825899250044342319639 3665738848875066513479459)
                ·
                  refine ⟨5498608273312599770219189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665738848875066513479459 5498608273312599770219189)
                  ·
                    refine ⟨515494525623056228458049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5498608273312599770219189 515494525623056228458049)
                    ·
                      rfl

theorem cell23_3011766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3011766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011766 prefixEnd_3011766 := by exact prefixLift 3011766
  have htrace : WordTrace (prefixWord ++ tailWord_3011766) baseStart_3011766 baseEnd_3011766 := by
    simpa [prefixWord, tailWord_3011766, baseEnd_3011766] using wordTrace_append hprefix tailTrace_3011766
  have hstable : (prefixWord ++ tailWord_3011766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011766).length < 2 ^ (prefixWord ++ tailWord_3011766).sum := by decide
  have hdescent : baseEnd_3011766 < baseStart_3011766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011769 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 1, 2, 2]
def baseStart_3011769 : Nat := 118140960795 + 3011769 * 2 ^ 59
def prefixEnd_3011769 : Nat := 4983230072969 + 3 ^ 40 * 3011769 * 2
def baseEnd_3011769 : Nat := 1546485117311132173636633

theorem tailTrace_3011769 : CollatzResearch.WordTrace tailWord_3011769 prefixEnd_3011769 1546485117311132173636633 := by
  unfold tailWord_3011769
  simp only [CollatzResearch.WordTrace]
  refine ⟨109848239825882757039286361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73232159883921838026190907 109848239825882757039286361)
  ·
    refine ⟨82386179869412067779464771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109848239825882757039286361 82386179869412067779464771)
    ·
      refine ⟨123579269804118101669197157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82386179869412067779464771 123579269804118101669197157)
      ·
        refine ⟨23171113088272144062974467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123579269804118101669197157 23171113088272144062974467)
        ·
          refine ⟨34756669632408216094461701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23171113088272144062974467 34756669632408216094461701)
          ·
            refine ⟨6516875556076540517711569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34756669632408216094461701 6516875556076540517711569)
            ·
              refine ⟨4887656667057405388283677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6516875556076540517711569 4887656667057405388283677)
              ·
                refine ⟨1832871250146527020606379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4887656667057405388283677 1832871250146527020606379)
                ·
                  refine ⟨2749306875219790530909569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832871250146527020606379 2749306875219790530909569)
                  ·
                    refine ⟨2061980156414842898182177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2749306875219790530909569 2061980156414842898182177)
                    ·
                      refine ⟨1546485117311132173636633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061980156414842898182177 1546485117311132173636633)
                      ·
                        rfl

theorem cell23_3011769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_3011769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011769 prefixEnd_3011769 := by exact prefixLift 3011769
  have htrace : WordTrace (prefixWord ++ tailWord_3011769) baseStart_3011769 baseEnd_3011769 := by
    simpa [prefixWord, tailWord_3011769, baseEnd_3011769] using wordTrace_append hprefix tailTrace_3011769
  have hstable : (prefixWord ++ tailWord_3011769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011769).length < 2 ^ (prefixWord ++ tailWord_3011769).sum := by decide
  have hdescent : baseEnd_3011769 < baseStart_3011769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011772 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_3011772 : Nat := 118140960795 + 3011772 * 2 ^ 59
def prefixEnd_3011772 : Nat := 4983230072969 + 3 ^ 40 * 3011772 * 2
def baseEnd_3011772 : Nat := 1546486657753095661899119

theorem tailTrace_3011772 : CollatzResearch.WordTrace tailWord_3011772 prefixEnd_3011772 1546486657753095661899119 := by
  unfold tailWord_3011772
  simp only [CollatzResearch.WordTrace]
  refine ⟨54924174622435944275822785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73232232829914592367763713 54924174622435944275822785)
  ·
    refine ⟨41193130966826958206867089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54924174622435944275822785 41193130966826958206867089)
    ·
      refine ⟨30894848225120218655150317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41193130966826958206867089 30894848225120218655150317)
      ·
        refine ⟨11585568084420081995681369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30894848225120218655150317 11585568084420081995681369)
        ·
          refine ⟨8689176063315061496761027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11585568084420081995681369 8689176063315061496761027)
          ·
            refine ⟨13033764094972592245141541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689176063315061496761027 13033764094972592245141541)
            ·
              refine ⟨2443830767807361045964039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13033764094972592245141541 2443830767807361045964039)
              ·
                refine ⟨3665746151711041568946059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443830767807361045964039 3665746151711041568946059)
                ·
                  refine ⟨5498619227566562353419089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665746151711041568946059 5498619227566562353419089)
                  ·
                    refine ⟨4123964420674921765064317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498619227566562353419089 4123964420674921765064317)
                    ·
                      refine ⟨1546486657753095661899119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4123964420674921765064317 1546486657753095661899119)
                      ·
                        rfl

theorem cell23_3011772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_3011772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011772 prefixEnd_3011772 := by exact prefixLift 3011772
  have htrace : WordTrace (prefixWord ++ tailWord_3011772) baseStart_3011772 baseEnd_3011772 := by
    simpa [prefixWord, tailWord_3011772, baseEnd_3011772] using wordTrace_append hprefix tailTrace_3011772
  have hstable : (prefixWord ++ tailWord_3011772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011772).length < 2 ^ (prefixWord ++ tailWord_3011772).sum := by decide
  have hdescent : baseEnd_3011772 < baseStart_3011772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011791 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_3011791 : Nat := 118140960795 + 3011791 * 2 ^ 59
def prefixEnd_3011791 : Nat := 4983230072969 + 3 ^ 40 * 3011791 * 2
def baseEnd_3011791 : Nat := 1546496413885531087561531

theorem tailTrace_3011791 : CollatzResearch.WordTrace tailWord_3011791 prefixEnd_3011791 1546496413885531087561531 := by
  unfold tailWord_3011791
  simp only [CollatzResearch.WordTrace]
  refine ⟨109849042231803054796587227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73232694821202036531058151 109849042231803054796587227)
  ·
    refine ⟨164773563347704582194880841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109849042231803054796587227 164773563347704582194880841)
    ·
      refine ⟨123580172510778436646160631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164773563347704582194880841 123580172510778436646160631)
      ·
        refine ⟨185370258766167654969240947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123580172510778436646160631 185370258766167654969240947)
        ·
          refine ⟨278055388149251482453861421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185370258766167654969240947 278055388149251482453861421)
          ·
            refine ⟨104270770555969305920198033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278055388149251482453861421 104270770555969305920198033)
            ·
              refine ⟨78203077916976979440148525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104270770555969305920198033 78203077916976979440148525)
              ·
                refine ⟨29326154218866367290055697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78203077916976979440148525 29326154218866367290055697)
                ·
                  refine ⟨21994615664149775467541773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29326154218866367290055697 21994615664149775467541773)
                  ·
                    refine ⟨8247980874056165800328165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21994615664149775467541773 8247980874056165800328165)
                    ·
                      refine ⟨1546496413885531087561531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8247980874056165800328165 1546496413885531087561531)
                      ·
                        rfl

theorem cell23_3011791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_3011791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011791 prefixEnd_3011791 := by exact prefixLift 3011791
  have htrace : WordTrace (prefixWord ++ tailWord_3011791) baseStart_3011791 baseEnd_3011791 := by
    simpa [prefixWord, tailWord_3011791, baseEnd_3011791] using wordTrace_append hprefix tailTrace_3011791
  have hstable : (prefixWord ++ tailWord_3011791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011791).length < 2 ^ (prefixWord ++ tailWord_3011791).sum := by decide
  have hdescent : baseEnd_3011791 < baseStart_3011791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011905 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3011905 : Nat := 118140960795 + 3011905 * 2 ^ 59
def prefixEnd_3011905 : Nat := 4983230072969 + 3 ^ 40 * 3011905 * 2
def baseEnd_3011905 : Nat := 1546554950680143641536007

theorem tailTrace_3011905 : CollatzResearch.WordTrace tailWord_3011905 prefixEnd_3011905 1546554950680143641536007 := by
  unfold tailWord_3011905
  simp only [CollatzResearch.WordTrace]
  refine ⟨109853200153390052266237169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73235466768926701510824779 109853200153390052266237169)
  ·
    refine ⟨82389900115042539199677877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109853200153390052266237169 82389900115042539199677877)
    ·
      refine ⟨7724053135785238049969801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82389900115042539199677877 7724053135785238049969801)
      ·
        refine ⟨5793039851838928537477351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7724053135785238049969801 5793039851838928537477351)
        ·
          refine ⟨8689559777758392806216027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793039851838928537477351 8689559777758392806216027)
          ·
            refine ⟨13034339666637589209324041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689559777758392806216027 13034339666637589209324041)
            ·
              refine ⟨9775754749978191906993031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13034339666637589209324041 9775754749978191906993031)
              ·
                refine ⟨14663632124967287860489547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775754749978191906993031 14663632124967287860489547)
                ·
                  refine ⟨21995448187450931790734321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14663632124967287860489547 21995448187450931790734321)
                  ·
                    refine ⟨16496586140588198843050741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21995448187450931790734321 16496586140588198843050741)
                    ·
                      refine ⟨1546554950680143641536007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16496586140588198843050741 1546554950680143641536007)
                      ·
                        rfl

theorem cell23_3011905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3011905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011905 prefixEnd_3011905 := by exact prefixLift 3011905
  have htrace : WordTrace (prefixWord ++ tailWord_3011905) baseStart_3011905 baseEnd_3011905 := by
    simpa [prefixWord, tailWord_3011905, baseEnd_3011905] using wordTrace_append hprefix tailTrace_3011905
  have hstable : (prefixWord ++ tailWord_3011905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011905).length < 2 ^ (prefixWord ++ tailWord_3011905).sum := by decide
  have hdescent : baseEnd_3011905 < baseStart_3011905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011925 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_3011925 : Nat := 118140960795 + 3011925 * 2 ^ 59
def prefixEnd_3011925 : Nat := 4983230072969 + 3 ^ 40 * 3011925 * 2
def baseEnd_3011925 : Nat := 515521740097744521095305

theorem tailTrace_3011925 : CollatzResearch.WordTrace tailWord_3011925 prefixEnd_3011925 515521740097744521095305 := by
  unfold tailWord_3011925
  simp only [CollatzResearch.WordTrace]
  refine ⟨109853929613317595681965229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73235953075545063787976819 109853929613317595681965229)
  ·
    refine ⟨41195223604994098380736961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109853929613317595681965229 41195223604994098380736961)
    ·
      refine ⟨30896417703745573785552721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41195223604994098380736961 30896417703745573785552721)
      ·
        refine ⟨23172313277809180339164541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30896417703745573785552721 23172313277809180339164541)
        ·
          refine ⟨8689617479178442627186703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23172313277809180339164541 8689617479178442627186703)
          ·
            refine ⟨13034426218767663940780055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689617479178442627186703 13034426218767663940780055)
            ·
              refine ⟨19551639328151495911170083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13034426218767663940780055 19551639328151495911170083)
              ·
                refine ⟨29327458992227243866755125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19551639328151495911170083 29327458992227243866755125)
                ·
                  refine ⟨2749449280521304112508293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29327458992227243866755125 2749449280521304112508293)
                  ·
                    refine ⟨515521740097744521095305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2749449280521304112508293 515521740097744521095305)
                    ·
                      rfl

theorem cell23_3011925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_3011925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011925 prefixEnd_3011925 := by exact prefixLift 3011925
  have htrace : WordTrace (prefixWord ++ tailWord_3011925) baseStart_3011925 baseEnd_3011925 := by
    simpa [prefixWord, tailWord_3011925, baseEnd_3011925] using wordTrace_append hprefix tailTrace_3011925
  have hstable : (prefixWord ++ tailWord_3011925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011925).length < 2 ^ (prefixWord ++ tailWord_3011925).sum := by decide
  have hdescent : baseEnd_3011925 < baseStart_3011925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011968 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_3011968 : Nat := 118140960795 + 3011968 * 2 ^ 59
def prefixEnd_3011968 : Nat := 4983230072969 + 3 ^ 40 * 3011968 * 2
def baseEnd_3011968 : Nat := 515529099987125631682739

theorem tailTrace_3011968 : CollatzResearch.WordTrace tailWord_3011968 prefixEnd_3011968 515529099987125631682739 := by
  unfold tailWord_3011968
  simp only [CollatzResearch.WordTrace]
  refine ⟨54927748976080907012890279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73236998634774542683853705 54927748976080907012890279)
  ·
    refine ⟨82391623464121360519335419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54927748976080907012890279 82391623464121360519335419)
    ·
      refine ⟨123587435196182040779003129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82391623464121360519335419 123587435196182040779003129)
      ·
        refine ⟨92690576397136530584252347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123587435196182040779003129 92690576397136530584252347)
        ·
          refine ⟨139035864595704795876378521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92690576397136530584252347 139035864595704795876378521)
          ·
            refine ⟨104276898446778596907283891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139035864595704795876378521 104276898446778596907283891)
            ·
              refine ⟨156415347670167895360925837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104276898446778596907283891 156415347670167895360925837)
              ·
                refine ⟨58655755376312960760347189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156415347670167895360925837 58655755376312960760347189)
                ·
                  refine ⟨5498977066529340071282549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58655755376312960760347189 5498977066529340071282549)
                  ·
                    refine ⟨515529099987125631682739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5498977066529340071282549 515529099987125631682739)
                    ·
                      rfl

theorem cell23_3011968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_3011968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011968 prefixEnd_3011968 := by exact prefixLift 3011968
  have htrace : WordTrace (prefixWord ++ tailWord_3011968) baseStart_3011968 baseEnd_3011968 := by
    simpa [prefixWord, tailWord_3011968, baseEnd_3011968] using wordTrace_append hprefix tailTrace_3011968
  have hstable : (prefixWord ++ tailWord_3011968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011968).length < 2 ^ (prefixWord ++ tailWord_3011968).sum := by decide
  have hdescent : baseEnd_3011968 < baseStart_3011968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011972 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 6]
def baseStart_3011972 : Nat := 118140960795 + 3011972 * 2 ^ 59
def prefixEnd_3011972 : Nat := 4983230072969 + 3 ^ 40 * 3011972 * 2
def baseEnd_3011972 : Nat := 171843261542666097710911

theorem tailTrace_3011972 : CollatzResearch.WordTrace tailWord_3011972 prefixEnd_3011972 171843261542666097710911 := by
  unfold tailWord_3011972
  simp only [CollatzResearch.WordTrace]
  refine ⟨54927821922073661354463085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73237095896098215139284113 54927821922073661354463085)
  ·
    refine ⟨20597933220777623007923657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54927821922073661354463085 20597933220777623007923657)
    ·
      refine ⟨15448449915583217255942743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20597933220777623007923657 15448449915583217255942743)
      ·
        refine ⟨23172674873374825883914115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15448449915583217255942743 23172674873374825883914115)
        ·
          refine ⟨34759012310062238825871173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23172674873374825883914115 34759012310062238825871173)
          ·
            refine ⟨6517314808136669779850845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34759012310062238825871173 6517314808136669779850845)
            ·
              refine ⟨2443993053051251167444067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6517314808136669779850845 2443993053051251167444067)
              ·
                refine ⟨3665989579576876751166101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443993053051251167444067 3665989579576876751166101)
                ·
                  refine ⟨171843261542666097710911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3665989579576876751166101 171843261542666097710911)
                  ·
                    rfl

theorem cell23_3011972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_3011972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3011972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3011972 prefixEnd_3011972 := by exact prefixLift 3011972
  have htrace : WordTrace (prefixWord ++ tailWord_3011972) baseStart_3011972 baseEnd_3011972 := by
    simpa [prefixWord, tailWord_3011972, baseEnd_3011972] using wordTrace_append hprefix tailTrace_3011972
  have hstable : (prefixWord ++ tailWord_3011972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011972).length < 2 ^ (prefixWord ++ tailWord_3011972).sum := by decide
  have hdescent : baseEnd_3011972 < baseStart_3011972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012002 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3012002 : Nat := 118140960795 + 3012002 * 2 ^ 59
def prefixEnd_3012002 : Nat := 4983230072969 + 3 ^ 40 * 3012002 * 2
def baseEnd_3012002 : Nat := 515534919434543254007687

theorem tailTrace_3012002 : CollatzResearch.WordTrace tailWord_3012002 prefixEnd_3012002 515534919434543254007687 := by
  unfold tailWord_3012002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27464184508509659458129565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73237825356025758555012173 27464184508509659458129565)
  ·
    refine ⟨10299069190691122296798587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27464184508509659458129565 10299069190691122296798587)
    ·
      refine ⟨15448603786036683445197881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10299069190691122296798587 15448603786036683445197881)
      ·
        refine ⟨11586452839527512583898411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15448603786036683445197881 11586452839527512583898411)
        ·
          refine ⟨17379679259291268875847617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11586452839527512583898411 17379679259291268875847617)
          ·
            refine ⟨13034759444468451656885713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17379679259291268875847617 13034759444468451656885713)
            ·
              refine ⟨9776069583351338742664285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13034759444468451656885713 9776069583351338742664285)
              ·
                refine ⟨3666026093756752028499107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9776069583351338742664285 3666026093756752028499107)
                ·
                  refine ⟨5499039140635128042748661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666026093756752028499107 5499039140635128042748661)
                  ·
                    refine ⟨515534919434543254007687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5499039140635128042748661 515534919434543254007687)
                    ·
                      rfl

theorem cell23_3012002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3012002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012002 prefixEnd_3012002 := by exact prefixLift 3012002
  have htrace : WordTrace (prefixWord ++ tailWord_3012002) baseStart_3012002 baseEnd_3012002 := by
    simpa [prefixWord, tailWord_3012002, baseEnd_3012002] using wordTrace_append hprefix tailTrace_3012002
  have hstable : (prefixWord ++ tailWord_3012002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012002).length < 2 ^ (prefixWord ++ tailWord_3012002).sum := by decide
  have hdescent : baseEnd_3012002 < baseStart_3012002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012042 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3012042 : Nat := 118140960795 + 3012042 * 2 ^ 59
def prefixEnd_3012042 : Nat := 4983230072969 + 3 ^ 40 * 3012042 * 2
def baseEnd_3012042 : Nat := 1546625297529809605522877

theorem tailTrace_3012042 : CollatzResearch.WordTrace tailWord_3012042 prefixEnd_3012042 1546625297529809605522877 := by
  unfold tailWord_3012042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27464549238473431165993595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73238797969262483109316253 27464549238473431165993595)
  ·
    refine ⟨41196823857710146748990393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27464549238473431165993595 41196823857710146748990393)
    ·
      refine ⟨30897617893282610061742795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41196823857710146748990393 30897617893282610061742795)
      ·
        refine ⟨46346426839923915092614193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30897617893282610061742795 46346426839923915092614193)
        ·
          refine ⟨34759820129942936319460645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46346426839923915092614193 34759820129942936319460645)
          ·
            refine ⟨6517466274364300559898871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34759820129942936319460645 6517466274364300559898871)
            ·
              refine ⟨9776199411546450839848307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517466274364300559898871 9776199411546450839848307)
              ·
                refine ⟨14664299117319676259772461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9776199411546450839848307 14664299117319676259772461)
                ·
                  refine ⟨5499112168994878597414673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14664299117319676259772461 5499112168994878597414673)
                  ·
                    refine ⟨4124334126746158948061005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5499112168994878597414673 4124334126746158948061005)
                    ·
                      refine ⟨1546625297529809605522877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4124334126746158948061005 1546625297529809605522877)
                      ·
                        rfl

theorem cell23_3012042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3012042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012042 prefixEnd_3012042 := by exact prefixLift 3012042
  have htrace : WordTrace (prefixWord ++ tailWord_3012042) baseStart_3012042 baseEnd_3012042 := by
    simpa [prefixWord, tailWord_3012042, baseEnd_3012042] using wordTrace_append hprefix tailTrace_3012042
  have hstable : (prefixWord ++ tailWord_3012042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012042).length < 2 ^ (prefixWord ++ tailWord_3012042).sum := by decide
  have hdescent : baseEnd_3012042 < baseStart_3012042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012048 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_3012048 : Nat := 118140960795 + 3012048 * 2 ^ 59
def prefixEnd_3012048 : Nat := 4983230072969 + 3 ^ 40 * 3012048 * 2
def baseEnd_3012048 : Nat := 1546628378413736582047849

theorem tailTrace_3012048 : CollatzResearch.WordTrace tailWord_3012048 prefixEnd_3012048 1546628378413736582047849 := by
  unfold tailWord_3012048
  simp only [CollatzResearch.WordTrace]
  refine ⟨54929207895935993844346399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73238943861247991792461865 54929207895935993844346399)
  ·
    refine ⟨82393811843903990766519599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54929207895935993844346399 82393811843903990766519599)
    ·
      refine ⟨123590717765855986149779399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82393811843903990766519599 123590717765855986149779399)
      ·
        refine ⟨185386076648783979224669099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123590717765855986149779399 185386076648783979224669099)
        ·
          refine ⟨278079114973175968837003649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185386076648783979224669099 278079114973175968837003649)
          ·
            refine ⟨208559336229881976627752737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278079114973175968837003649 208559336229881976627752737)
            ·
              refine ⟨156419502172411482470814553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208559336229881976627752737 156419502172411482470814553)
              ·
                refine ⟨117314626629308611853110915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156419502172411482470814553 117314626629308611853110915)
                ·
                  refine ⟨175971939943962917779666373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117314626629308611853110915 175971939943962917779666373)
                  ·
                    refine ⟨32994738739493047083687445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175971939943962917779666373 32994738739493047083687445)
                    ·
                      refine ⟨1546628378413736582047849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32994738739493047083687445 1546628378413736582047849)
                      ·
                        rfl

theorem cell23_3012048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_3012048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012048 prefixEnd_3012048 := by exact prefixLift 3012048
  have htrace : WordTrace (prefixWord ++ tailWord_3012048) baseStart_3012048 baseEnd_3012048 := by
    simpa [prefixWord, tailWord_3012048, baseEnd_3012048] using wordTrace_append hprefix tailTrace_3012048
  have hstable : (prefixWord ++ tailWord_3012048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012048).length < 2 ^ (prefixWord ++ tailWord_3012048).sum := by decide
  have hdescent : baseEnd_3012048 < baseStart_3012048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012165 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_3012165 : Nat := 118140960795 + 3012165 * 2 ^ 59
def prefixEnd_3012165 : Nat := 4983230072969 + 3 ^ 40 * 3012165 * 2
def baseEnd_3012165 : Nat := 515562818550104208094937

theorem tailTrace_3012165 : CollatzResearch.WordTrace tailWord_3012165 prefixEnd_3012165 515562818550104208094937 := by
  unfold tailWord_3012165
  simp only [CollatzResearch.WordTrace]
  refine ⟨109862683132448116670701949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73241788754965411113801299 109862683132448116670701949)
  ·
    refine ⟨41198506174668043751513231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109862683132448116670701949 41198506174668043751513231)
    ·
      refine ⟨61797759262002065627269847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41198506174668043751513231 61797759262002065627269847)
      ·
        refine ⟨92696638893003098440904771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61797759262002065627269847 92696638893003098440904771)
        ·
          refine ⟨139044958339504647661357157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92696638893003098440904771 139044958339504647661357157)
          ·
            refine ⟨26070929688657121436504467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139044958339504647661357157 26070929688657121436504467)
            ·
              refine ⟨39106394532985682154756701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26070929688657121436504467 39106394532985682154756701)
              ·
                refine ⟨14664897949869630808033763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39106394532985682154756701 14664897949869630808033763)
                ·
                  refine ⟨21997346924804446212050645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14664897949869630808033763 21997346924804446212050645)
                  ·
                    refine ⟨515562818550104208094937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21997346924804446212050645 515562818550104208094937)
                    ·
                      rfl

theorem cell23_3012165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_3012165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012165 prefixEnd_3012165 := by exact prefixLift 3012165
  have htrace : WordTrace (prefixWord ++ tailWord_3012165) baseStart_3012165 baseEnd_3012165 := by
    simpa [prefixWord, tailWord_3012165, baseEnd_3012165] using wordTrace_append hprefix tailTrace_3012165
  have hstable : (prefixWord ++ tailWord_3012165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012165).length < 2 ^ (prefixWord ++ tailWord_3012165).sum := by decide
  have hdescent : baseEnd_3012165 < baseStart_3012165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012166 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3012166 : Nat := 118140960795 + 3012166 * 2 ^ 59
def prefixEnd_3012166 : Nat := 4983230072969 + 3 ^ 40 * 3012166 * 2
def baseEnd_3012166 : Nat := 1546688969130967120372307

theorem tailTrace_3012166 : CollatzResearch.WordTrace tailWord_3012166 prefixEnd_3012166 1546688969130967120372307 := by
  unfold tailWord_3012166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433209987670140432546511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73241813070296329227658901 3433209987670140432546511)
  ·
    refine ⟨5149814981505210648819767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3433209987670140432546511 5149814981505210648819767)
    ·
      refine ⟨7724722472257815973229651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5149814981505210648819767 7724722472257815973229651)
      ·
        refine ⟨11587083708386723959844477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7724722472257815973229651 11587083708386723959844477)
        ·
          refine ⟨4345156390645021484941679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11587083708386723959844477 4345156390645021484941679)
          ·
            refine ⟨6517734585967532227412519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345156390645021484941679 6517734585967532227412519)
            ·
              refine ⟨9776601878951298341118779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517734585967532227412519 9776601878951298341118779)
              ·
                refine ⟨14664902818426947511678169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9776601878951298341118779 14664902818426947511678169)
                ·
                  refine ⟨10998677113820210633758627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14664902818426947511678169 10998677113820210633758627)
                  ·
                    refine ⟨16498015670730315950637941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10998677113820210633758627 16498015670730315950637941)
                    ·
                      refine ⟨1546688969130967120372307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16498015670730315950637941 1546688969130967120372307)
                      ·
                        rfl

theorem cell23_3012166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3012166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012166 prefixEnd_3012166 := by exact prefixLift 3012166
  have htrace : WordTrace (prefixWord ++ tailWord_3012166) baseStart_3012166 baseEnd_3012166 := by
    simpa [prefixWord, tailWord_3012166, baseEnd_3012166] using wordTrace_append hprefix tailTrace_3012166
  have hstable : (prefixWord ++ tailWord_3012166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012166).length < 2 ^ (prefixWord ++ tailWord_3012166).sum := by decide
  have hdescent : baseEnd_3012166 < baseStart_3012166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012175 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_3012175 : Nat := 118140960795 + 3012175 * 2 ^ 59
def prefixEnd_3012175 : Nat := 4983230072969 + 3 ^ 40 * 3012175 * 2
def baseEnd_3012175 : Nat := 1546693590456857585159765

theorem tailTrace_3012175 : CollatzResearch.WordTrace tailWord_3012175 prefixEnd_3012175 1546693590456857585159765 := by
  unfold tailWord_3012175
  simp only [CollatzResearch.WordTrace]
  refine ⟨109863047862411888378565979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73242031908274592252377319 109863047862411888378565979)
  ·
    refine ⟨164794571793617832567848969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109863047862411888378565979 164794571793617832567848969)
    ·
      refine ⟨123595928845213374425886727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164794571793617832567848969 123595928845213374425886727)
      ·
        refine ⟨185393893267820061638830091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123595928845213374425886727 185393893267820061638830091)
        ·
          refine ⟨278090839901730092458245137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185393893267820061638830091 278090839901730092458245137)
          ·
            refine ⟨208568129926297569343683853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278090839901730092458245137 208568129926297569343683853)
            ·
              refine ⟨78213048722361588503881445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208568129926297569343683853 78213048722361588503881445)
              ·
                refine ⟨14664946635442797844477771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78213048722361588503881445 14664946635442797844477771)
                ·
                  refine ⟨21997419953164196766716657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14664946635442797844477771 21997419953164196766716657)
                  ·
                    refine ⟨16498064964873147575037493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21997419953164196766716657 16498064964873147575037493)
                    ·
                      refine ⟨1546693590456857585159765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16498064964873147575037493 1546693590456857585159765)
                      ·
                        rfl

theorem cell23_3012175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_3012175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012175 prefixEnd_3012175 := by exact prefixLift 3012175
  have htrace : WordTrace (prefixWord ++ tailWord_3012175) baseStart_3012175 baseEnd_3012175 := by
    simpa [prefixWord, tailWord_3012175, baseEnd_3012175] using wordTrace_append hprefix tailTrace_3012175
  have hstable : (prefixWord ++ tailWord_3012175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012175).length < 2 ^ (prefixWord ++ tailWord_3012175).sum := by decide
  have hdescent : baseEnd_3012175 < baseStart_3012175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012215 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_3012215 : Nat := 118140960795 + 3012215 * 2 ^ 59
def prefixEnd_3012215 : Nat := 4983230072969 + 3 ^ 40 * 3012215 * 2
def baseEnd_3012215 : Nat := 1546714129683037428659581

theorem tailTrace_3012215 : CollatzResearch.WordTrace tailWord_3012215 prefixEnd_3012215 1546714129683037428659581 := by
  unfold tailWord_3012215
  simp only [CollatzResearch.WordTrace]
  refine ⟨109864506782266975210022099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73243004521511316806681399 109864506782266975210022099)
  ·
    refine ⟨164796760173400462815033149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109864506782266975210022099 164796760173400462815033149)
    ·
      refine ⟨61798785065025173555637431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164796760173400462815033149 61798785065025173555637431)
      ·
        refine ⟨92698177597537760333456147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61798785065025173555637431 92698177597537760333456147)
        ·
          refine ⟨139047266396306640500184221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92698177597537760333456147 139047266396306640500184221)
          ·
            refine ⟨52142724898614990187569083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139047266396306640500184221 52142724898614990187569083)
            ·
              refine ⟨78214087347922485281353625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52142724898614990187569083 78214087347922485281353625)
              ·
                refine ⟨58660565510941863961015219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78214087347922485281353625 58660565510941863961015219)
                ·
                  refine ⟨87990848266412795941522829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58660565510941863961015219 87990848266412795941522829)
                  ·
                    refine ⟨32996568099904798478071061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87990848266412795941522829 32996568099904798478071061)
                    ·
                      refine ⟨1546714129683037428659581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32996568099904798478071061 1546714129683037428659581)
                      ·
                        rfl

theorem cell23_3012215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_3012215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012215 prefixEnd_3012215 := by exact prefixLift 3012215
  have htrace : WordTrace (prefixWord ++ tailWord_3012215) baseStart_3012215 baseEnd_3012215 := by
    simpa [prefixWord, tailWord_3012215, baseEnd_3012215] using wordTrace_append hprefix tailTrace_3012215
  have hstable : (prefixWord ++ tailWord_3012215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012215).length < 2 ^ (prefixWord ++ tailWord_3012215).sum := by decide
  have hdescent : baseEnd_3012215 < baseStart_3012215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012270 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3012270 : Nat := 118140960795 + 3012270 * 2 ^ 59
def prefixEnd_3012270 : Nat := 4983230072969 + 3 ^ 40 * 3012270 * 2
def baseEnd_3012270 : Nat := 1546742371119034713471829

theorem tailTrace_3012270 : CollatzResearch.WordTrace tailWord_3012270 prefixEnd_3012270 1546742371119034713471829 := by
  unfold tailWord_3012270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733314099633464950409283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73244341864711813068849509 13733314099633464950409283)
  ·
    refine ⟨20599971149450197425613925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13733314099633464950409283 20599971149450197425613925)
    ·
      refine ⟨3862494590521912017302611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20599971149450197425613925 3862494590521912017302611)
      ·
        refine ⟨5793741885782868025953917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862494590521912017302611 5793741885782868025953917)
        ·
          refine ⟨2172653207168575509732719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5793741885782868025953917 2172653207168575509732719)
          ·
            refine ⟨3258979810752863264599079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172653207168575509732719 3258979810752863264599079)
            ·
              refine ⟨4888469716129294896898619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258979810752863264599079 4888469716129294896898619)
              ·
                refine ⟨7332704574193942345347929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888469716129294896898619 7332704574193942345347929)
                ·
                  refine ⟨5499528430645456759010947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7332704574193942345347929 5499528430645456759010947)
                  ·
                    refine ⟨8249292645968185138516421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5499528430645456759010947 8249292645968185138516421)
                    ·
                      refine ⟨1546742371119034713471829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8249292645968185138516421 1546742371119034713471829)
                      ·
                        rfl

theorem cell23_3012270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3012270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012270 prefixEnd_3012270 := by exact prefixLift 3012270
  have htrace : WordTrace (prefixWord ++ tailWord_3012270) baseStart_3012270 baseEnd_3012270 := by
    simpa [prefixWord, tailWord_3012270, baseEnd_3012270] using wordTrace_append hprefix tailTrace_3012270
  have hstable : (prefixWord ++ tailWord_3012270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012270).length < 2 ^ (prefixWord ++ tailWord_3012270).sum := by decide
  have hdescent : baseEnd_3012270 < baseStart_3012270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012272 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_3012272 : Nat := 118140960795 + 3012272 * 2 ^ 59
def prefixEnd_3012272 : Nat := 4983230072969 + 3 ^ 40 * 3012272 * 2
def baseEnd_3012272 : Nat := 515581132693447901882273

theorem tailTrace_3012272 : CollatzResearch.WordTrace tailWord_3012272 prefixEnd_3012272 515581132693447901882273 := by
  unfold tailWord_3012272
  simp only [CollatzResearch.WordTrace]
  refine ⟨54933292871530236972423535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73244390495373649296564713 54933292871530236972423535)
  ·
    refine ⟨82399939307295355458635303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54933292871530236972423535 82399939307295355458635303)
    ·
      refine ⟨123599908960943033187952955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82399939307295355458635303 123599908960943033187952955)
      ·
        refine ⟨185399863441414549781929433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123599908960943033187952955 185399863441414549781929433)
        ·
          refine ⟨139049897581060912336447075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185399863441414549781929433 139049897581060912336447075)
          ·
            refine ⟨208574846371591368504670613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139049897581060912336447075 208574846371591368504670613)
            ·
              refine ⟨9776945923668345398656435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208574846371591368504670613 9776945923668345398656435)
              ·
                refine ⟨14665418885502518097984653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9776945923668345398656435 14665418885502518097984653)
                ·
                  refine ⟨5499532082063444286744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14665418885502518097984653 5499532082063444286744245)
                  ·
                    refine ⟨515581132693447901882273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5499532082063444286744245 515581132693447901882273)
                    ·
                      rfl

theorem cell23_3012272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_3012272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012272 prefixEnd_3012272 := by exact prefixLift 3012272
  have htrace : WordTrace (prefixWord ++ tailWord_3012272) baseStart_3012272 baseEnd_3012272 := by
    simpa [prefixWord, tailWord_3012272, baseEnd_3012272] using wordTrace_append hprefix tailTrace_3012272
  have hstable : (prefixWord ++ tailWord_3012272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012272).length < 2 ^ (prefixWord ++ tailWord_3012272).sum := by decide
  have hdescent : baseEnd_3012272 < baseStart_3012272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012310 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3012310 : Nat := 118140960795 + 3012310 * 2 ^ 59
def prefixEnd_3012310 : Nat := 4983230072969 + 3 ^ 40 * 3012310 * 2
def baseEnd_3012310 : Nat := 171862545593912728552405

theorem tailTrace_3012310 : CollatzResearch.WordTrace tailWord_3012310 prefixEnd_3012310 171862545593912728552405 := by
  unfold tailWord_3012310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866748232307675402170649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73245314477948537623153589 6866748232307675402170649)
  ·
    refine ⟨5150061174230756551627987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6866748232307675402170649 5150061174230756551627987)
    ·
      refine ⟨7725091761346134827441981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150061174230756551627987 7725091761346134827441981)
      ·
        refine ⟨2896909410504800560290743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7725091761346134827441981 2896909410504800560290743)
        ·
          refine ⟨4345364115757200840436115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896909410504800560290743 4345364115757200840436115)
          ·
            refine ⟨6518046173635801260654173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345364115757200840436115 6518046173635801260654173)
            ·
              refine ⟨2444267315113425472745315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6518046173635801260654173 2444267315113425472745315)
              ·
                refine ⟨3666400972670138209117973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444267315113425472745315 3666400972670138209117973)
                ·
                  refine ⟨171862545593912728552405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3666400972670138209117973 171862545593912728552405)
                  ·
                    rfl

theorem cell23_3012310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3012310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012310 prefixEnd_3012310 := by exact prefixLift 3012310
  have htrace : WordTrace (prefixWord ++ tailWord_3012310) baseStart_3012310 baseEnd_3012310 := by
    simpa [prefixWord, tailWord_3012310, baseEnd_3012310] using wordTrace_append hprefix tailTrace_3012310
  have hstable : (prefixWord ++ tailWord_3012310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012310).length < 2 ^ (prefixWord ++ tailWord_3012310).sum := by decide
  have hdescent : baseEnd_3012310 < baseStart_3012310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012369 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 7, 2]
def baseStart_3012369 : Nat := 118140960795 + 3012369 * 2 ^ 59
def prefixEnd_3012369 : Nat := 4983230072969 + 3 ^ 40 * 3012369 * 2
def baseEnd_3012369 : Nat := 1546793205703829826133873

theorem tailTrace_3012369 : CollatzResearch.WordTrace tailWord_3012369 prefixEnd_3012369 1546793205703829826133873 := by
  unfold tailWord_3012369
  simp only [CollatzResearch.WordTrace]
  refine ⟨109870123623709059511128161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73246749082472706340752107 109870123623709059511128161)
  ·
    refine ⟨82402592717781794633346121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109870123623709059511128161 82402592717781794633346121)
    ·
      refine ⟨61801944538336345975009591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82402592717781794633346121 61801944538336345975009591)
      ·
        refine ⟨92702916807504518962514387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61801944538336345975009591 92702916807504518962514387)
        ·
          refine ⟨139054375211256778443771581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92702916807504518962514387 139054375211256778443771581)
          ·
            refine ⟨52145390704221291916414343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139054375211256778443771581 52145390704221291916414343)
            ·
              refine ⟨78218086056331937874621515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52145390704221291916414343 78218086056331937874621515)
              ·
                refine ⟨117327129084497906811932273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78218086056331937874621515 117327129084497906811932273)
                ·
                  refine ⟨87995346813373430108949205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117327129084497906811932273 87995346813373430108949205)
                  ·
                    refine ⟨2062390940938439768178497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 87995346813373430108949205 2062390940938439768178497)
                    ·
                      refine ⟨1546793205703829826133873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062390940938439768178497 1546793205703829826133873)
                      ·
                        rfl

theorem cell23_3012369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_3012369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012369 prefixEnd_3012369 := by exact prefixLift 3012369
  have htrace : WordTrace (prefixWord ++ tailWord_3012369) baseStart_3012369 baseEnd_3012369 := by
    simpa [prefixWord, tailWord_3012369, baseEnd_3012369] using wordTrace_append hprefix tailTrace_3012369
  have hstable : (prefixWord ++ tailWord_3012369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012369).length < 2 ^ (prefixWord ++ tailWord_3012369).sum := by decide
  have hdescent : baseEnd_3012369 < baseStart_3012369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012370 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3012370 : Nat := 118140960795 + 3012370 * 2 ^ 59
def prefixEnd_3012370 : Nat := 4983230072969 + 3 ^ 40 * 3012370 * 2
def baseEnd_3012370 : Nat := 515597906394828107407123

theorem tailTrace_3012370 : CollatzResearch.WordTrace tailWord_3012370 prefixEnd_3012370 515597906394828107407123 := by
  unfold tailWord_3012370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27467540024176359170478641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73246773397803624454609709 27467540024176359170478641)
  ·
    refine ⟨20600655018132269377858981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27467540024176359170478641 20600655018132269377858981)
    ·
      refine ⟨3862622815899800508348559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20600655018132269377858981 3862622815899800508348559)
      ·
        refine ⟨5793934223849700762522839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862622815899800508348559 5793934223849700762522839)
        ·
          refine ⟨8690901335774551143784259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793934223849700762522839 8690901335774551143784259)
          ·
            refine ⟨13036352003661826715676389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690901335774551143784259 13036352003661826715676389)
            ·
              refine ⟨2444316000686592509189323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13036352003661826715676389 2444316000686592509189323)
              ·
                refine ⟨3666474001029888763783985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444316000686592509189323 3666474001029888763783985)
                ·
                  refine ⟨2749855500772416572837989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3666474001029888763783985 2749855500772416572837989)
                  ·
                    refine ⟨515597906394828107407123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2749855500772416572837989 515597906394828107407123)
                    ·
                      rfl

theorem cell23_3012370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3012370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012370 prefixEnd_3012370 := by exact prefixLift 3012370
  have htrace : WordTrace (prefixWord ++ tailWord_3012370) baseStart_3012370 baseEnd_3012370 := by
    simpa [prefixWord, tailWord_3012370, baseEnd_3012370] using wordTrace_append hprefix tailTrace_3012370
  have hstable : (prefixWord ++ tailWord_3012370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012370).length < 2 ^ (prefixWord ++ tailWord_3012370).sum := by decide
  have hdescent : baseEnd_3012370 < baseStart_3012370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012419 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 3]
def baseStart_3012419 : Nat := 118140960795 + 3012419 * 2 ^ 59
def prefixEnd_3012419 : Nat := 4983230072969 + 3 ^ 40 * 3012419 * 2
def baseEnd_3012419 : Nat := 1546818879736554630508643

theorem tailTrace_3012419 : CollatzResearch.WordTrace tailWord_3012419 prefixEnd_3012419 1546818879736554630508643 := by
  unfold tailWord_3012419
  simp only [CollatzResearch.WordTrace]
  refine ⟨109871947273527918050448311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73247964849018612033632207 109871947273527918050448311)
  ·
    refine ⟨164807920910291877075672467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109871947273527918050448311 164807920910291877075672467)
    ·
      refine ⟨247211881365437815613508701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164807920910291877075672467 247211881365437815613508701)
      ·
        refine ⟨92704455512039180855065763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247211881365437815613508701 92704455512039180855065763)
        ·
          refine ⟨139056683268058771282598645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92704455512039180855065763 139056683268058771282598645)
          ·
            refine ⟨13036564056380509807743623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139056683268058771282598645 13036564056380509807743623)
            ·
              refine ⟨19554846084570764711615435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13036564056380509807743623 19554846084570764711615435)
              ·
                refine ⟨29332269126856147067423153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19554846084570764711615435 29332269126856147067423153)
                ·
                  refine ⟨21999201845142110300567365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29332269126856147067423153 21999201845142110300567365)
                  ·
                    refine ⟨4124850345964145681356381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21999201845142110300567365 4124850345964145681356381)
                    ·
                      refine ⟨1546818879736554630508643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4124850345964145681356381 1546818879736554630508643)
                      ·
                        rfl

theorem cell23_3012419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_3012419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012419 prefixEnd_3012419 := by exact prefixLift 3012419
  have htrace : WordTrace (prefixWord ++ tailWord_3012419) baseStart_3012419 baseEnd_3012419 := by
    simpa [prefixWord, tailWord_3012419, baseEnd_3012419] using wordTrace_append hprefix tailTrace_3012419
  have hstable : (prefixWord ++ tailWord_3012419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012419).length < 2 ^ (prefixWord ++ tailWord_3012419).sum := by decide
  have hdescent : baseEnd_3012419 < baseStart_3012419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012433 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 1, 4, 2]
def baseStart_3012433 : Nat := 118140960795 + 3012433 * 2 ^ 59
def prefixEnd_3012433 : Nat := 4983230072969 + 3 ^ 40 * 3012433 * 2
def baseEnd_3012433 : Nat := 1546826068465717575733579

theorem tailTrace_3012433 : CollatzResearch.WordTrace tailWord_3012433 prefixEnd_3012433 1546826068465717575733579 := by
  unfold tailWord_3012433
  simp only [CollatzResearch.WordTrace]
  refine ⟨109872457895477198441457953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73248305263651465627638635 109872457895477198441457953)
  ·
    refine ⟨82404343421607898831093465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109872457895477198441457953 82404343421607898831093465)
    ·
      refine ⟨61803257566205924123320099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82404343421607898831093465 61803257566205924123320099)
      ·
        refine ⟨92704886349308886184980149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61803257566205924123320099 92704886349308886184980149)
        ·
          refine ⟨8691083095247708079841889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92704886349308886184980149 8691083095247708079841889)
          ·
            refine ⟨6518312321435781059881417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8691083095247708079841889 6518312321435781059881417)
            ·
              refine ⟨4888734241076835794911063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518312321435781059881417 4888734241076835794911063)
              ·
                refine ⟨7333101361615253692366595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888734241076835794911063 7333101361615253692366595)
                ·
                  refine ⟨10999652042422880538549893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7333101361615253692366595 10999652042422880538549893)
                  ·
                    refine ⟨2062434757954290100978105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10999652042422880538549893 2062434757954290100978105)
                    ·
                      refine ⟨1546826068465717575733579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062434757954290100978105 1546826068465717575733579)
                      ·
                        rfl

theorem cell23_3012433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_3012433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012433 prefixEnd_3012433 := by exact prefixLift 3012433
  have htrace : WordTrace (prefixWord ++ tailWord_3012433) baseStart_3012433 baseEnd_3012433 := by
    simpa [prefixWord, tailWord_3012433, baseEnd_3012433] using wordTrace_append hprefix tailTrace_3012433
  have hstable : (prefixWord ++ tailWord_3012433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012433).length < 2 ^ (prefixWord ++ tailWord_3012433).sum := by decide
  have hdescent : baseEnd_3012433 < baseStart_3012433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012449 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_3012449 : Nat := 118140960795 + 3012449 * 2 ^ 59
def prefixEnd_3012449 : Nat := 4983230072969 + 3 ^ 40 * 3012449 * 2
def baseEnd_3012449 : Nat := 1546834284156189513133505

theorem tailTrace_3012449 : CollatzResearch.WordTrace tailWord_3012449 prefixEnd_3012449 1546834284156189513133505 := by
  unfold tailWord_3012449
  simp only [CollatzResearch.WordTrace]
  refine ⟨109873041463419233174040401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73248694308946155449360267 109873041463419233174040401)
  ·
    refine ⟨82404781097564424880530301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109873041463419233174040401 82404781097564424880530301)
    ·
      refine ⟨30901792911586659330198863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82404781097564424880530301 30901792911586659330198863)
      ·
        refine ⟨46352689367379988995298295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30901792911586659330198863 46352689367379988995298295)
        ·
          refine ⟨69529034051069983492947443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46352689367379988995298295 69529034051069983492947443)
          ·
            refine ⟨104293551076604975239421165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69529034051069983492947443 104293551076604975239421165)
            ·
              refine ⟨39110081653726865714782937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104293551076604975239421165 39110081653726865714782937)
              ·
                refine ⟨29332561240295149286087203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39110081653726865714782937 29332561240295149286087203)
                ·
                  refine ⟨43998841860442723929130805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29332561240295149286087203 43998841860442723929130805)
                  ·
                    refine ⟨4124891424416505368356013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43998841860442723929130805 4124891424416505368356013)
                    ·
                      refine ⟨1546834284156189513133505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4124891424416505368356013 1546834284156189513133505)
                      ·
                        rfl

theorem cell23_3012449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_3012449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012449 prefixEnd_3012449 := by exact prefixLift 3012449
  have htrace : WordTrace (prefixWord ++ tailWord_3012449) baseStart_3012449 baseEnd_3012449 := by
    simpa [prefixWord, tailWord_3012449, baseEnd_3012449] using wordTrace_append hprefix tailTrace_3012449
  have hstable : (prefixWord ++ tailWord_3012449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012449).length < 2 ^ (prefixWord ++ tailWord_3012449).sum := by decide
  have hdescent : baseEnd_3012449 < baseStart_3012449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012489 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_3012489 : Nat := 118140960795 + 3012489 * 2 ^ 59
def prefixEnd_3012489 : Nat := 4983230072969 + 3 ^ 40 * 3012489 * 2
def baseEnd_3012489 : Nat := 1546854823382369356633321

theorem tailTrace_3012489 : CollatzResearch.WordTrace tailWord_3012489 prefixEnd_3012489 1546854823382369356633321 := by
  unfold tailWord_3012489
  simp only [CollatzResearch.WordTrace]
  refine ⟨109874500383274320005496521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73249666922182880003664347 109874500383274320005496521)
  ·
    refine ⟨82405875287455740004122391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109874500383274320005496521 82405875287455740004122391)
    ·
      refine ⟨123608812931183610006183587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82405875287455740004122391 123608812931183610006183587)
      ·
        refine ⟨185413219396775415009275381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123608812931183610006183587 185413219396775415009275381)
        ·
          refine ⟨17382489318447695157119567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185413219396775415009275381 17382489318447695157119567)
          ·
            refine ⟨26073733977671542735679351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17382489318447695157119567 26073733977671542735679351)
            ·
              refine ⟨39110600966507314103519027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26073733977671542735679351 39110600966507314103519027)
              ·
                refine ⟨58665901449760971155278541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39110600966507314103519027 58665901449760971155278541)
                ·
                  refine ⟨21999713043660364183229453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58665901449760971155278541 21999713043660364183229453)
                  ·
                    refine ⟨8249892391372636568711045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21999713043660364183229453 8249892391372636568711045)
                    ·
                      refine ⟨1546854823382369356633321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8249892391372636568711045 1546854823382369356633321)
                      ·
                        rfl

theorem cell23_3012489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_3012489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012489 prefixEnd_3012489 := by exact prefixLift 3012489
  have htrace : WordTrace (prefixWord ++ tailWord_3012489) baseStart_3012489 baseEnd_3012489 := by
    simpa [prefixWord, tailWord_3012489, baseEnd_3012489] using wordTrace_append hprefix tailTrace_3012489
  have hstable : (prefixWord ++ tailWord_3012489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012489).length < 2 ^ (prefixWord ++ tailWord_3012489).sum := by decide
  have hdescent : baseEnd_3012489 < baseStart_3012489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012506 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3012506 : Nat := 118140960795 + 3012506 * 2 ^ 59
def prefixEnd_3012506 : Nat := 4983230072969 + 3 ^ 40 * 3012506 * 2
def baseEnd_3012506 : Nat := 1546863552553495790120743

theorem tailTrace_3012506 : CollatzResearch.WordTrace tailWord_3012506 prefixEnd_3012506 1546863552553495790120743 := by
  unfold tailWord_3012506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27468780106053182977216343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73250080282808487939243581 27468780106053182977216343)
  ·
    refine ⟨41203170159079774465824515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27468780106053182977216343 41203170159079774465824515)
    ·
      refine ⟨61804755238619661698736773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41203170159079774465824515 61804755238619661698736773)
      ·
        refine ⟨11588391607241186568513145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61804755238619661698736773 11588391607241186568513145)
        ·
          refine ⟨8691293705430889926384859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11588391607241186568513145 8691293705430889926384859)
          ·
            refine ⟨13036940558146334889577289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691293705430889926384859 13036940558146334889577289)
            ·
              refine ⟨9777705418609751167182967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13036940558146334889577289 9777705418609751167182967)
              ·
                refine ⟨14666558127914626750774451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9777705418609751167182967 14666558127914626750774451)
                ·
                  refine ⟨21999837191871940126161677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14666558127914626750774451 21999837191871940126161677)
                  ·
                    refine ⟨8249938946951977547310629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21999837191871940126161677 8249938946951977547310629)
                    ·
                      refine ⟨1546863552553495790120743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8249938946951977547310629 1546863552553495790120743)
                      ·
                        rfl

theorem cell23_3012506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3012506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012506 prefixEnd_3012506 := by exact prefixLift 3012506
  have htrace : WordTrace (prefixWord ++ tailWord_3012506) baseStart_3012506 baseEnd_3012506 := by
    simpa [prefixWord, tailWord_3012506, baseEnd_3012506] using wordTrace_append hprefix tailTrace_3012506
  have hstable : (prefixWord ++ tailWord_3012506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012506).length < 2 ^ (prefixWord ++ tailWord_3012506).sum := by decide
  have hdescent : baseEnd_3012506 < baseStart_3012506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012520 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3012520 : Nat := 118140960795 + 3012520 * 2 ^ 59
def prefixEnd_3012520 : Nat := 4983230072969 + 3 ^ 40 * 3012520 * 2
def baseEnd_3012520 : Nat := 515623580427552911781893

theorem tailTrace_3012520 : CollatzResearch.WordTrace tailWord_3012520 prefixEnd_3012520 515623580427552911781893 := by
  unfold tailWord_3012520
  simp only [CollatzResearch.WordTrace]
  refine ⟨54937815523081006149937507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73250420697441341533250009 54937815523081006149937507)
  ·
    refine ⟨82406723284621509224906261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54937815523081006149937507 82406723284621509224906261)
    ·
      refine ⟨3862815153966633244917481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82406723284621509224906261 3862815153966633244917481)
      ·
        refine ⟨2897111365474974933688111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3862815153966633244917481 2897111365474974933688111)
        ·
          refine ⟨4345667048212462400532167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897111365474974933688111 4345667048212462400532167)
          ·
            refine ⟨6518500572318693600798251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345667048212462400532167 6518500572318693600798251)
            ·
              refine ⟨9777750858478040401197377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518500572318693600798251 9777750858478040401197377)
              ·
                refine ⟨7333313143858530300898033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9777750858478040401197377 7333313143858530300898033)
                ·
                  refine ⟨5499984857893897725673525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7333313143858530300898033 5499984857893897725673525)
                  ·
                    refine ⟨515623580427552911781893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5499984857893897725673525 515623580427552911781893)
                    ·
                      rfl

theorem cell23_3012520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3012520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012520 prefixEnd_3012520 := by exact prefixLift 3012520
  have htrace : WordTrace (prefixWord ++ tailWord_3012520) baseStart_3012520 baseEnd_3012520 := by
    simpa [prefixWord, tailWord_3012520, baseEnd_3012520] using wordTrace_append hprefix tailTrace_3012520
  have hstable : (prefixWord ++ tailWord_3012520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012520).length < 2 ^ (prefixWord ++ tailWord_3012520).sum := by decide
  have hdescent : baseEnd_3012520 < baseStart_3012520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012533 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_3012533 : Nat := 118140960795 + 3012533 * 2 ^ 59
def prefixEnd_3012533 : Nat := 4983230072969 + 3 ^ 40 * 3012533 * 2
def baseEnd_3012533 : Nat := 515625805510389061494373

theorem tailTrace_3012533 : CollatzResearch.WordTrace tailWord_3012533 prefixEnd_3012533 515625805510389061494373 := by
  unfold tailWord_3012533
  simp only [CollatzResearch.WordTrace]
  refine ⟨109876105195114915520098253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73250736796743277013398835 109876105195114915520098253)
  ·
    refine ⟨41203539448168093320036845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109876105195114915520098253 41203539448168093320036845)
    ·
      refine ⟨15451327293063034995013817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41203539448168093320036845 15451327293063034995013817)
      ·
        refine ⟨11588495469797276246260363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15451327293063034995013817 11588495469797276246260363)
        ·
          refine ⟨17382743204695914369390545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11588495469797276246260363 17382743204695914369390545)
          ·
            refine ⟨13037057403521935777042909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17382743204695914369390545 13037057403521935777042909)
            ·
              refine ⟨4888896526320725916391091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13037057403521935777042909 4888896526320725916391091)
              ·
                refine ⟨7333344789481088874586637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888896526320725916391091 7333344789481088874586637)
                ·
                  refine ⟨2750004296055408327969989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7333344789481088874586637 2750004296055408327969989)
                  ·
                    refine ⟨515625805510389061494373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750004296055408327969989 515625805510389061494373)
                    ·
                      rfl

theorem cell23_3012533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_3012533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012533 prefixEnd_3012533 := by exact prefixLift 3012533
  have htrace : WordTrace (prefixWord ++ tailWord_3012533) baseStart_3012533 baseEnd_3012533 := by
    simpa [prefixWord, tailWord_3012533, baseEnd_3012533] using wordTrace_append hprefix tailTrace_3012533
  have hstable : (prefixWord ++ tailWord_3012533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012533).length < 2 ^ (prefixWord ++ tailWord_3012533).sum := by decide
  have hdescent : baseEnd_3012533 < baseStart_3012533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012576 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 1, 5]
def baseStart_3012576 : Nat := 118140960795 + 3012576 * 2 ^ 59
def prefixEnd_3012576 : Nat := 4983230072969 + 3 ^ 40 * 3012576 * 2
def baseEnd_3012576 : Nat := 515633165399770172081807

theorem tailTrace_3012576 : CollatzResearch.WordTrace tailWord_3012576 prefixEnd_3012576 515633165399770172081807 := by
  unfold tailWord_3012576
  simp only [CollatzResearch.WordTrace]
  refine ⟨54938836766979566931956791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73251782355972755909275721 54938836766979566931956791)
  ·
    refine ⟨82408255150469350397935187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54938836766979566931956791 82408255150469350397935187)
    ·
      refine ⟨123612382725704025596902781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82408255150469350397935187 123612382725704025596902781)
      ·
        refine ⟨46354643522139009598838543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123612382725704025596902781 46354643522139009598838543)
        ·
          refine ⟨69531965283208514398257815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46354643522139009598838543 69531965283208514398257815)
          ·
            refine ⟨104297947924812771597386723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69531965283208514398257815 104297947924812771597386723)
            ·
              refine ⟨156446921887219157396080085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104297947924812771597386723 156446921887219157396080085)
              ·
                refine ⟨3666724731731699001470627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 156446921887219157396080085 3666724731731699001470627)
                ·
                  refine ⟨5500087097597548502205941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666724731731699001470627 5500087097597548502205941)
                  ·
                    refine ⟨515633165399770172081807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5500087097597548502205941 515633165399770172081807)
                    ·
                      rfl

theorem cell23_3012576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_3012576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012576 prefixEnd_3012576 := by exact prefixLift 3012576
  have htrace : WordTrace (prefixWord ++ tailWord_3012576) baseStart_3012576 baseEnd_3012576 := by
    simpa [prefixWord, tailWord_3012576, baseEnd_3012576] using wordTrace_append hprefix tailTrace_3012576
  have hstable : (prefixWord ++ tailWord_3012576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012576).length < 2 ^ (prefixWord ++ tailWord_3012576).sum := by decide
  have hdescent : baseEnd_3012576 < baseStart_3012576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012636 : List Nat := [2, 2, 3, 1, 3, 2, 10]
def baseStart_3012636 : Nat := 118140960795 + 3012636 * 2 ^ 59
def prefixEnd_3012636 : Nat := 4983230072969 + 3 ^ 40 * 3012636 * 2
def baseEnd_3012636 : Nat := 19097905000476299771545

theorem tailTrace_3012636 : CollatzResearch.WordTrace tailWord_3012636 prefixEnd_3012636 19097905000476299771545 := by
  unfold tailWord_3012636
  simp only [CollatzResearch.WordTrace]
  refine ⟨54939930956870882055548881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73253241275827842740731841 54939930956870882055548881)
  ·
    refine ⟨41204948217653161541661661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54939930956870882055548881 41204948217653161541661661)
    ·
      refine ⟨15451855581619935578123123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41204948217653161541661661 15451855581619935578123123)
      ·
        refine ⟨23177783372429903367184685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15451855581619935578123123 23177783372429903367184685)
        ·
          refine ⟨8691668764661213762694257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23177783372429903367184685 8691668764661213762694257)
          ·
            refine ⟨6518751573495910322020693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8691668764661213762694257 6518751573495910322020693)
            ·
              refine ⟨19097905000476299771545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6518751573495910322020693 19097905000476299771545)
              ·
                rfl

theorem cell23_3012636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 10].length) (baseStart_3012636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012636 prefixEnd_3012636 := by exact prefixLift 3012636
  have htrace : WordTrace (prefixWord ++ tailWord_3012636) baseStart_3012636 baseEnd_3012636 := by
    simpa [prefixWord, tailWord_3012636, baseEnd_3012636] using wordTrace_append hprefix tailTrace_3012636
  have hstable : (prefixWord ++ tailWord_3012636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012636).length < 2 ^ (prefixWord ++ tailWord_3012636).sum := by decide
  have hdescent : baseEnd_3012636 < baseStart_3012636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012660 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3012660 : Nat := 118140960795 + 3012660 * 2 ^ 59
def prefixEnd_3012660 : Nat := 4983230072969 + 3 ^ 40 * 3012660 * 2
def baseEnd_3012660 : Nat := 1546942628574288187595035

theorem tailTrace_3012660 : CollatzResearch.WordTrace tailWord_3012660 prefixEnd_3012660 1546942628574288187595035 := by
  unfold tailWord_3012660
  simp only [CollatzResearch.WordTrace]
  refine ⟨54940368632827408104985717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73253824843769877473314289 54940368632827408104985717)
  ·
    refine ⟨5150659559327569509842411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54940368632827408104985717 5150659559327569509842411)
    ·
      refine ⟨7725989338991354264763617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150659559327569509842411 7725989338991354264763617)
      ·
        refine ⟨5794492004243515698572713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7725989338991354264763617 5794492004243515698572713)
        ·
          refine ⟨4345869003182636773929535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794492004243515698572713 4345869003182636773929535)
          ·
            refine ⟨6518803504773955160894303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345869003182636773929535 6518803504773955160894303)
            ·
              refine ⟨9778205257160932741341455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518803504773955160894303 9778205257160932741341455)
              ·
                refine ⟨14667307885741399112012183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9778205257160932741341455 14667307885741399112012183)
                ·
                  refine ⟨22000961828612098668018275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14667307885741399112012183 22000961828612098668018275)
                  ·
                    refine ⟨33001442742918148002027413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22000961828612098668018275 33001442742918148002027413)
                    ·
                      refine ⟨1546942628574288187595035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33001442742918148002027413 1546942628574288187595035)
                      ·
                        rfl

theorem cell23_3012660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3012660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012660 prefixEnd_3012660 := by exact prefixLift 3012660
  have htrace : WordTrace (prefixWord ++ tailWord_3012660) baseStart_3012660 baseEnd_3012660 := by
    simpa [prefixWord, tailWord_3012660, baseEnd_3012660] using wordTrace_append hprefix tailTrace_3012660
  have hstable : (prefixWord ++ tailWord_3012660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012660).length < 2 ^ (prefixWord ++ tailWord_3012660).sum := by decide
  have hdescent : baseEnd_3012660 < baseStart_3012660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012663 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_3012663 : Nat := 118140960795 + 3012663 * 2 ^ 59
def prefixEnd_3012663 : Nat := 4983230072969 + 3 ^ 40 * 3012663 * 2
def baseEnd_3012663 : Nat := 1546944169016251675857521

theorem tailTrace_3012663 : CollatzResearch.WordTrace tailWord_3012663 prefixEnd_3012663 1546944169016251675857521 := by
  unfold tailWord_3012663
  simp only [CollatzResearch.WordTrace]
  refine ⟨109880846684643947722330643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73253897789762631814887095 109880846684643947722330643)
  ·
    refine ⟨164821270026965921583495965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109880846684643947722330643 164821270026965921583495965)
    ·
      refine ⟨61807976260112220593810987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164821270026965921583495965 61807976260112220593810987)
      ·
        refine ⟨92711964390168330890716481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61807976260112220593810987 92711964390168330890716481)
        ·
          refine ⟨69533973292626248168037361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92711964390168330890716481 69533973292626248168037361)
          ·
            refine ⟨52150479969469686126028021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69533973292626248168037361 52150479969469686126028021)
            ·
              refine ⟨4889107497137783074315127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52150479969469686126028021 4889107497137783074315127)
              ·
                refine ⟨7333661245706674611472691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889107497137783074315127 7333661245706674611472691)
                ·
                  refine ⟨11000491868560011917209037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7333661245706674611472691 11000491868560011917209037)
                  ·
                    refine ⟨4125184450710004468953389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11000491868560011917209037 4125184450710004468953389)
                    ·
                      refine ⟨1546944169016251675857521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125184450710004468953389 1546944169016251675857521)
                      ·
                        rfl

theorem cell23_3012663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_3012663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012663 prefixEnd_3012663 := by exact prefixLift 3012663
  have htrace : WordTrace (prefixWord ++ tailWord_3012663) baseStart_3012663 baseEnd_3012663 := by
    simpa [prefixWord, tailWord_3012663, baseEnd_3012663] using wordTrace_append hprefix tailTrace_3012663
  have hstable : (prefixWord ++ tailWord_3012663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012663).length < 2 ^ (prefixWord ++ tailWord_3012663).sum := by decide
  have hdescent : baseEnd_3012663 < baseStart_3012663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012703 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 5, 4, 2]
def baseStart_3012703 : Nat := 118140960795 + 3012703 * 2 ^ 59
def prefixEnd_3012703 : Nat := 4983230072969 + 3 ^ 40 * 3012703 * 2
def baseEnd_3012703 : Nat := 1546964708242431519357337

theorem tailTrace_3012703 : CollatzResearch.WordTrace tailWord_3012703 prefixEnd_3012703 1546964708242431519357337 := by
  unfold tailWord_3012703
  simp only [CollatzResearch.WordTrace]
  refine ⟨109882305604499034553786763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73254870402999356369191175 109882305604499034553786763)
  ·
    refine ⟨164823458406748551830680145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109882305604499034553786763 164823458406748551830680145)
    ·
      refine ⟨123617593805061413873010109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164823458406748551830680145 123617593805061413873010109)
      ·
        refine ⟨46356597676898030202378791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123617593805061413873010109 46356597676898030202378791)
        ·
          refine ⟨69534896515347045303568187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46356597676898030202378791 69534896515347045303568187)
          ·
            refine ⟨104302344773020567955352281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69534896515347045303568187 104302344773020567955352281)
            ·
              refine ⟨78226758579765425966514211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104302344773020567955352281 78226758579765425966514211)
              ·
                refine ⟨117340137869648138949771317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78226758579765425966514211 117340137869648138949771317)
                ·
                  refine ⟨11000637925279513026541061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117340137869648138949771317 11000637925279513026541061)
                  ·
                    refine ⟨2062619610989908692476449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11000637925279513026541061 2062619610989908692476449)
                    ·
                      refine ⟨1546964708242431519357337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062619610989908692476449 1546964708242431519357337)
                      ·
                        rfl

theorem cell23_3012703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_3012703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012703 prefixEnd_3012703 := by exact prefixLift 3012703
  have htrace : WordTrace (prefixWord ++ tailWord_3012703) baseStart_3012703 baseEnd_3012703 := by
    simpa [prefixWord, tailWord_3012703, baseEnd_3012703] using wordTrace_append hprefix tailTrace_3012703
  have hstable : (prefixWord ++ tailWord_3012703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012703).length < 2 ^ (prefixWord ++ tailWord_3012703).sum := by decide
  have hdescent : baseEnd_3012703 < baseStart_3012703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012737 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_3012737 : Nat := 118140960795 + 3012737 * 2 ^ 59
def prefixEnd_3012737 : Nat := 4983230072969 + 3 ^ 40 * 3012737 * 2
def baseEnd_3012737 : Nat := 1546982166584684386332181

theorem tailTrace_3012737 : CollatzResearch.WordTrace tailWord_3012737 prefixEnd_3012737 1546982166584684386332181 := by
  unfold tailWord_3012737
  simp only [CollatzResearch.WordTrace]
  refine ⟨109883545686375858360524465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73255697124250572240349643 109883545686375858360524465)
  ·
    refine ⟨82412659264781893770393349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109883545686375858360524465 82412659264781893770393349)
    ·
      refine ⟨15452373612146605081948753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82412659264781893770393349 15452373612146605081948753)
      ·
        refine ⟨11589280209109953811461565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15452373612146605081948753 11589280209109953811461565)
        ·
          refine ⟨4345980078416232679298087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11589280209109953811461565 4345980078416232679298087)
          ·
            refine ⟨6518970117624349018947131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345980078416232679298087 6518970117624349018947131)
            ·
              refine ⟨9778455176436523528420697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518970117624349018947131 9778455176436523528420697)
              ·
                refine ⟨7333841382327392646315523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9778455176436523528420697 7333841382327392646315523)
                ·
                  refine ⟨11000762073491088969473285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7333841382327392646315523 11000762073491088969473285)
                  ·
                    refine ⟨2062642888779579181776241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11000762073491088969473285 2062642888779579181776241)
                    ·
                      refine ⟨1546982166584684386332181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062642888779579181776241 1546982166584684386332181)
                      ·
                        rfl

theorem cell23_3012737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_3012737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012737 prefixEnd_3012737 := by exact prefixLift 3012737
  have htrace : WordTrace (prefixWord ++ tailWord_3012737) baseStart_3012737 baseEnd_3012737 := by
    simpa [prefixWord, tailWord_3012737, baseEnd_3012737] using wordTrace_append hprefix tailTrace_3012737
  have hstable : (prefixWord ++ tailWord_3012737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012737).length < 2 ^ (prefixWord ++ tailWord_3012737).sum := by decide
  have hdescent : baseEnd_3012737 < baseStart_3012737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012754 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_3012754 : Nat := 118140960795 + 3012754 * 2 ^ 59
def prefixEnd_3012754 : Nat := 4983230072969 + 3 ^ 40 * 3012754 * 2
def baseEnd_3012754 : Nat := 1546990895755810819819603

theorem tailTrace_3012754 : CollatzResearch.WordTrace tailWord_3012754 prefixEnd_3012754 1546990895755810819819603 := by
  unfold tailWord_3012754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471041431828567565973329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73256110484876180175928877 27471041431828567565973329)
  ·
    refine ⟨20603281073871425674479997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27471041431828567565973329 20603281073871425674479997)
    ·
      refine ⟨7726230402701784627929999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20603281073871425674479997 7726230402701784627929999)
      ·
        refine ⟨11589345604052676941894999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7726230402701784627929999 11589345604052676941894999)
        ·
          refine ⟨17384018406079015412842499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11589345604052676941894999 17384018406079015412842499)
          ·
            refine ⟨26076027609118523119263749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17384018406079015412842499 26076027609118523119263749)
            ·
              refine ⟨4889255176709723084861953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26076027609118523119263749 4889255176709723084861953)
              ·
                refine ⟨3666941382532292313646465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889255176709723084861953 3666941382532292313646465)
                ·
                  refine ⟨2750206036899219235234849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3666941382532292313646465 2750206036899219235234849)
                  ·
                    refine ⟨2062654527674414426426137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2750206036899219235234849 2062654527674414426426137)
                    ·
                      refine ⟨1546990895755810819819603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062654527674414426426137 1546990895755810819819603)
                      ·
                        rfl

theorem cell23_3012754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_3012754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012754 prefixEnd_3012754 := by exact prefixLift 3012754
  have htrace : WordTrace (prefixWord ++ tailWord_3012754) baseStart_3012754 baseEnd_3012754 := by
    simpa [prefixWord, tailWord_3012754, baseEnd_3012754] using wordTrace_append hprefix tailTrace_3012754
  have hstable : (prefixWord ++ tailWord_3012754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012754).length < 2 ^ (prefixWord ++ tailWord_3012754).sum := by decide
  have hdescent : baseEnd_3012754 < baseStart_3012754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012763 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 7, 2]
def baseStart_3012763 : Nat := 118140960795 + 3012763 * 2 ^ 59
def prefixEnd_3012763 : Nat := 4983230072969 + 3 ^ 40 * 3012763 * 2
def baseEnd_3012763 : Nat := 1546995517081701284607061

theorem tailTrace_3012763 : CollatzResearch.WordTrace tailWord_3012763 prefixEnd_3012763 1546995517081701284607061 := by
  unfold tailWord_3012763
  simp only [CollatzResearch.WordTrace]
  refine ⟨109884493984281664800970943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73256329322854443200647295 109884493984281664800970943)
  ·
    refine ⟨164826740976422497201456415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109884493984281664800970943 164826740976422497201456415)
    ·
      refine ⟨247240111464633745802184623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164826740976422497201456415 247240111464633745802184623)
      ·
        refine ⟨370860167196950618703276935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247240111464633745802184623 370860167196950618703276935)
        ·
          refine ⟨556290250795425928054915403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370860167196950618703276935 556290250795425928054915403)
          ·
            refine ⟨834435376193138892082373105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556290250795425928054915403 834435376193138892082373105)
            ·
              refine ⟨625826532144854169061779829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834435376193138892082373105 625826532144854169061779829)
              ·
                refine ⟨58671237388580078349541859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 625826532144854169061779829 58671237388580078349541859)
                ·
                  refine ⟨88006856082870117524312789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58671237388580078349541859 88006856082870117524312789)
                  ·
                    refine ⟨2062660689442268379476081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 88006856082870117524312789 2062660689442268379476081)
                    ·
                      refine ⟨1546995517081701284607061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062660689442268379476081 1546995517081701284607061)
                      ·
                        rfl

theorem cell23_3012763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7, 2].length) (baseStart_3012763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012763 prefixEnd_3012763 := by exact prefixLift 3012763
  have htrace : WordTrace (prefixWord ++ tailWord_3012763) baseStart_3012763 baseEnd_3012763 := by
    simpa [prefixWord, tailWord_3012763, baseEnd_3012763] using wordTrace_append hprefix tailTrace_3012763
  have hstable : (prefixWord ++ tailWord_3012763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012763).length < 2 ^ (prefixWord ++ tailWord_3012763).sum := by decide
  have hdescent : baseEnd_3012763 < baseStart_3012763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012770 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3012770 : Nat := 118140960795 + 3012770 * 2 ^ 59
def prefixEnd_3012770 : Nat := 4983230072969 + 3 ^ 40 * 3012770 * 2
def baseEnd_3012770 : Nat := 1546999111446282757219529

theorem tailTrace_3012770 : CollatzResearch.WordTrace tailWord_3012770 prefixEnd_3012770 1546999111446282757219529 := by
  unfold tailWord_3012770
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471187323814076249118941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73256499530170869997650509 27471187323814076249118941)
  ·
    refine ⟨10301695246430278593419603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27471187323814076249118941 10301695246430278593419603)
    ·
      refine ⟨15452542869645417890129405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10301695246430278593419603 15452542869645417890129405)
      ·
        refine ⟨5794703576117031708798527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15452542869645417890129405 5794703576117031708798527)
        ·
          refine ⟨8692055364175547563197791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794703576117031708798527 8692055364175547563197791)
          ·
            refine ⟨13038083046263321344796687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692055364175547563197791 13038083046263321344796687)
            ·
              refine ⟨19557124569394982017195031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13038083046263321344796687 19557124569394982017195031)
              ·
                refine ⟨29335686854092473025792547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19557124569394982017195031 29335686854092473025792547)
                ·
                  refine ⟨44003530281138709538688821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29335686854092473025792547 44003530281138709538688821)
                  ·
                    refine ⟨4125330963856754019252077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44003530281138709538688821 4125330963856754019252077)
                    ·
                      refine ⟨1546999111446282757219529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125330963856754019252077 1546999111446282757219529)
                      ·
                        rfl

theorem cell23_3012770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3012770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012770 prefixEnd_3012770 := by exact prefixLift 3012770
  have htrace : WordTrace (prefixWord ++ tailWord_3012770) baseStart_3012770 baseEnd_3012770 := by
    simpa [prefixWord, tailWord_3012770, baseEnd_3012770] using wordTrace_append hprefix tailTrace_3012770
  have hstable : (prefixWord ++ tailWord_3012770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012770).length < 2 ^ (prefixWord ++ tailWord_3012770).sum := by decide
  have hdescent : baseEnd_3012770 < baseStart_3012770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012793 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3012793 : Nat := 118140960795 + 3012793 * 2 ^ 59
def prefixEnd_3012793 : Nat := 4983230072969 + 3 ^ 40 * 3012793 * 2
def baseEnd_3012793 : Nat := 1547010921501336167231923

theorem tailTrace_3012793 : CollatzResearch.WordTrace tailWord_3012793 prefixEnd_3012793 1547010921501336167231923 := by
  unfold tailWord_3012793
  simp only [CollatzResearch.WordTrace]
  refine ⟨109885588174172979924563033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73257058782781986616375355 109885588174172979924563033)
  ·
    refine ⟨82414191130629734943422275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109885588174172979924563033 82414191130629734943422275)
    ·
      refine ⟨123621286695944602415133413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82414191130629734943422275 123621286695944602415133413)
      ·
        refine ⟨23178991255489612952837515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123621286695944602415133413 23178991255489612952837515)
        ·
          refine ⟨34768486883234419429256273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23178991255489612952837515 34768486883234419429256273)
          ·
            refine ⟨26076365162425814571942205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34768486883234419429256273 26076365162425814571942205)
            ·
              refine ⟨9778636935909680464478327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26076365162425814571942205 9778636935909680464478327)
              ·
                refine ⟨14667955403864520696717491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9778636935909680464478327 14667955403864520696717491)
                ·
                  refine ⟨22001933105796781045076237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14667955403864520696717491 22001933105796781045076237)
                  ·
                    refine ⟨8250724914673792891903589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22001933105796781045076237 8250724914673792891903589)
                    ·
                      refine ⟨1547010921501336167231923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8250724914673792891903589 1547010921501336167231923)
                      ·
                        rfl

theorem cell23_3012793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3012793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012793 prefixEnd_3012793 := by exact prefixLift 3012793
  have htrace : WordTrace (prefixWord ++ tailWord_3012793) baseStart_3012793 baseEnd_3012793 := by
    simpa [prefixWord, tailWord_3012793, baseEnd_3012793] using wordTrace_append hprefix tailTrace_3012793
  have hstable : (prefixWord ++ tailWord_3012793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012793).length < 2 ^ (prefixWord ++ tailWord_3012793).sum := by decide
  have hdescent : baseEnd_3012793 < baseStart_3012793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012810 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_3012810 : Nat := 118140960795 + 3012810 * 2 ^ 59
def prefixEnd_3012810 : Nat := 4983230072969 + 3 ^ 40 * 3012810 * 2
def baseEnd_3012810 : Nat := 1547019650672462600719345

theorem tailTrace_3012810 : CollatzResearch.WordTrace tailWord_3012810 prefixEnd_3012810 1547019650672462600719345 := by
  unfold tailWord_3012810
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471552053777847956982971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73257472143407594551954589 27471552053777847956982971)
  ·
    refine ⟨41207328080666771935474457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27471552053777847956982971 41207328080666771935474457)
    ·
      refine ⟨30905496060500078951605843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41207328080666771935474457 30905496060500078951605843)
      ·
        refine ⟨46358244090750118427408765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30905496060500078951605843 46358244090750118427408765)
        ·
          refine ⟨17384341534031294410278287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46358244090750118427408765 17384341534031294410278287)
          ·
            refine ⟨26076512301046941615417431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17384341534031294410278287 26076512301046941615417431)
            ·
              refine ⟨39114768451570412423126147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26076512301046941615417431 39114768451570412423126147)
              ·
                refine ⟨58672152677355618634689221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39114768451570412423126147 58672152677355618634689221)
                ·
                  refine ⟨11001028627004178494004229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58672152677355618634689221 11001028627004178494004229)
                  ·
                    refine ⟨2062692867563283467625793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11001028627004178494004229 2062692867563283467625793)
                    ·
                      refine ⟨1547019650672462600719345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062692867563283467625793 1547019650672462600719345)
                      ·
                        rfl

theorem cell23_3012810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_3012810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012810 prefixEnd_3012810 := by exact prefixLift 3012810
  have htrace : WordTrace (prefixWord ++ tailWord_3012810) baseStart_3012810 baseEnd_3012810 := by
    simpa [prefixWord, tailWord_3012810, baseEnd_3012810] using wordTrace_append hprefix tailTrace_3012810
  have hstable : (prefixWord ++ tailWord_3012810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012810).length < 2 ^ (prefixWord ++ tailWord_3012810).sum := by decide
  have hdescent : baseEnd_3012810 < baseStart_3012810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012843 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 3]
def baseStart_3012843 : Nat := 118140960795 + 3012843 * 2 ^ 59
def prefixEnd_3012843 : Nat := 4983230072969 + 3 ^ 40 * 3012843 * 2
def baseEnd_3012843 : Nat := 1547036595534060971606693

theorem tailTrace_3012843 : CollatzResearch.WordTrace tailWord_3012843 prefixEnd_3012843 1547036595534060971606693 := by
  unfold tailWord_3012843
  simp only [CollatzResearch.WordTrace]
  refine ⟨109887411823991838463883183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73258274549327892309255455 109887411823991838463883183)
  ·
    refine ⟨164831117735987757695824775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109887411823991838463883183 164831117735987757695824775)
    ·
      refine ⟨247246676603981636543737163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164831117735987757695824775 247246676603981636543737163)
      ·
        refine ⟨370870014905972454815605745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247246676603981636543737163 370870014905972454815605745)
        ·
          refine ⟨278152511179479341111704309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370870014905972454815605745 278152511179479341111704309)
          ·
            refine ⟨26076797923076188229222279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278152511179479341111704309 26076797923076188229222279)
            ·
              refine ⟨39115196884614282343833419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26076797923076188229222279 39115196884614282343833419)
              ·
                refine ⟨58672795326921423515750129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39115196884614282343833419 58672795326921423515750129)
                ·
                  refine ⟨44004596495191067636812597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58672795326921423515750129 44004596495191067636812597)
                  ·
                    refine ⟨4125430921424162590951181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44004596495191067636812597 4125430921424162590951181)
                    ·
                      refine ⟨1547036595534060971606693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125430921424162590951181 1547036595534060971606693)
                      ·
                        rfl

theorem cell23_3012843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 3].length) (baseStart_3012843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012843 prefixEnd_3012843 := by exact prefixLift 3012843
  have htrace : WordTrace (prefixWord ++ tailWord_3012843) baseStart_3012843 baseEnd_3012843 := by
    simpa [prefixWord, tailWord_3012843, baseEnd_3012843] using wordTrace_append hprefix tailTrace_3012843
  have hstable : (prefixWord ++ tailWord_3012843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012843).length < 2 ^ (prefixWord ++ tailWord_3012843).sum := by decide
  have hdescent : baseEnd_3012843 < baseStart_3012843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012854 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_3012854 : Nat := 118140960795 + 3012854 * 2 ^ 59
def prefixEnd_3012854 : Nat := 4983230072969 + 3 ^ 40 * 3012854 * 2
def baseEnd_3012854 : Nat := 515680747940420142856381

theorem tailTrace_3012854 : CollatzResearch.WordTrace tailWord_3012854 prefixEnd_3012854 515680747940420142856381 := by
  unfold tailWord_3012854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867988314184499208908351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73258542017967991561689077 6867988314184499208908351)
  ·
    refine ⟨10301982471276748813362527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6867988314184499208908351 10301982471276748813362527)
    ·
      refine ⟨15452973706915123220043791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10301982471276748813362527 15452973706915123220043791)
      ·
        refine ⟨23179460560372684830065687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15452973706915123220043791 23179460560372684830065687)
        ·
          refine ⟨34769190840559027245098531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23179460560372684830065687 34769190840559027245098531)
          ·
            refine ⟨52153786260838540867647797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34769190840559027245098531 52153786260838540867647797)
            ·
              refine ⟨4889417461953613206341981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52153786260838540867647797 4889417461953613206341981)
              ·
                refine ⟨1833531548232604952378243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889417461953613206341981 1833531548232604952378243)
                ·
                  refine ⟨2750297322348907428567365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833531548232604952378243 2750297322348907428567365)
                  ·
                    refine ⟨515680747940420142856381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750297322348907428567365 515680747940420142856381)
                    ·
                      rfl

theorem cell23_3012854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_3012854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012854 prefixEnd_3012854 := by exact prefixLift 3012854
  have htrace : WordTrace (prefixWord ++ tailWord_3012854) baseStart_3012854 baseEnd_3012854 := by
    simpa [prefixWord, tailWord_3012854, baseEnd_3012854] using wordTrace_append hprefix tailTrace_3012854
  have hstable : (prefixWord ++ tailWord_3012854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012854).length < 2 ^ (prefixWord ++ tailWord_3012854).sum := by decide
  have hdescent : baseEnd_3012854 < baseStart_3012854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012871 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 3, 4]
def baseStart_3012871 : Nat := 118140960795 + 3012871 * 2 ^ 59
def prefixEnd_3012871 : Nat := 4983230072969 + 3 ^ 40 * 3012871 * 2
def baseEnd_3012871 : Nat := 515683657664128954018855

theorem tailTrace_3012871 : CollatzResearch.WordTrace tailWord_3012871 prefixEnd_3012871 515683657664128954018855 := by
  unfold tailWord_3012871
  simp only [CollatzResearch.WordTrace]
  refine ⟨109888433067890399245902467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73258955378593599497268311 109888433067890399245902467)
  ·
    refine ⟨164832649601835598868853701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109888433067890399245902467 164832649601835598868853701)
    ·
      refine ⟨30906121800344174787910069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164832649601835598868853701 30906121800344174787910069)
      ·
        refine ⟨2897448918782266386366569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30906121800344174787910069 2897448918782266386366569)
        ·
          refine ⟨2173086689086699789774927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897448918782266386366569 2173086689086699789774927)
          ·
            refine ⟨3259630033630049684662391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173086689086699789774927 3259630033630049684662391)
            ·
              refine ⟨4889445050445074526993587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259630033630049684662391 4889445050445074526993587)
              ·
                refine ⟨7334167575667611790490381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889445050445074526993587 7334167575667611790490381)
                ·
                  refine ⟨2750312840875354421433893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7334167575667611790490381 2750312840875354421433893)
                  ·
                    refine ⟨515683657664128954018855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750312840875354421433893 515683657664128954018855)
                    ·
                      rfl

theorem cell23_3012871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_3012871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012871 prefixEnd_3012871 := by exact prefixLift 3012871
  have htrace : WordTrace (prefixWord ++ tailWord_3012871) baseStart_3012871 baseEnd_3012871 := by
    simpa [prefixWord, tailWord_3012871, baseEnd_3012871] using wordTrace_append hprefix tailTrace_3012871
  have hstable : (prefixWord ++ tailWord_3012871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012871).length < 2 ^ (prefixWord ++ tailWord_3012871).sum := by decide
  have hdescent : baseEnd_3012871 < baseStart_3012871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012914 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_3012914 : Nat := 118140960795 + 3012914 * 2 ^ 59
def prefixEnd_3012914 : Nat := 4983230072969 + 3 ^ 40 * 3012914 * 2
def baseEnd_3012914 : Nat := 515691017553510064606289

theorem tailTrace_3012914 : CollatzResearch.WordTrace tailWord_3012914 prefixEnd_3012914 515691017553510064606289 := by
  unfold tailWord_3012914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27472500351683654397429449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73260000937823078393145197 27472500351683654397429449)
  ·
    refine ⟨20604375263762740798072087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27472500351683654397429449 20604375263762740798072087)
    ·
      refine ⟨30906562895644111197108131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20604375263762740798072087 30906562895644111197108131)
      ·
        refine ⟨46359844343466166795662197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30906562895644111197108131 46359844343466166795662197)
        ·
          refine ⟨4346235407199953137093331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46359844343466166795662197 4346235407199953137093331)
          ·
            refine ⟨6519353110799929705639997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346235407199953137093331 6519353110799929705639997)
            ·
              refine ⟨2444757416549973639614999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6519353110799929705639997 2444757416549973639614999)
              ·
                refine ⟨3667136124824960459422499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444757416549973639614999 3667136124824960459422499)
                ·
                  refine ⟨5500704187237440689133749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667136124824960459422499 5500704187237440689133749)
                  ·
                    refine ⟨515691017553510064606289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5500704187237440689133749 515691017553510064606289)
                    ·
                      rfl

theorem cell23_3012914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_3012914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012914 prefixEnd_3012914 := by exact prefixLift 3012914
  have htrace : WordTrace (prefixWord ++ tailWord_3012914) baseStart_3012914 baseEnd_3012914 := by
    simpa [prefixWord, tailWord_3012914, baseEnd_3012914] using wordTrace_append hprefix tailTrace_3012914
  have hstable : (prefixWord ++ tailWord_3012914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012914).length < 2 ^ (prefixWord ++ tailWord_3012914).sum := by decide
  have hdescent : baseEnd_3012914 < baseStart_3012914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012920 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_3012920 : Nat := 118140960795 + 3012920 * 2 ^ 59
def prefixEnd_3012920 : Nat := 4983230072969 + 3 ^ 40 * 3012920 * 2
def baseEnd_3012920 : Nat := 1547076133544457170343839

theorem tailTrace_3012920 : CollatzResearch.WordTrace tailWord_3012920 prefixEnd_3012920 1547076133544457170343839 := by
  unfold tailWord_3012920
  simp only [CollatzResearch.WordTrace]
  refine ⟨54945110122356440307218107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73260146829808587076290809 54945110122356440307218107)
  ·
    refine ⟨82417665183534660460827161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54945110122356440307218107 82417665183534660460827161)
    ·
      refine ⟨61813248887650995345620371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82417665183534660460827161 61813248887650995345620371)
      ·
        refine ⟨92719873331476493018430557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61813248887650995345620371 92719873331476493018430557)
        ·
          refine ⟨34769952499303684881911459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92719873331476493018430557 34769952499303684881911459)
          ·
            refine ⟨52154928748955527322867189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34769952499303684881911459 52154928748955527322867189)
            ·
              refine ⟨4889524570214580686518799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52154928748955527322867189 4889524570214580686518799)
              ·
                refine ⟨7334286855321871029778199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889524570214580686518799 7334286855321871029778199)
                ·
                  refine ⟨11001430282982806544667299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334286855321871029778199 11001430282982806544667299)
                  ·
                    refine ⟨16502145424474209817000949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11001430282982806544667299 16502145424474209817000949)
                    ·
                      refine ⟨1547076133544457170343839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16502145424474209817000949 1547076133544457170343839)
                      ·
                        rfl

theorem cell23_3012920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_3012920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012920 prefixEnd_3012920 := by exact prefixLift 3012920
  have htrace : WordTrace (prefixWord ++ tailWord_3012920) baseStart_3012920 baseEnd_3012920 := by
    simpa [prefixWord, tailWord_3012920, baseEnd_3012920] using wordTrace_append hprefix tailTrace_3012920
  have hstable : (prefixWord ++ tailWord_3012920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012920).length < 2 ^ (prefixWord ++ tailWord_3012920).sum := by decide
  have hdescent : baseEnd_3012920 < baseStart_3012920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012927 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 2, 4]
def baseStart_3012927 : Nat := 118140960795 + 3012927 * 2 ^ 59
def prefixEnd_3012927 : Nat := 4983230072969 + 3 ^ 40 * 3012927 * 2
def baseEnd_3012927 : Nat := 515693242636346214318769

theorem tailTrace_3012927 : CollatzResearch.WordTrace tailWord_3012927 prefixEnd_3012927 515693242636346214318769 := by
  unfold tailWord_3012927
  simp only [CollatzResearch.WordTrace]
  refine ⟨109890475555687520809941035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73260317037125013873294023 109890475555687520809941035)
  ·
    refine ⟨164835713333531281214911553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109890475555687520809941035 164835713333531281214911553)
    ·
      refine ⟨123626785000148460911183665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164835713333531281214911553 123626785000148460911183665)
      ·
        refine ⟨92720088750111345683387749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123626785000148460911183665 92720088750111345683387749)
        ·
          refine ⟨17385016640645877315635203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92720088750111345683387749 17385016640645877315635203)
          ·
            refine ⟨26077524960968815973452805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17385016640645877315635203 26077524960968815973452805)
            ·
              refine ⟨4889535930181652995022401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26077524960968815973452805 4889535930181652995022401)
              ·
                refine ⟨3667151947636239746266801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889535930181652995022401 3667151947636239746266801)
                ·
                  refine ⟨2750363960727179809700101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667151947636239746266801 2750363960727179809700101)
                  ·
                    refine ⟨515693242636346214318769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750363960727179809700101 515693242636346214318769)
                    ·
                      rfl

theorem cell23_3012927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_3012927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012927 prefixEnd_3012927 := by exact prefixLift 3012927
  have htrace : WordTrace (prefixWord ++ tailWord_3012927) baseStart_3012927 baseEnd_3012927 := by
    simpa [prefixWord, tailWord_3012927, baseEnd_3012927] using wordTrace_append hprefix tailTrace_3012927
  have hstable : (prefixWord ++ tailWord_3012927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012927).length < 2 ^ (prefixWord ++ tailWord_3012927).sum := by decide
  have hdescent : baseEnd_3012927 < baseStart_3012927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012953 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_3012953 : Nat := 118140960795 + 3012953 * 2 ^ 59
def prefixEnd_3012953 : Nat := 4983230072969 + 3 ^ 40 * 3012953 * 2
def baseEnd_3012953 : Nat := 515697692802018513743729

theorem tailTrace_3012953 : CollatzResearch.WordTrace tailWord_3012953 prefixEnd_3012953 515697692802018513743729 := by
  unfold tailWord_3012953
  simp only [CollatzResearch.WordTrace]
  refine ⟨109891423853593327250387513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73260949235728884833591675 109891423853593327250387513)
  ·
    refine ⟨82418567890194995437790635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109891423853593327250387513 82418567890194995437790635)
    ·
      refine ⟨123627851835292493156685953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82418567890194995437790635 123627851835292493156685953)
      ·
        refine ⟨92720888876469369867514465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123627851835292493156685953 92720888876469369867514465)
        ·
          refine ⟨69540666657352027400635849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92720888876469369867514465 69540666657352027400635849)
          ·
            refine ⟨52155499993014020550476887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69540666657352027400635849 52155499993014020550476887)
            ·
              refine ⟨78233249989521030825715331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52155499993014020550476887 78233249989521030825715331)
              ·
                refine ⟨117349874984281546238572997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78233249989521030825715331 117349874984281546238572997)
                ·
                  refine ⟨22003101559552789919732437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117349874984281546238572997 22003101559552789919732437)
                  ·
                    refine ⟨515697692802018513743729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22003101559552789919732437 515697692802018513743729)
                    ·
                      rfl

theorem cell23_3012953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_3012953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012953 prefixEnd_3012953 := by exact prefixLift 3012953
  have htrace : WordTrace (prefixWord ++ tailWord_3012953) baseStart_3012953 baseEnd_3012953 := by
    simpa [prefixWord, tailWord_3012953, baseEnd_3012953] using wordTrace_append hprefix tailTrace_3012953
  have hstable : (prefixWord ++ tailWord_3012953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012953).length < 2 ^ (prefixWord ++ tailWord_3012953).sum := by decide
  have hdescent : baseEnd_3012953 < baseStart_3012953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012967 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3012967 : Nat := 118140960795 + 3012967 * 2 ^ 59
def prefixEnd_3012967 : Nat := 4983230072969 + 3 ^ 40 * 3012967 * 2
def baseEnd_3012967 : Nat := 1547100267135218486456123

theorem tailTrace_3012967 : CollatzResearch.WordTrace tailWord_3012967 prefixEnd_3012967 1547100267135218486456123 := by
  unfold tailWord_3012967
  simp only [CollatzResearch.WordTrace]
  refine ⟨109891934475542607641397155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73261289650361738427598103 109891934475542607641397155)
  ·
    refine ⟨164837901713313911462095733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109891934475542607641397155 164837901713313911462095733)
    ·
      refine ⟨15453553285623179199571475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164837901713313911462095733 15453553285623179199571475)
      ·
        refine ⟨23180329928434768799357213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15453553285623179199571475 23180329928434768799357213)
        ·
          refine ⟨8692623723163038299758955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23180329928434768799357213 8692623723163038299758955)
          ·
            refine ⟨13038935584744557449638433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692623723163038299758955 13038935584744557449638433)
            ·
              refine ⟨9779201688558418087228825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13038935584744557449638433 9779201688558418087228825)
              ·
                refine ⟨7334401266418813565421619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9779201688558418087228825 7334401266418813565421619)
                ·
                  refine ⟨11001601899628220348132429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334401266418813565421619 11001601899628220348132429)
                  ·
                    refine ⟨4125600712360582630549661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11001601899628220348132429 4125600712360582630549661)
                    ·
                      refine ⟨1547100267135218486456123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125600712360582630549661 1547100267135218486456123)
                      ·
                        rfl

theorem cell23_3012967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3012967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012967 prefixEnd_3012967 := by exact prefixLift 3012967
  have htrace : WordTrace (prefixWord ++ tailWord_3012967) baseStart_3012967 baseEnd_3012967 := by
    simpa [prefixWord, tailWord_3012967, baseEnd_3012967] using wordTrace_append hprefix tailTrace_3012967
  have hstable : (prefixWord ++ tailWord_3012967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012967).length < 2 ^ (prefixWord ++ tailWord_3012967).sum := by decide
  have hdescent : baseEnd_3012967 < baseStart_3012967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012968 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3012968 : Nat := 118140960795 + 3012968 * 2 ^ 59
def prefixEnd_3012968 : Nat := 4983230072969 + 3 ^ 40 * 3012968 * 2
def baseEnd_3012968 : Nat := 1547100780615872982543619

theorem tailTrace_3012968 : CollatzResearch.WordTrace tailWord_3012968 prefixEnd_3012968 1547100780615872982543619 := by
  unfold tailWord_3012968
  simp only [CollatzResearch.WordTrace]
  refine ⟨54945985474269492406091779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73261313965692656541455705 54945985474269492406091779)
  ·
    refine ⟨82418978211404238609137669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54945985474269492406091779 82418978211404238609137669)
    ·
      refine ⟨15453558414638294739213313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82418978211404238609137669 15453558414638294739213313)
      ·
        refine ⟨11590168810978721054409985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15453558414638294739213313 11590168810978721054409985)
        ·
          refine ⟨8692626608234040790807489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11590168810978721054409985 8692626608234040790807489)
          ·
            refine ⟨6519469956175530593105617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8692626608234040790807489 6519469956175530593105617)
            ·
              refine ⟨4889602467131647944829213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6519469956175530593105617 4889602467131647944829213)
              ·
                refine ⟨1833600925174367979310955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889602467131647944829213 1833600925174367979310955)
                ·
                  refine ⟨2750401387761551968966433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833600925174367979310955 2750401387761551968966433)
                  ·
                    refine ⟨2062801040821163976724825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2750401387761551968966433 2062801040821163976724825)
                    ·
                      refine ⟨1547100780615872982543619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062801040821163976724825 1547100780615872982543619)
                      ·
                        rfl

theorem cell23_3012968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3012968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3012968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3012968 prefixEnd_3012968 := by exact prefixLift 3012968
  have htrace : WordTrace (prefixWord ++ tailWord_3012968) baseStart_3012968 baseEnd_3012968 := by
    simpa [prefixWord, tailWord_3012968, baseEnd_3012968] using wordTrace_append hprefix tailTrace_3012968
  have hstable : (prefixWord ++ tailWord_3012968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012968).length < 2 ^ (prefixWord ++ tailWord_3012968).sum := by decide
  have hdescent : baseEnd_3012968 < baseStart_3012968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013000 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3013000 : Nat := 118140960795 + 3013000 * 2 ^ 59
def prefixEnd_3013000 : Nat := 4983230072969 + 3 ^ 40 * 3013000 * 2
def baseEnd_3013000 : Nat := 515705737332272285781157

theorem tailTrace_3013000 : CollatzResearch.WordTrace tailWord_3013000 prefixEnd_3013000 515705737332272285781157 := by
  unfold tailWord_3013000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54946569042211527138674227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73262092056282036184898969 54946569042211527138674227)
  ·
    refine ⟨82419853563317290708011341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54946569042211527138674227 82419853563317290708011341)
    ·
      refine ⟨30907445086243984015504253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82419853563317290708011341 30907445086243984015504253)
      ·
        refine ⟨11590291907341494005814095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30907445086243984015504253 11590291907341494005814095)
        ·
          refine ⟨17385437861012241008721143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11590291907341494005814095 17385437861012241008721143)
          ·
            refine ⟨26078156791518361513081715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17385437861012241008721143 26078156791518361513081715)
            ·
              refine ⟨39117235187277542269622573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26078156791518361513081715 39117235187277542269622573)
              ·
                refine ⟨14668963195229078351108465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39117235187277542269622573 14668963195229078351108465)
                ·
                  refine ⟨11001722396421808763331349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14668963195229078351108465 11001722396421808763331349)
                  ·
                    refine ⟨515705737332272285781157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11001722396421808763331349 515705737332272285781157)
                    ·
                      rfl

theorem cell23_3013000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3013000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013000 prefixEnd_3013000 := by exact prefixLift 3013000
  have htrace : WordTrace (prefixWord ++ tailWord_3013000) baseStart_3013000 baseEnd_3013000 := by
    simpa [prefixWord, tailWord_3013000, baseEnd_3013000] using wordTrace_append hprefix tailTrace_3013000
  have hstable : (prefixWord ++ tailWord_3013000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013000).length < 2 ^ (prefixWord ++ tailWord_3013000).sum := by decide
  have hdescent : baseEnd_3013000 < baseStart_3013000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013001 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 2, 1, 3]
def baseStart_3013001 : Nat := 118140960795 + 3013001 * 2 ^ 59
def prefixEnd_3013001 : Nat := 4983230072969 + 3 ^ 40 * 3013001 * 2
def baseEnd_3013001 : Nat := 1547117725477471353430967

theorem tailTrace_3013001 : CollatzResearch.WordTrace tailWord_3013001 prefixEnd_3013001 1547117725477471353430967 := by
  unfold tailWord_3013001
  simp only [CollatzResearch.WordTrace]
  refine ⟨109893174557419431448134857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73262116371612954298756571 109893174557419431448134857)
  ·
    refine ⟨82419880918064573586101143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109893174557419431448134857 82419880918064573586101143)
    ·
      refine ⟨123629821377096860379151715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82419880918064573586101143 123629821377096860379151715)
      ·
        refine ⟨185444732065645290568727573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123629821377096860379151715 185444732065645290568727573)
        ·
          refine ⟨8692721815577122995409105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185444732065645290568727573 8692721815577122995409105)
          ·
            refine ⟨6519541361682842246556829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8692721815577122995409105 6519541361682842246556829)
            ·
              refine ⟨2444828010631065842458811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6519541361682842246556829 2444828010631065842458811)
              ·
                refine ⟨3667242015946598763688217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444828010631065842458811 3667242015946598763688217)
                ·
                  refine ⟨2750431511959949072766163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667242015946598763688217 2750431511959949072766163)
                  ·
                    refine ⟨4125647267939923609149245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2750431511959949072766163 4125647267939923609149245)
                    ·
                      refine ⟨1547117725477471353430967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125647267939923609149245 1547117725477471353430967)
                      ·
                        rfl

theorem cell23_3013001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 1, 3].length) (baseStart_3013001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013001 prefixEnd_3013001 := by exact prefixLift 3013001
  have htrace : WordTrace (prefixWord ++ tailWord_3013001) baseStart_3013001 baseEnd_3013001 := by
    simpa [prefixWord, tailWord_3013001, baseEnd_3013001] using wordTrace_append hprefix tailTrace_3013001
  have hstable : (prefixWord ++ tailWord_3013001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013001).length < 2 ^ (prefixWord ++ tailWord_3013001).sum := by decide
  have hdescent : baseEnd_3013001 < baseStart_3013001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013024 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 4, 2, 2]
def baseStart_3013024 : Nat := 118140960795 + 3013024 * 2 ^ 59
def prefixEnd_3013024 : Nat := 4983230072969 + 3 ^ 40 * 3013024 * 2
def baseEnd_3013024 : Nat := 1547129535532524763443361

theorem tailTrace_3013024 : CollatzResearch.WordTrace tailWord_3013024 prefixEnd_3013024 1547129535532524763443361 := by
  unfold tailWord_3013024
  simp only [CollatzResearch.WordTrace]
  refine ⟨54947006718168053188111063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73262675624224070917481417 54947006718168053188111063)
  ·
    refine ⟨82420510077252079782166595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54947006718168053188111063 82420510077252079782166595)
    ·
      refine ⟨123630765115878119673249893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82420510077252079782166595 123630765115878119673249893)
      ·
        refine ⟨23180768459227147438734355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123630765115878119673249893 23180768459227147438734355)
        ·
          refine ⟨34771152688840721158101533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23180768459227147438734355 34771152688840721158101533)
          ·
            refine ⟨13039182258315270434288075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34771152688840721158101533 13039182258315270434288075)
            ·
              refine ⟨19558773387472905651432113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13039182258315270434288075 19558773387472905651432113)
              ·
                refine ⟨14669080040604679238574085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19558773387472905651432113 14669080040604679238574085)
                ·
                  refine ⟨2750452507613377357232641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14669080040604679238574085 2750452507613377357232641)
                  ·
                    refine ⟨2062839380710033017924481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2750452507613377357232641 2062839380710033017924481)
                    ·
                      refine ⟨1547129535532524763443361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2062839380710033017924481 1547129535532524763443361)
                      ·
                        rfl

theorem cell23_3013024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_3013024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013024 prefixEnd_3013024 := by exact prefixLift 3013024
  have htrace : WordTrace (prefixWord ++ tailWord_3013024) baseStart_3013024 baseEnd_3013024 := by
    simpa [prefixWord, tailWord_3013024, baseEnd_3013024] using wordTrace_append hprefix tailTrace_3013024
  have hstable : (prefixWord ++ tailWord_3013024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013024).length < 2 ^ (prefixWord ++ tailWord_3013024).sum := by decide
  have hdescent : baseEnd_3013024 < baseStart_3013024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013047 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 7]
def baseStart_3013047 : Nat := 118140960795 + 3013047 * 2 ^ 59
def prefixEnd_3013047 : Nat := 4983230072969 + 3 ^ 40 * 3013047 * 2
def baseEnd_3013047 : Nat := 171904593954175352606195

theorem tailTrace_3013047 : CollatzResearch.WordTrace tailWord_3013047 prefixEnd_3013047 171904593954175352606195 := by
  unfold tailWord_3013047
  simp only [CollatzResearch.WordTrace]
  refine ⟨109894852315252781304309395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73263234876835187536206263 109894852315252781304309395)
  ·
    refine ⟨164842278472879171956464093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109894852315252781304309395 164842278472879171956464093)
    ·
      refine ⟨61815854427329689483674035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164842278472879171956464093 61815854427329689483674035)
      ·
        refine ⟨92723781640994534225511053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61815854427329689483674035 92723781640994534225511053)
        ·
          refine ⟨34771418115372950334566645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92723781640994534225511053 34771418115372950334566645)
          ·
            refine ⟨3259820448316214093865623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34771418115372950334566645 3259820448316214093865623)
            ·
              refine ⟨4889730672474321140798435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259820448316214093865623 4889730672474321140798435)
              ·
                refine ⟨7334596008711481711197653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889730672474321140798435 7334596008711481711197653)
                ·
                  refine ⟨171904593954175352606195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7334596008711481711197653 171904593954175352606195)
                  ·
                    rfl

theorem cell23_3013047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 7].length) (baseStart_3013047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013047 prefixEnd_3013047 := by exact prefixLift 3013047
  have htrace : WordTrace (prefixWord ++ tailWord_3013047) baseStart_3013047 baseEnd_3013047 := by
    simpa [prefixWord, tailWord_3013047, baseEnd_3013047] using wordTrace_append hprefix tailTrace_3013047
  have hstable : (prefixWord ++ tailWord_3013047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013047).length < 2 ^ (prefixWord ++ tailWord_3013047).sum := by decide
  have hdescent : baseEnd_3013047 < baseStart_3013047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013070 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3013070 : Nat := 118140960795 + 3013070 * 2 ^ 59
def prefixEnd_3013070 : Nat := 4983230072969 + 3 ^ 40 * 3013070 * 2
def baseEnd_3013070 : Nat := 1547153155642631583468149

theorem tailTrace_3013070 : CollatzResearch.WordTrace tailWord_3013070 prefixEnd_3013070 1547153155642631583468149 := by
  unfold tailWord_3013070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13736961399271182029049583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73263794129446304154931109 13736961399271182029049583)
  ·
    refine ⟨20605442098906773043574375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13736961399271182029049583 20605442098906773043574375)
    ·
      refine ⟨30908163148360159565361563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20605442098906773043574375 30908163148360159565361563)
      ·
        refine ⟨46362244722540239348042345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30908163148360159565361563 46362244722540239348042345)
        ·
          refine ⟨34771683541905179511031759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46362244722540239348042345 34771683541905179511031759)
          ·
            refine ⟨52157525312857769266547639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34771683541905179511031759 52157525312857769266547639)
            ·
              refine ⟨78236287969286653899821459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52157525312857769266547639 78236287969286653899821459)
              ·
                refine ⟨117354431953929980849732189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78236287969286653899821459 117354431953929980849732189)
                ·
                  refine ⟨44007911982723742818649571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117354431953929980849732189 44007911982723742818649571)
                  ·
                    refine ⟨66011867974085614227974357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44007911982723742818649571 66011867974085614227974357)
                    ·
                      refine ⟨1547153155642631583468149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66011867974085614227974357 1547153155642631583468149)
                      ·
                        rfl

theorem cell23_3013070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3013070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013070 prefixEnd_3013070 := by exact prefixLift 3013070
  have htrace : WordTrace (prefixWord ++ tailWord_3013070) baseStart_3013070 baseEnd_3013070 := by
    simpa [prefixWord, tailWord_3013070, baseEnd_3013070] using wordTrace_append hprefix tailTrace_3013070
  have hstable : (prefixWord ++ tailWord_3013070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013070).length < 2 ^ (prefixWord ++ tailWord_3013070).sum := by decide
  have hdescent : baseEnd_3013070 < baseStart_3013070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013077 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_3013077 : Nat := 118140960795 + 3013077 * 2 ^ 59
def prefixEnd_3013077 : Nat := 4983230072969 + 3 ^ 40 * 3013077 * 2
def baseEnd_3013077 : Nat := 515718916669071018693539

theorem tailTrace_3013077 : CollatzResearch.WordTrace tailWord_3013077 prefixEnd_3013077 515718916669071018693539 := by
  unfold tailWord_3013077
  simp only [CollatzResearch.WordTrace]
  refine ⟨109895946505144096427901485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73263964336762730951934323 109895946505144096427901485)
  ·
    refine ⟨41210979939429036160463057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109895946505144096427901485 41210979939429036160463057)
    ·
      refine ⟨30908234954571777120347293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41210979939429036160463057 30908234954571777120347293)
      ·
        refine ⟨11590588107964416420130235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30908234954571777120347293 11590588107964416420130235)
        ·
          refine ⟨17385882161946624630195353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11590588107964416420130235 17385882161946624630195353)
          ·
            refine ⟨13039411621459968472646515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17385882161946624630195353 13039411621459968472646515)
            ·
              refine ⟨19559117432189952708969773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13039411621459968472646515 19559117432189952708969773)
              ·
                refine ⟨7334669037071232265863665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19559117432189952708969773 7334669037071232265863665)
                ·
                  refine ⟨5501001777803424199397749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7334669037071232265863665 5501001777803424199397749)
                  ·
                    refine ⟨515718916669071018693539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5501001777803424199397749 515718916669071018693539)
                    ·
                      rfl

theorem cell23_3013077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_3013077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013077 prefixEnd_3013077 := by exact prefixLift 3013077
  have htrace : WordTrace (prefixWord ++ tailWord_3013077) baseStart_3013077 baseEnd_3013077 := by
    simpa [prefixWord, tailWord_3013077, baseEnd_3013077] using wordTrace_append hprefix tailTrace_3013077
  have hstable : (prefixWord ++ tailWord_3013077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013077).length < 2 ^ (prefixWord ++ tailWord_3013077).sum := by decide
  have hdescent : baseEnd_3013077 < baseStart_3013077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013100 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3013100 : Nat := 118140960795 + 3013100 * 2 ^ 59
def prefixEnd_3013100 : Nat := 4983230072969 + 3 ^ 40 * 3013100 * 2
def baseEnd_3013100 : Nat := 1547168560062266466093011

theorem tailTrace_3013100 : CollatzResearch.WordTrace tailWord_3013100 prefixEnd_3013100 1547168560062266466093011 := by
  unfold tailWord_3013100
  simp only [CollatzResearch.WordTrace]
  refine ⟨54948392692030385677994377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73264523589373847570659169 54948392692030385677994377)
  ·
    refine ⟨41211294519022789258495783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54948392692030385677994377 41211294519022789258495783)
    ·
      refine ⟨61816941778534183887743675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41211294519022789258495783 61816941778534183887743675)
      ·
        refine ⟨92725412667801275831615513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61816941778534183887743675 92725412667801275831615513)
        ·
          refine ⟨69544059500850956873711635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92725412667801275831615513 69544059500850956873711635)
          ·
            refine ⟨104316089251276435310567453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69544059500850956873711635 104316089251276435310567453)
            ·
              refine ⟨39118533469228663241462795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104316089251276435310567453 39118533469228663241462795)
              ·
                refine ⟨58677800203842994862194193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39118533469228663241462795 58677800203842994862194193)
                ·
                  refine ⟨44008350152882246146645645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58677800203842994862194193 44008350152882246146645645)
                  ·
                    refine ⟨16503131307330842304992117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44008350152882246146645645 16503131307330842304992117)
                    ·
                      refine ⟨1547168560062266466093011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16503131307330842304992117 1547168560062266466093011)
                      ·
                        rfl

theorem cell23_3013100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3013100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013100 prefixEnd_3013100 := by exact prefixLift 3013100
  have htrace : WordTrace (prefixWord ++ tailWord_3013100) baseStart_3013100 baseEnd_3013100 := by
    simpa [prefixWord, tailWord_3013100, baseEnd_3013100] using wordTrace_append hprefix tailTrace_3013100
  have hstable : (prefixWord ++ tailWord_3013100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013100).length < 2 ^ (prefixWord ++ tailWord_3013100).sum := by decide
  have hdescent : baseEnd_3013100 < baseStart_3013100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013107 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 3, 4]
def baseStart_3013107 : Nat := 118140960795 + 3013107 * 2 ^ 59
def prefixEnd_3013107 : Nat := 4983230072969 + 3 ^ 40 * 3013107 * 2
def baseEnd_3013107 : Nat := 515724051475615979568493

theorem tailTrace_3013107 : CollatzResearch.WordTrace tailWord_3013107 prefixEnd_3013107 515724051475615979568493 := by
  unfold tailWord_3013107
  simp only [CollatzResearch.WordTrace]
  refine ⟨109897040695035411551493575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73264693796690274367662383 109897040695035411551493575)
  ·
    refine ⟨164845561042553117327240363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109897040695035411551493575 164845561042553117327240363)
    ·
      refine ⟨247268341563829675990860545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164845561042553117327240363 247268341563829675990860545)
      ·
        refine ⟨185451256172872256993145409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247268341563829675990860545 185451256172872256993145409)
        ·
          refine ⟨139088442129654192744859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185451256172872256993145409 139088442129654192744859057)
          ·
            refine ⟨104316331597240644558644293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139088442129654192744859057 104316331597240644558644293)
            ·
              refine ⟨19559312174482620854745805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104316331597240644558644293 19559312174482620854745805)
              ·
                refine ⟨7334742065430982820529677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19559312174482620854745805 7334742065430982820529677)
                ·
                  refine ⟨2750528274536618557698629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7334742065430982820529677 2750528274536618557698629)
                  ·
                    refine ⟨515724051475615979568493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750528274536618557698629 515724051475615979568493)
                    ·
                      rfl

theorem cell23_3013107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 4].length) (baseStart_3013107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013107 prefixEnd_3013107 := by exact prefixLift 3013107
  have htrace : WordTrace (prefixWord ++ tailWord_3013107) baseStart_3013107 baseEnd_3013107 := by
    simpa [prefixWord, tailWord_3013107, baseEnd_3013107] using wordTrace_append hprefix tailTrace_3013107
  have hstable : (prefixWord ++ tailWord_3013107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013107).length < 2 ^ (prefixWord ++ tailWord_3013107).sum := by decide
  have hdescent : baseEnd_3013107 < baseStart_3013107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013117 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_3013117 : Nat := 118140960795 + 3013117 * 2 ^ 59
def prefixEnd_3013117 : Nat := 4983230072969 + 3 ^ 40 * 3013117 * 2
def baseEnd_3013117 : Nat := 1547177289233392899580433

theorem tailTrace_3013117 : CollatzResearch.WordTrace tailWord_3013117 prefixEnd_3013117 1547177289233392899580433 := by
  unfold tailWord_3013117
  simp only [CollatzResearch.WordTrace]
  refine ⟨109897405424999183259357605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73264936949999455506238403 109897405424999183259357605)
  ·
    refine ⟨20605763517187346861129551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109897405424999183259357605 20605763517187346861129551)
    ·
      refine ⟨30908645275781020291694327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20605763517187346861129551 30908645275781020291694327)
      ·
        refine ⟨46362967913671530437541491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30908645275781020291694327 46362967913671530437541491)
        ·
          refine ⟨69544451870507295656312237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46362967913671530437541491 69544451870507295656312237)
          ·
            refine ⟨26079169451440235871117089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69544451870507295656312237 26079169451440235871117089)
            ·
              refine ⟨19559377088580176903337817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26079169451440235871117089 19559377088580176903337817)
              ·
                refine ⟨14669532816435132677503363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19559377088580176903337817 14669532816435132677503363)
                ·
                  refine ⟨22004299224652699016255045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14669532816435132677503363 22004299224652699016255045)
                  ·
                    refine ⟨4125806104622381065547821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22004299224652699016255045 4125806104622381065547821)
                    ·
                      refine ⟨1547177289233392899580433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125806104622381065547821 1547177289233392899580433)
                      ·
                        rfl

theorem cell23_3013117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_3013117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013117 prefixEnd_3013117 := by exact prefixLift 3013117
  have htrace : WordTrace (prefixWord ++ tailWord_3013117) baseStart_3013117 baseEnd_3013117 := by
    simpa [prefixWord, tailWord_3013117, baseEnd_3013117] using wordTrace_append hprefix tailTrace_3013117
  have hstable : (prefixWord ++ tailWord_3013117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013117).length < 2 ^ (prefixWord ++ tailWord_3013117).sum := by decide
  have hdescent : baseEnd_3013117 < baseStart_3013117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013124 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_3013124 : Nat := 118140960795 + 3013124 * 2 ^ 59
def prefixEnd_3013124 : Nat := 4983230072969 + 3 ^ 40 * 3013124 * 2
def baseEnd_3013124 : Nat := 515726961199324790730967

theorem tailTrace_3013124 : CollatzResearch.WordTrace tailWord_3013124 prefixEnd_3013124 515726961199324790730967 := by
  unfold tailWord_3013124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54948830367986911727431213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73265107157315882303241617 54948830367986911727431213)
  ·
    refine ⟨20605811387995091897786705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54948830367986911727431213 20605811387995091897786705)
    ·
      refine ⟨15454358540996318923340029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20605811387995091897786705 15454358540996318923340029)
      ·
        refine ⟨5795384452873619596252511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15454358540996318923340029 5795384452873619596252511)
        ·
          refine ⟨8693076679310429394378767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795384452873619596252511 8693076679310429394378767)
          ·
            refine ⟨13039615018965644091568151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693076679310429394378767 13039615018965644091568151)
            ·
              refine ⟨19559422528448466137352227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13039615018965644091568151 19559422528448466137352227)
              ·
                refine ⟨29339133792672699206028341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19559422528448466137352227 29339133792672699206028341)
                ·
                  refine ⟨2750543793063065550565157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29339133792672699206028341 2750543793063065550565157)
                  ·
                    refine ⟨515726961199324790730967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750543793063065550565157 515726961199324790730967)
                    ·
                      rfl

theorem cell23_3013124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_3013124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013124 prefixEnd_3013124 := by exact prefixLift 3013124
  have htrace : WordTrace (prefixWord ++ tailWord_3013124) baseStart_3013124 baseEnd_3013124 := by
    simpa [prefixWord, tailWord_3013124, baseEnd_3013124] using wordTrace_append hprefix tailTrace_3013124
  have hstable : (prefixWord ++ tailWord_3013124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013124).length < 2 ^ (prefixWord ++ tailWord_3013124).sum := by decide
  have hdescent : baseEnd_3013124 < baseStart_3013124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013134 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3013134 : Nat := 118140960795 + 3013134 * 2 ^ 59
def prefixEnd_3013134 : Nat := 4983230072969 + 3 ^ 40 * 3013134 * 2
def baseEnd_3013134 : Nat := 1547186018404519333067855

theorem tailTrace_3013134 : CollatzResearch.WordTrace tailWord_3013134 prefixEnd_3013134 1547186018404519333067855 := by
  unfold tailWord_3013134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737253183242199395340807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73265350310625063441817637 13737253183242199395340807)
  ·
    refine ⟨20605879774863299093011211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13737253183242199395340807 20605879774863299093011211)
    ·
      refine ⟨30908819662294948639516817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20605879774863299093011211 30908819662294948639516817)
      ·
        refine ⟨23181614746721211479637613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30908819662294948639516817 23181614746721211479637613)
        ·
          refine ⟨8693105530020454304864105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23181614746721211479637613 8693105530020454304864105)
          ·
            refine ⟨6519829147515340728648079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8693105530020454304864105 6519829147515340728648079)
            ·
              refine ⟨9779743721273011092972119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6519829147515340728648079 9779743721273011092972119)
              ·
                refine ⟨14669615581909516639458179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9779743721273011092972119 14669615581909516639458179)
                ·
                  refine ⟨22004423372864274959187269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14669615581909516639458179 22004423372864274959187269)
                  ·
                    refine ⟨4125829382412051554847613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22004423372864274959187269 4125829382412051554847613)
                    ·
                      refine ⟨1547186018404519333067855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125829382412051554847613 1547186018404519333067855)
                      ·
                        rfl

theorem cell23_3013134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3013134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013134 prefixEnd_3013134 := by exact prefixLift 3013134
  have htrace : WordTrace (prefixWord ++ tailWord_3013134) baseStart_3013134 baseEnd_3013134 := by
    simpa [prefixWord, tailWord_3013134, baseEnd_3013134] using wordTrace_append hprefix tailTrace_3013134
  have hstable : (prefixWord ++ tailWord_3013134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013134).length < 2 ^ (prefixWord ++ tailWord_3013134).sum := by decide
  have hdescent : baseEnd_3013134 < baseStart_3013134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013141 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_3013141 : Nat := 118140960795 + 3013141 * 2 ^ 59
def prefixEnd_3013141 : Nat := 4983230072969 + 3 ^ 40 * 3013141 * 2
def baseEnd_3013141 : Nat := 515729870923033601893441

theorem tailTrace_3013141 : CollatzResearch.WordTrace tailWord_3013141 prefixEnd_3013141 515729870923033601893441 := by
  unfold tailWord_3013141
  simp only [CollatzResearch.WordTrace]
  refine ⟨109898280776912235358231277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73265520517941490238820851 109898280776912235358231277)
  ·
    refine ⟨41211855291342088259336729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109898280776912235358231277 41211855291342088259336729)
    ·
      refine ⟨30908891468506566194502547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41211855291342088259336729 30908891468506566194502547)
      ·
        refine ⟨46363337202759849291753821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30908891468506566194502547 46363337202759849291753821)
        ·
          refine ⟨17386251451034943484407683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46363337202759849291753821 17386251451034943484407683)
          ·
            refine ⟨26079377176552415226611525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17386251451034943484407683 26079377176552415226611525)
            ·
              refine ⟨4889883220603577854989661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26079377176552415226611525 4889883220603577854989661)
              ·
                refine ⟨1833706207726341695621123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889883220603577854989661 1833706207726341695621123)
                ·
                  refine ⟨2750559311589512543431685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833706207726341695621123 2750559311589512543431685)
                  ·
                    refine ⟨515729870923033601893441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750559311589512543431685 515729870923033601893441)
                    ·
                      rfl

theorem cell23_3013141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_3013141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013141 prefixEnd_3013141 := by exact prefixLift 3013141
  have htrace : WordTrace (prefixWord ++ tailWord_3013141) baseStart_3013141 baseEnd_3013141 := by
    simpa [prefixWord, tailWord_3013141, baseEnd_3013141] using wordTrace_append hprefix tailTrace_3013141
  have hstable : (prefixWord ++ tailWord_3013141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013141).length < 2 ^ (prefixWord ++ tailWord_3013141).sum := by decide
  have hdescent : baseEnd_3013141 < baseStart_3013141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013181 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3013181 : Nat := 118140960795 + 3013181 * 2 ^ 59
def prefixEnd_3013181 : Nat := 4983230072969 + 3 ^ 40 * 3013181 * 2
def baseEnd_3013181 : Nat := 1547210151995280649180139

theorem tailTrace_3013181 : CollatzResearch.WordTrace tailWord_3013181 prefixEnd_3013181 1547210151995280649180139 := by
  unfold tailWord_3013181
  simp only [CollatzResearch.WordTrace]
  refine ⟨109899739696767322189687397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73266493131178214793124931 109899739696767322189687397)
  ·
    refine ⟨20606201193143872910566387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109899739696767322189687397 20606201193143872910566387)
    ·
      refine ⟨30909301789715809365849581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20606201193143872910566387 30909301789715809365849581)
      ·
        refine ⟨11590988171143428512193593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30909301789715809365849581 11590988171143428512193593)
        ·
          refine ⟨8693241128357571384145195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11590988171143428512193593 8693241128357571384145195)
          ·
            refine ⟨13039861692536357076217793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693241128357571384145195 13039861692536357076217793)
            ·
              refine ⟨9779896269402267807163345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13039861692536357076217793 9779896269402267807163345)
              ·
                refine ⟨7334922202051700855372509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9779896269402267807163345 7334922202051700855372509)
                ·
                  refine ⟨2750595825769387820764691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7334922202051700855372509 2750595825769387820764691)
                  ·
                    refine ⟨4125893738654081731147037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2750595825769387820764691 4125893738654081731147037)
                    ·
                      refine ⟨1547210151995280649180139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125893738654081731147037 1547210151995280649180139)
                      ·
                        rfl

theorem cell23_3013181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3013181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013181 prefixEnd_3013181 := by exact prefixLift 3013181
  have htrace : WordTrace (prefixWord ++ tailWord_3013181) baseStart_3013181 baseEnd_3013181 := by
    simpa [prefixWord, tailWord_3013181, baseEnd_3013181] using wordTrace_append hprefix tailTrace_3013181
  have hstable : (prefixWord ++ tailWord_3013181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013181).length < 2 ^ (prefixWord ++ tailWord_3013181).sum := by decide
  have hdescent : baseEnd_3013181 < baseStart_3013181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013187 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 4]
def baseStart_3013187 : Nat := 118140960795 + 3013187 * 2 ^ 59
def prefixEnd_3013187 : Nat := 4983230072969 + 3 ^ 40 * 3013187 * 2
def baseEnd_3013187 : Nat := 1547213232879207625705111

theorem tailTrace_3013187 : CollatzResearch.WordTrace tailWord_3013187 prefixEnd_3013187 1547213232879207625705111 := by
  unfold tailWord_3013187
  simp only [CollatzResearch.WordTrace]
  refine ⟨109899958534745585214405815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73266639023163723476270543 109899958534745585214405815)
  ·
    refine ⟨164849937802118377821608723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109899958534745585214405815 164849937802118377821608723)
    ·
      refine ⟨247274906703177566732413085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164849937802118377821608723 247274906703177566732413085)
      ·
        refine ⟨92728090013691587524654907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247274906703177566732413085 92728090013691587524654907)
        ·
          refine ⟨139092135020537381286982361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92728090013691587524654907 139092135020537381286982361)
          ·
            refine ⟨104319101265403035965236771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139092135020537381286982361 104319101265403035965236771)
            ·
              refine ⟨156478651898104553947855157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104319101265403035965236771 156478651898104553947855157)
              ·
                refine ⟨14669873615447301932611421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156478651898104553947855157 14669873615447301932611421)
                ·
                  refine ⟨5501202605792738224729283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14669873615447301932611421 5501202605792738224729283)
                  ·
                    refine ⟨8251803908689107337093925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5501202605792738224729283 8251803908689107337093925)
                    ·
                      refine ⟨1547213232879207625705111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8251803908689107337093925 1547213232879207625705111)
                      ·
                        rfl

theorem cell23_3013187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_3013187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013187 prefixEnd_3013187 := by exact prefixLift 3013187
  have htrace : WordTrace (prefixWord ++ tailWord_3013187) baseStart_3013187 baseEnd_3013187 := by
    simpa [prefixWord, tailWord_3013187, baseEnd_3013187] using wordTrace_append hprefix tailTrace_3013187
  have hstable : (prefixWord ++ tailWord_3013187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013187).length < 2 ^ (prefixWord ++ tailWord_3013187).sum := by decide
  have hdescent : baseEnd_3013187 < baseStart_3013187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013198 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_3013198 : Nat := 118140960795 + 3013198 * 2 ^ 59
def prefixEnd_3013198 : Nat := 4983230072969 + 3 ^ 40 * 3013198 * 2
def baseEnd_3013198 : Nat := 1547218881166407082667561

theorem tailTrace_3013198 : CollatzResearch.WordTrace tailWord_3013198 prefixEnd_3013198 1547218881166407082667561 := by
  unfold tailWord_3013198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737544967213216761632031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73266906491803822728704165 13737544967213216761632031)
  ·
    refine ⟨20606317450819825142448047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13737544967213216761632031 20606317450819825142448047)
    ·
      refine ⟨30909476176229737713672071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20606317450819825142448047 30909476176229737713672071)
      ·
        refine ⟨46364214264344606570508107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30909476176229737713672071 46364214264344606570508107)
        ·
          refine ⟨69546321396516909855762161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46364214264344606570508107 69546321396516909855762161)
          ·
            refine ⟨52159741047387682391821621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69546321396516909855762161 52159741047387682391821621)
            ·
              refine ⟨4889975723192595224233277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52159741047387682391821621 4889975723192595224233277)
              ·
                refine ⟨1833740896197223209087479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889975723192595224233277 1833740896197223209087479)
                ·
                  refine ⟨2750611344295834813631219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833740896197223209087479 2750611344295834813631219)
                  ·
                    refine ⟨4125917016443752220446829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2750611344295834813631219 4125917016443752220446829)
                    ·
                      refine ⟨1547218881166407082667561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125917016443752220446829 1547218881166407082667561)
                      ·
                        rfl

theorem cell23_3013198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_3013198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013198 prefixEnd_3013198 := by exact prefixLift 3013198
  have htrace : WordTrace (prefixWord ++ tailWord_3013198) baseStart_3013198 baseEnd_3013198 := by
    simpa [prefixWord, tailWord_3013198, baseEnd_3013198] using wordTrace_append hprefix tailTrace_3013198
  have hstable : (prefixWord ++ tailWord_3013198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013198).length < 2 ^ (prefixWord ++ tailWord_3013198).sum := by decide
  have hdescent : baseEnd_3013198 < baseStart_3013198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013217 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3013217 : Nat := 118140960795 + 3013217 * 2 ^ 59
def prefixEnd_3013217 : Nat := 4983230072969 + 3 ^ 40 * 3013217 * 2
def baseEnd_3013217 : Nat := 1547228637298842508329973

theorem tailTrace_3013217 : CollatzResearch.WordTrace tailWord_3013217 prefixEnd_3013217 1547228637298842508329973 := by
  unfold tailWord_3013217
  simp only [CollatzResearch.WordTrace]
  refine ⟨109901052724636900337997905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73267368483091266891998603 109901052724636900337997905)
  ·
    refine ⟨82425789543477675253498429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109901052724636900337997905 82425789543477675253498429)
    ·
      refine ⟨30909671078804128220061911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82425789543477675253498429 30909671078804128220061911)
      ·
        refine ⟨46364506618206192330092867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30909671078804128220061911 46364506618206192330092867)
        ·
          refine ⟨69546759927309288495139301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46364506618206192330092867 69546759927309288495139301)
          ·
            refine ⟨13040017486370491592838619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69546759927309288495139301 13040017486370491592838619)
            ·
              refine ⟨19560026229555737389257929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13040017486370491592838619 19560026229555737389257929)
              ·
                refine ⟨14670019672166803041943447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19560026229555737389257929 14670019672166803041943447)
                ·
                  refine ⟨22005029508250204562915171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14670019672166803041943447 22005029508250204562915171)
                  ·
                    refine ⟨33007544262375306844372757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22005029508250204562915171 33007544262375306844372757)
                    ·
                      refine ⟨1547228637298842508329973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33007544262375306844372757 1547228637298842508329973)
                      ·
                        rfl

theorem cell23_3013217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3013217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013217 prefixEnd_3013217 := by exact prefixLift 3013217
  have htrace : WordTrace (prefixWord ++ tailWord_3013217) baseStart_3013217 baseEnd_3013217 := by
    simpa [prefixWord, tailWord_3013217, baseEnd_3013217] using wordTrace_append hprefix tailTrace_3013217
  have hstable : (prefixWord ++ tailWord_3013217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013217).length < 2 ^ (prefixWord ++ tailWord_3013217).sum := by decide
  have hdescent : baseEnd_3013217 < baseStart_3013217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013231 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 2, 4]
def baseStart_3013231 : Nat := 118140960795 + 3013231 * 2 ^ 59
def prefixEnd_3013231 : Nat := 4983230072969 + 3 ^ 40 * 3013231 * 2
def baseEnd_3013231 : Nat := 515745275342668484518303

theorem tailTrace_3013231 : CollatzResearch.WordTrace tailWord_3013231 prefixEnd_3013231 515745275342668484518303 := by
  unfold tailWord_3013231
  simp only [CollatzResearch.WordTrace]
  refine ⟨109901563346586180729007547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73267708897724120486005031 109901563346586180729007547)
  ·
    refine ⟨164852345019879271093511321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109901563346586180729007547 164852345019879271093511321)
    ·
      refine ⟨123639258764909453320133491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164852345019879271093511321 123639258764909453320133491)
      ·
        refine ⟨185458888147364179980200237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123639258764909453320133491 185458888147364179980200237)
        ·
          refine ⟨69547083055261567492575089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185458888147364179980200237 69547083055261567492575089)
          ·
            refine ⟨52160312291446175619431317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69547083055261567492575089 52160312291446175619431317)
            ·
              refine ⟨2445014638661539482160843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52160312291446175619431317 2445014638661539482160843)
              ·
                refine ⟨3667521957992309223241265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445014638661539482160843 3667521957992309223241265)
                ·
                  refine ⟨2750641468494231917430949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667521957992309223241265 2750641468494231917430949)
                  ·
                    refine ⟨515745275342668484518303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750641468494231917430949 515745275342668484518303)
                    ·
                      rfl

theorem cell23_3013231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 4].length) (baseStart_3013231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013231 prefixEnd_3013231 := by exact prefixLift 3013231
  have htrace : WordTrace (prefixWord ++ tailWord_3013231) baseStart_3013231 baseEnd_3013231 := by
    simpa [prefixWord, tailWord_3013231, baseEnd_3013231] using wordTrace_append hprefix tailTrace_3013231
  have hstable : (prefixWord ++ tailWord_3013231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013231).length < 2 ^ (prefixWord ++ tailWord_3013231).sum := by decide
  have hdescent : baseEnd_3013231 < baseStart_3013231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013241 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 3]
def baseStart_3013241 : Nat := 118140960795 + 3013241 * 2 ^ 59
def prefixEnd_3013241 : Nat := 4983230072969 + 3 ^ 40 * 3013241 * 2
def baseEnd_3013241 : Nat := 1547240960834550414429863

theorem tailTrace_3013241 : CollatzResearch.WordTrace tailWord_3013241 prefixEnd_3013241 1547240960834550414429863 := by
  unfold tailWord_3013241
  simp only [CollatzResearch.WordTrace]
  refine ⟨109901928076549952436871577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73267952051033301624581051 109901928076549952436871577)
  ·
    refine ⟨82426446057412464327653683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109901928076549952436871577 82426446057412464327653683)
    ·
      refine ⟨123639669086118696491480525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82426446057412464327653683 123639669086118696491480525)
      ·
        refine ⟨46364875907294511184305197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123639669086118696491480525 46364875907294511184305197)
        ·
          refine ⟨17386828465235441694114449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46364875907294511184305197 17386828465235441694114449)
          ·
            refine ⟨13040121348926581270585837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17386828465235441694114449 13040121348926581270585837)
            ·
              refine ⟨4890045505847467976469689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13040121348926581270585837 4890045505847467976469689)
              ·
                refine ⟨3667534129385600982352267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4890045505847467976469689 3667534129385600982352267)
                ·
                  refine ⟨5501301194078401473528401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667534129385600982352267 5501301194078401473528401)
                  ·
                    refine ⟨4125975895558801105146301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5501301194078401473528401 4125975895558801105146301)
                    ·
                      refine ⟨1547240960834550414429863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4125975895558801105146301 1547240960834550414429863)
                      ·
                        rfl

theorem cell23_3013241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_3013241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013241 prefixEnd_3013241 := by exact prefixLift 3013241
  have htrace : WordTrace (prefixWord ++ tailWord_3013241) baseStart_3013241 baseEnd_3013241 := by
    simpa [prefixWord, tailWord_3013241, baseEnd_3013241] using wordTrace_append hprefix tailTrace_3013241
  have hstable : (prefixWord ++ tailWord_3013241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013241).length < 2 ^ (prefixWord ++ tailWord_3013241).sum := by decide
  have hdescent : baseEnd_3013241 < baseStart_3013241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013258 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3013258 : Nat := 118140960795 + 3013258 * 2 ^ 59
def prefixEnd_3013258 : Nat := 4983230072969 + 3 ^ 40 * 3013258 * 2
def baseEnd_3013258 : Nat := 1547249690005676847917285

theorem tailTrace_3013258 : CollatzResearch.WordTrace tailWord_3013258 prefixEnd_3013258 1547249690005676847917285 := by
  unfold tailWord_3013258
  simp only [CollatzResearch.WordTrace]
  refine ⟨27475637029372091085060107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73268365411658909560160285 27475637029372091085060107)
  ·
    refine ⟨41213455544058136627590161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27475637029372091085060107 41213455544058136627590161)
    ·
      refine ⟨30910091658043602470692621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41213455544058136627590161 30910091658043602470692621)
      ·
        refine ⟨11591284371766350926509733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30910091658043602470692621 11591284371766350926509733)
        ·
          refine ⟨2173365819706190798720575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11591284371766350926509733 2173365819706190798720575)
          ·
            refine ⟨3260048729559286198080863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173365819706190798720575 3260048729559286198080863)
            ·
              refine ⟨4890073094338929297121295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260048729559286198080863 4890073094338929297121295)
              ·
                refine ⟨7335109641508393945681943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890073094338929297121295 7335109641508393945681943)
                ·
                  refine ⟨11002664462262590918522915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7335109641508393945681943 11002664462262590918522915)
                  ·
                    refine ⟨16503996693393886377784373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11002664462262590918522915 16503996693393886377784373)
                    ·
                      refine ⟨1547249690005676847917285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16503996693393886377784373 1547249690005676847917285)
                      ·
                        rfl

theorem cell23_3013258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3013258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013258 prefixEnd_3013258 := by exact prefixLift 3013258
  have htrace : WordTrace (prefixWord ++ tailWord_3013258) baseStart_3013258 baseEnd_3013258 := by
    simpa [prefixWord, tailWord_3013258, baseEnd_3013258] using wordTrace_append hprefix tailTrace_3013258
  have hstable : (prefixWord ++ tailWord_3013258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013258).length < 2 ^ (prefixWord ++ tailWord_3013258).sum := by decide
  have hdescent : baseEnd_3013258 < baseStart_3013258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013311 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 1, 4, 2]
def baseStart_3013311 : Nat := 118140960795 + 3013311 * 2 ^ 59
def prefixEnd_3013311 : Nat := 4983230072969 + 3 ^ 40 * 3013311 * 2
def baseEnd_3013311 : Nat := 1547276904480365140554541

theorem tailTrace_3013311 : CollatzResearch.WordTrace tailWord_3013311 prefixEnd_3013311 1547276904480365140554541 := by
  unfold tailWord_3013311
  simp only [CollatzResearch.WordTrace]
  refine ⟨109904481186296354391919787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73269654124197569594613191 109904481186296354391919787)
  ·
    refine ⟨164856721779444531587879681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109904481186296354391919787 164856721779444531587879681)
    ·
      refine ⟨123642541334583398690909761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164856721779444531587879681 123642541334583398690909761)
      ·
        refine ⟨92731906000937549018182321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123642541334583398690909761 92731906000937549018182321)
        ·
          refine ⟨69548929500703161763636741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92731906000937549018182321 69548929500703161763636741)
          ·
            refine ⟨13040424281381842830681889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69548929500703161763636741 13040424281381842830681889)
            ·
              refine ⟨9780318211036382123011417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13040424281381842830681889 9780318211036382123011417)
              ·
                refine ⟨7335238658277286592258563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9780318211036382123011417 7335238658277286592258563)
                ·
                  refine ⟨11002857987415929888387845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7335238658277286592258563 11002857987415929888387845)
                  ·
                    refine ⟨2063035872640486854072721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11002857987415929888387845 2063035872640486854072721)
                    ·
                      refine ⟨1547276904480365140554541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063035872640486854072721 1547276904480365140554541)
                      ·
                        rfl

theorem cell23_3013311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_3013311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013311 prefixEnd_3013311 := by exact prefixLift 3013311
  have htrace : WordTrace (prefixWord ++ tailWord_3013311) baseStart_3013311 baseEnd_3013311 := by
    simpa [prefixWord, tailWord_3013311, baseEnd_3013311] using wordTrace_append hprefix tailTrace_3013311
  have hstable : (prefixWord ++ tailWord_3013311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013311).length < 2 ^ (prefixWord ++ tailWord_3013311).sum := by decide
  have hdescent : baseEnd_3013311 < baseStart_3013311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013365 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3013365 : Nat := 118140960795 + 3013365 * 2 ^ 59
def prefixEnd_3013365 : Nat := 4983230072969 + 3 ^ 40 * 3013365 * 2
def baseEnd_3013365 : Nat := 1547304632435707929279293

theorem tailTrace_3013365 : CollatzResearch.WordTrace tailWord_3013365 prefixEnd_3013365 1547304632435707929279293 := by
  unfold tailWord_3013365
  simp only [CollatzResearch.WordTrace]
  refine ⟨109906450728100721614385549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73270967152067147742923699 109906450728100721614385549)
  ·
    refine ⟨41214919023037770605394581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109906450728100721614385549 41214919023037770605394581)
    ·
      refine ⟨1931949329204895497127871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41214919023037770605394581 1931949329204895497127871)
      ·
        refine ⟨2897923993807343245691807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931949329204895497127871 2897923993807343245691807)
        ·
          refine ⟨4346885990711014868537711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897923993807343245691807 4346885990711014868537711)
          ·
            refine ⟨6520328986066522302806567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346885990711014868537711 6520328986066522302806567)
            ·
              refine ⟨9780493479099783454209851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520328986066522302806567 9780493479099783454209851)
              ·
                refine ⟨14670740218649675181314777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9780493479099783454209851 14670740218649675181314777)
                ·
                  refine ⟨11003055163987256385986083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14670740218649675181314777 11003055163987256385986083)
                  ·
                    refine ⟨16504582745980884578979125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11003055163987256385986083 16504582745980884578979125)
                    ·
                      refine ⟨1547304632435707929279293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16504582745980884578979125 1547304632435707929279293)
                      ·
                        rfl

theorem cell23_3013365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3013365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013365 prefixEnd_3013365 := by exact prefixLift 3013365
  have htrace : WordTrace (prefixWord ++ tailWord_3013365) baseStart_3013365 baseEnd_3013365 := by
    simpa [prefixWord, tailWord_3013365, baseEnd_3013365] using wordTrace_append hprefix tailTrace_3013365
  have hstable : (prefixWord ++ tailWord_3013365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013365).length < 2 ^ (prefixWord ++ tailWord_3013365).sum := by decide
  have hdescent : baseEnd_3013365 < baseStart_3013365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013451 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 3]
def baseStart_3013451 : Nat := 118140960795 + 3013451 * 2 ^ 59
def prefixEnd_3013451 : Nat := 4983230072969 + 3 ^ 40 * 3013451 * 2
def baseEnd_3013451 : Nat := 1547348791771994592803897

theorem tailTrace_3013451 : CollatzResearch.WordTrace tailWord_3013451 prefixEnd_3013451 1547348791771994592803897 := by
  unfold tailWord_3013451
  simp only [CollatzResearch.WordTrace]
  refine ⟨109909587405789158302016207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73273058270526105534677471 109909587405789158302016207)
  ·
    refine ⟨164864381108683737453024311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109909587405789158302016207 164864381108683737453024311)
    ·
      refine ⟨247296571663025606179536467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164864381108683737453024311 247296571663025606179536467)
      ·
        refine ⟨370944857494538409269304701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247296571663025606179536467 370944857494538409269304701)
        ·
          refine ⟨139104321560451903475989263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370944857494538409269304701 139104321560451903475989263)
          ·
            refine ⟨208656482340677855213983895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139104321560451903475989263 208656482340677855213983895)
            ·
              refine ⟨312984723511016782820975843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208656482340677855213983895 312984723511016782820975843)
              ·
                refine ⟨469477085266525174231463765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312984723511016782820975843 469477085266525174231463765)
                ·
                  refine ⟨2750842296483545942762483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 469477085266525174231463765 2750842296483545942762483)
                  ·
                    refine ⟨4126263444725318914143725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2750842296483545942762483 4126263444725318914143725)
                    ·
                      refine ⟨1547348791771994592803897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4126263444725318914143725 1547348791771994592803897)
                      ·
                        rfl

theorem cell23_3013451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 3].length) (baseStart_3013451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013451 prefixEnd_3013451 := by exact prefixLift 3013451
  have htrace : WordTrace (prefixWord ++ tailWord_3013451) baseStart_3013451 baseEnd_3013451 := by
    simpa [prefixWord, tailWord_3013451, baseEnd_3013451] using wordTrace_append hprefix tailTrace_3013451
  have hstable : (prefixWord ++ tailWord_3013451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013451).length < 2 ^ (prefixWord ++ tailWord_3013451).sum := by decide
  have hdescent : baseEnd_3013451 < baseStart_3013451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013471 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 1, 5]
def baseStart_3013471 : Nat := 118140960795 + 3013471 * 2 ^ 59
def prefixEnd_3013471 : Nat := 4983230072969 + 3 ^ 40 * 3013471 * 2
def baseEnd_3013471 : Nat := 515786353795028171517935

theorem tailTrace_3013471 : CollatzResearch.WordTrace tailWord_3013471 prefixEnd_3013471 515786353795028171517935 := by
  unfold tailWord_3013471
  simp only [CollatzResearch.WordTrace]
  refine ⟨109910316865716701717744267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73273544577144467811829511 109910316865716701717744267)
  ·
    refine ⟨164865475298575052576616401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109910316865716701717744267 164865475298575052576616401)
    ·
      refine ⟨123649106473931289432462301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164865475298575052576616401 123649106473931289432462301)
      ·
        refine ⟨46368414927724233537173363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123649106473931289432462301 46368414927724233537173363)
        ·
          refine ⟨69552622391586350305760045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46368414927724233537173363 69552622391586350305760045)
          ·
            refine ⟨26082233396844881364660017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69552622391586350305760045 26082233396844881364660017)
            ·
              refine ⟨19561675047633661023495013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26082233396844881364660017 19561675047633661023495013)
              ·
                refine ⟨3667814071431311441905315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19561675047633661023495013 3667814071431311441905315)
                ·
                  refine ⟨5501721107146967162857973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667814071431311441905315 5501721107146967162857973)
                  ·
                    refine ⟨515786353795028171517935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5501721107146967162857973 515786353795028171517935)
                    ·
                      rfl

theorem cell23_3013471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_3013471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013471 prefixEnd_3013471 := by exact prefixLift 3013471
  have htrace : WordTrace (prefixWord ++ tailWord_3013471) baseStart_3013471 baseEnd_3013471 := by
    simpa [prefixWord, tailWord_3013471, baseEnd_3013471] using wordTrace_append hprefix tailTrace_3013471
  have hstable : (prefixWord ++ tailWord_3013471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013471).length < 2 ^ (prefixWord ++ tailWord_3013471).sum := by decide
  have hdescent : baseEnd_3013471 < baseStart_3013471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013488 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 1, 5]
def baseStart_3013488 : Nat := 118140960795 + 3013488 * 2 ^ 59
def prefixEnd_3013488 : Nat := 4983230072969 + 3 ^ 40 * 3013488 * 2
def baseEnd_3013488 : Nat := 515789263518736982680409

theorem tailTrace_3013488 : CollatzResearch.WordTrace tailWord_3013488 prefixEnd_3013488 515789263518736982680409 := by
  unfold tailWord_3013488
  simp only [CollatzResearch.WordTrace]
  refine ⟨54955468453327556810556559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73273957937770075747408745 54955468453327556810556559)
  ·
    refine ⟨82433202679991335215834839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54955468453327556810556559 82433202679991335215834839)
    ·
      refine ⟨123649804019987002823752259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82433202679991335215834839 123649804019987002823752259)
      ·
        refine ⟨185474706029980504235628389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123649804019987002823752259 185474706029980504235628389)
        ·
          refine ⟨34776507380621344544180323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185474706029980504235628389 34776507380621344544180323)
          ·
            refine ⟨52164761070932016816270485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34776507380621344544180323 52164761070932016816270485)
            ·
              refine ⟨2445223175199938288262679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52164761070932016816270485 2445223175199938288262679)
              ·
                refine ⟨3667834762799907432394019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445223175199938288262679 3667834762799907432394019)
                ·
                  refine ⟨5501752144199861148591029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667834762799907432394019 5501752144199861148591029)
                  ·
                    refine ⟨515789263518736982680409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5501752144199861148591029 515789263518736982680409)
                    ·
                      rfl

theorem cell23_3013488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 5].length) (baseStart_3013488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013488 prefixEnd_3013488 := by exact prefixLift 3013488
  have htrace : WordTrace (prefixWord ++ tailWord_3013488) baseStart_3013488 baseEnd_3013488 := by
    simpa [prefixWord, tailWord_3013488, baseEnd_3013488] using wordTrace_append hprefix tailTrace_3013488
  have hstable : (prefixWord ++ tailWord_3013488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013488).length < 2 ^ (prefixWord ++ tailWord_3013488).sum := by decide
  have hdescent : baseEnd_3013488 < baseStart_3013488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013511 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3013511 : Nat := 118140960795 + 3013511 * 2 ^ 59
def prefixEnd_3013511 : Nat := 4983230072969 + 3 ^ 40 * 3013511 * 2
def baseEnd_3013511 : Nat := 1547379600611264358053621

theorem tailTrace_3013511 : CollatzResearch.WordTrace tailWord_3013511 prefixEnd_3013511 1547379600611264358053621 := by
  unfold tailWord_3013511
  simp only [CollatzResearch.WordTrace]
  refine ⟨109911775785571788549200387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73274517190381192366133591 109911775785571788549200387)
  ·
    refine ⟨164867663678357682823800581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109911775785571788549200387 164867663678357682823800581)
    ·
      refine ⟨30912686939692065529462609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164867663678357682823800581 30912686939692065529462609)
      ·
        refine ⟨23184515204769049147096957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30912686939692065529462609 23184515204769049147096957)
        ·
          refine ⟨8694193201788393430161359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23184515204769049147096957 8694193201788393430161359)
          ·
            refine ⟨13041289802682590145242039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8694193201788393430161359 13041289802682590145242039)
            ·
              refine ⟨19561934704023885217863059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13041289802682590145242039 19561934704023885217863059)
              ·
                refine ⟨29342902056035827826794589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19561934704023885217863059 29342902056035827826794589)
                ·
                  refine ⟨11003588271013435435047971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29342902056035827826794589 11003588271013435435047971)
                  ·
                    refine ⟨16505382406520153152571957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11003588271013435435047971 16505382406520153152571957)
                    ·
                      refine ⟨1547379600611264358053621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16505382406520153152571957 1547379600611264358053621)
                      ·
                        rfl

theorem cell23_3013511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3013511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013511 prefixEnd_3013511 := by exact prefixLift 3013511
  have htrace : WordTrace (prefixWord ++ tailWord_3013511) baseStart_3013511 baseEnd_3013511 := by
    simpa [prefixWord, tailWord_3013511, baseEnd_3013511] using wordTrace_append hprefix tailTrace_3013511
  have hstable : (prefixWord ++ tailWord_3013511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013511).length < 2 ^ (prefixWord ++ tailWord_3013511).sum := by decide
  have hdescent : baseEnd_3013511 < baseStart_3013511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013525 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_3013525 : Nat := 118140960795 + 3013525 * 2 ^ 59
def prefixEnd_3013525 : Nat := 4983230072969 + 3 ^ 40 * 3013525 * 2
def baseEnd_3013525 : Nat := 1547386789340427303278557

theorem tailTrace_3013525 : CollatzResearch.WordTrace tailWord_3013525 prefixEnd_3013525 1547386789340427303278557 := by
  unfold tailWord_3013525
  simp only [CollatzResearch.WordTrace]
  refine ⟨109912286407521068940210029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73274857605014045960140019 109912286407521068940210029)
  ·
    refine ⟨41217107402820400852578761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109912286407521068940210029 41217107402820400852578761)
    ·
      refine ⟨30912830552115300639434071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41217107402820400852578761 30912830552115300639434071)
      ·
        refine ⟨46369245828172950959151107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30912830552115300639434071 46369245828172950959151107)
        ·
          refine ⟨69553868742259426438726661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46369245828172950959151107 69553868742259426438726661)
          ·
            refine ⟨13041350389173642457261249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69553868742259426438726661 13041350389173642457261249)
            ·
              refine ⟨9781012791880231842945937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13041350389173642457261249 9781012791880231842945937)
              ·
                refine ⟨7335759593910173882209453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9781012791880231842945937 7335759593910173882209453)
                ·
                  refine ⟨2750909847716315205828545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7335759593910173882209453 2750909847716315205828545)
                  ·
                    refine ⟨2063182385787236404371409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2750909847716315205828545 2063182385787236404371409)
                    ·
                      refine ⟨1547386789340427303278557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063182385787236404371409 1547386789340427303278557)
                      ·
                        rfl

theorem cell23_3013525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_3013525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013525 prefixEnd_3013525 := by exact prefixLift 3013525
  have htrace : WordTrace (prefixWord ++ tailWord_3013525) baseStart_3013525 baseEnd_3013525 := by
    simpa [prefixWord, tailWord_3013525, baseEnd_3013525] using wordTrace_append hprefix tailTrace_3013525
  have hstable : (prefixWord ++ tailWord_3013525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013525).length < 2 ^ (prefixWord ++ tailWord_3013525).sum := by decide
  have hdescent : baseEnd_3013525 < baseStart_3013525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013628 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_3013628 : Nat := 118140960795 + 3013628 * 2 ^ 59
def prefixEnd_3013628 : Nat := 4983230072969 + 3 ^ 40 * 3013628 * 2
def baseEnd_3013628 : Nat := 1547439677847840400290583

theorem tailTrace_3013628 : CollatzResearch.WordTrace tailWord_3013628 prefixEnd_3013628 1547439677847840400290583 := by
  unfold tailWord_3013628
  simp only [CollatzResearch.WordTrace]
  refine ⟨54958021563073958765604769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73277362084098611687473025 54958021563073958765604769)
  ·
    refine ⟨41218516172305469074203577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54958021563073958765604769 41218516172305469074203577)
    ·
      refine ⟨30913887129229101805652683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41218516172305469074203577 30913887129229101805652683)
      ·
        refine ⟨46370830693843652708479025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30913887129229101805652683 46370830693843652708479025)
        ·
          refine ⟨34778123020382739531359269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46370830693843652708479025 34778123020382739531359269)
          ·
            refine ⟨6520898066321763662129863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34778123020382739531359269 6520898066321763662129863)
            ·
              refine ⟨9781347099482645493194795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520898066321763662129863 9781347099482645493194795)
              ·
                refine ⟨14672020649223968239792193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9781347099482645493194795 14672020649223968239792193)
                ·
                  refine ⟨11004015486917976179844145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14672020649223968239792193 11004015486917976179844145)
                  ·
                    refine ⟨8253011615188482134883109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11004015486917976179844145 8253011615188482134883109)
                    ·
                      refine ⟨1547439677847840400290583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8253011615188482134883109 1547439677847840400290583)
                      ·
                        rfl

theorem cell23_3013628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_3013628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013628 prefixEnd_3013628 := by exact prefixLift 3013628
  have htrace : WordTrace (prefixWord ++ tailWord_3013628) baseStart_3013628 baseEnd_3013628 := by
    simpa [prefixWord, tailWord_3013628, baseEnd_3013628] using wordTrace_append hprefix tailTrace_3013628
  have hstable : (prefixWord ++ tailWord_3013628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013628).length < 2 ^ (prefixWord ++ tailWord_3013628).sum := by decide
  have hdescent : baseEnd_3013628 < baseStart_3013628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013655 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 5]
def baseStart_3013655 : Nat := 118140960795 + 3013655 * 2 ^ 59
def prefixEnd_3013655 : Nat := 4983230072969 + 3 ^ 40 * 3013655 * 2
def baseEnd_3013655 : Nat := 171939282425056866072551

theorem tailTrace_3013655 : CollatzResearch.WordTrace tailWord_3013655 prefixEnd_3013655 171939282425056866072551 := by
  unfold tailWord_3013655
  simp only [CollatzResearch.WordTrace]
  refine ⟨109917027897050101142442419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73278018598033400761628279 109917027897050101142442419)
  ·
    refine ⟨164875541845575151713663629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109917027897050101142442419 164875541845575151713663629)
    ·
      refine ⟨61828328192090681892623861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164875541845575151713663629 61828328192090681892623861)
      ·
        refine ⟨5796405768008501427433487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61828328192090681892623861 5796405768008501427433487)
        ·
          refine ⟨8694608652012752141150231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796405768008501427433487 8694608652012752141150231)
          ·
            refine ⟨13041912978019128211725347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8694608652012752141150231 13041912978019128211725347)
            ·
              refine ⟨19562869467028692317588021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13041912978019128211725347 19562869467028692317588021)
              ·
                refine ⟨1834019012533939904773877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19562869467028692317588021 1834019012533939904773877)
                ·
                  refine ⟨171939282425056866072551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1834019012533939904773877 171939282425056866072551)
                  ·
                    rfl

theorem cell23_3013655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 5].length) (baseStart_3013655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013655 prefixEnd_3013655 := by exact prefixLift 3013655
  have htrace : WordTrace (prefixWord ++ tailWord_3013655) baseStart_3013655 baseEnd_3013655 := by
    simpa [prefixWord, tailWord_3013655, baseEnd_3013655] using wordTrace_append hprefix tailTrace_3013655
  have hstable : (prefixWord ++ tailWord_3013655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013655).length < 2 ^ (prefixWord ++ tailWord_3013655).sum := by decide
  have hdescent : baseEnd_3013655 < baseStart_3013655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013678 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3013678 : Nat := 118140960795 + 3013678 * 2 ^ 59
def prefixEnd_3013678 : Nat := 4983230072969 + 3 ^ 40 * 3013678 * 2
def baseEnd_3013678 : Nat := 1547465351880565204665353

theorem tailTrace_3013678 : CollatzResearch.WordTrace tailWord_3013678 prefixEnd_3013678 1547465351880565204665353 := by
  unfold tailWord_3013678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13739733346995847008816211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73278577850644517380353125 13739733346995847008816211)
  ·
    refine ⟨20609600020493770513224317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13739733346995847008816211 20609600020493770513224317)
    ·
      refine ⟨7728600007685163942459119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20609600020493770513224317 7728600007685163942459119)
      ·
        refine ⟨11592900011527745913688679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7728600007685163942459119 11592900011527745913688679)
        ·
          refine ⟨17389350017291618870533019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11592900011527745913688679 17389350017291618870533019)
          ·
            refine ⟨26084025025937428305799529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17389350017291618870533019 26084025025937428305799529)
            ·
              refine ⟨19563018769453071229349647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26084025025937428305799529 19563018769453071229349647)
              ·
                refine ⟨29344528154179606844024471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19563018769453071229349647 29344528154179606844024471)
                ·
                  refine ⟨44016792231269410266036707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29344528154179606844024471 44016792231269410266036707)
                  ·
                    refine ⟨66025188346904115399055061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44016792231269410266036707 66025188346904115399055061)
                    ·
                      refine ⟨1547465351880565204665353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66025188346904115399055061 1547465351880565204665353)
                      ·
                        rfl

theorem cell23_3013678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3013678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013678 prefixEnd_3013678 := by exact prefixLift 3013678
  have htrace : WordTrace (prefixWord ++ tailWord_3013678) baseStart_3013678 baseEnd_3013678 := by
    simpa [prefixWord, tailWord_3013678, baseEnd_3013678] using wordTrace_append hprefix tailTrace_3013678
  have hstable : (prefixWord ++ tailWord_3013678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013678).length < 2 ^ (prefixWord ++ tailWord_3013678).sum := by decide
  have hdescent : baseEnd_3013678 < baseStart_3013678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013688 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3013688 : Nat := 118140960795 + 3013688 * 2 ^ 59
def prefixEnd_3013688 : Nat := 4983230072969 + 3 ^ 40 * 3013688 * 2
def baseEnd_3013688 : Nat := 1547470486687110165540307

theorem tailTrace_3013688 : CollatzResearch.WordTrace tailWord_3013688 prefixEnd_3013688 1547470486687110165540307 := by
  unfold tailWord_3013688
  simp only [CollatzResearch.WordTrace]
  refine ⟨54959115752965273889196859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73278821003953698518929145 54959115752965273889196859)
  ·
    refine ⟨82438673629447910833795289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54959115752965273889196859 82438673629447910833795289)
    ·
      refine ⟨61829005222085933125346467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82438673629447910833795289 61829005222085933125346467)
      ·
        refine ⟨92743507833128899688019701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61829005222085933125346467 92743507833128899688019701)
        ·
          refine ⟨8694703859355834345751847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92743507833128899688019701 8694703859355834345751847)
          ·
            refine ⟨13042055789033751518627771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8694703859355834345751847 13042055789033751518627771)
            ·
              refine ⟨19563083683550627277941657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13042055789033751518627771 19563083683550627277941657)
              ·
                refine ⟨14672312762662970458456243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19563083683550627277941657 14672312762662970458456243)
                ·
                  refine ⟨22008469143994455687684365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14672312762662970458456243 22008469143994455687684365)
                  ·
                    refine ⟨8253175928997920882881637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22008469143994455687684365 8253175928997920882881637)
                    ·
                      refine ⟨1547470486687110165540307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8253175928997920882881637 1547470486687110165540307)
                      ·
                        rfl

theorem cell23_3013688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3013688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013688 prefixEnd_3013688 := by exact prefixLift 3013688
  have htrace : WordTrace (prefixWord ++ tailWord_3013688) baseStart_3013688 baseEnd_3013688 := by
    simpa [prefixWord, tailWord_3013688, baseEnd_3013688] using wordTrace_append hprefix tailTrace_3013688
  have hstable : (prefixWord ++ tailWord_3013688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013688).length < 2 ^ (prefixWord ++ tailWord_3013688).sum := by decide
  have hdescent : baseEnd_3013688 < baseStart_3013688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013728 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 6]
def baseStart_3013728 : Nat := 118140960795 + 3013728 * 2 ^ 59
def prefixEnd_3013728 : Nat := 4983230072969 + 3 ^ 40 * 3013728 * 2
def baseEnd_3013728 : Nat := 171943447323698889893347

theorem tailTrace_3013728 : CollatzResearch.WordTrace tailWord_3013728 prefixEnd_3013728 171943447323698889893347 := by
  unfold tailWord_3013728
  simp only [CollatzResearch.WordTrace]
  refine ⟨54959845212892817304924919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73279793617190423073233225 54959845212892817304924919)
  ·
    refine ⟨82439767819339225957387379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54959845212892817304924919 82439767819339225957387379)
    ·
      refine ⟨123659651729008838936081069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82439767819339225957387379 123659651729008838936081069)
      ·
        refine ⟨46372369398378314601030401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123659651729008838936081069 46372369398378314601030401)
        ·
          refine ⟨34779277048783735950772801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46372369398378314601030401 34779277048783735950772801)
          ·
            refine ⟨26084457786587801963079601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34779277048783735950772801 26084457786587801963079601)
            ·
              refine ⟨19563343339940851472309701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26084457786587801963079601 19563343339940851472309701)
              ·
                refine ⟨3668126876238909651058069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19563343339940851472309701 3668126876238909651058069)
                ·
                  refine ⟨171943447323698889893347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3668126876238909651058069 171943447323698889893347)
                  ·
                    rfl

theorem cell23_3013728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_3013728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013728 prefixEnd_3013728 := by exact prefixLift 3013728
  have htrace : WordTrace (prefixWord ++ tailWord_3013728) baseStart_3013728 baseEnd_3013728 := by
    simpa [prefixWord, tailWord_3013728, baseEnd_3013728] using wordTrace_append hprefix tailTrace_3013728
  have hstable : (prefixWord ++ tailWord_3013728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013728).length < 2 ^ (prefixWord ++ tailWord_3013728).sum := by decide
  have hdescent : baseEnd_3013728 < baseStart_3013728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013755 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 3]
def baseStart_3013755 : Nat := 118140960795 + 3013755 * 2 ^ 59
def prefixEnd_3013755 : Nat := 4983230072969 + 3 ^ 40 * 3013755 * 2
def baseEnd_3013755 : Nat := 1547504889890961403402499

theorem tailTrace_3013755 : CollatzResearch.WordTrace tailWord_3013755 prefixEnd_3013755 1547504889890961403402499 := by
  unfold tailWord_3013755
  simp only [CollatzResearch.WordTrace]
  refine ⟨109920675196687818221082719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73280450131125212147388479 109920675196687818221082719)
  ·
    refine ⟨164881012795031727331624079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109920675196687818221082719 164881012795031727331624079)
    ·
      refine ⟨247321519192547590997436119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164881012795031727331624079 247321519192547590997436119)
      ·
        refine ⟨370982278788821386496154179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247321519192547590997436119 370982278788821386496154179)
        ·
          refine ⟨556473418183232079744231269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370982278788821386496154179 556473418183232079744231269)
          ·
            refine ⟨104338765909356014952043363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 556473418183232079744231269 104338765909356014952043363)
            ·
              refine ⟨156508148864034022428065045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104338765909356014952043363 156508148864034022428065045)
              ·
                refine ⟨7336319478001594801315549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156508148864034022428065045 7336319478001594801315549)
                ·
                  refine ⟨2751119804250598050493331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7336319478001594801315549 2751119804250598050493331)
                  ·
                    refine ⟨4126679706375897075739997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2751119804250598050493331 4126679706375897075739997)
                    ·
                      refine ⟨1547504889890961403402499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4126679706375897075739997 1547504889890961403402499)
                      ·
                        rfl

theorem cell23_3013755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 3].length) (baseStart_3013755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013755 prefixEnd_3013755 := by exact prefixLift 3013755
  have htrace : WordTrace (prefixWord ++ tailWord_3013755) baseStart_3013755 baseEnd_3013755 := by
    simpa [prefixWord, tailWord_3013755, baseEnd_3013755] using wordTrace_append hprefix tailTrace_3013755
  have hstable : (prefixWord ++ tailWord_3013755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013755).length < 2 ^ (prefixWord ++ tailWord_3013755).sum := by decide
  have hdescent : baseEnd_3013755 < baseStart_3013755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013789 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_3013789 : Nat := 118140960795 + 3013789 * 2 ^ 59
def prefixEnd_3013789 : Nat := 4983230072969 + 3 ^ 40 * 3013789 * 2
def baseEnd_3013789 : Nat := 1547522348233214270377343

theorem tailTrace_3013789 : CollatzResearch.WordTrace tailWord_3013789 prefixEnd_3013789 1547522348233214270377343 := by
  unfold tailWord_3013789
  simp only [CollatzResearch.WordTrace]
  refine ⟨109921915278564642027820421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73281276852376428018546947 109921915278564642027820421)
  ·
    refine ⟨20610359114730870380216329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109921915278564642027820421 20610359114730870380216329)
    ·
      refine ⟨15457769336048152785162247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20610359114730870380216329 15457769336048152785162247)
      ·
        refine ⟨23186654004072229177743371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15457769336048152785162247 23186654004072229177743371)
        ·
          refine ⟨34779981006108343766615057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23186654004072229177743371 34779981006108343766615057)
          ·
            refine ⟨26084985754581257824961293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34779981006108343766615057 26084985754581257824961293)
            ·
              refine ⟨9781869657967971684360485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26084985754581257824961293 9781869657967971684360485)
              ·
                refine ⟨1834100560868994690817591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9781869657967971684360485 1834100560868994690817591)
                ·
                  refine ⟨2751150841303492036226387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834100560868994690817591 2751150841303492036226387)
                  ·
                    refine ⟨4126726261955238054339581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2751150841303492036226387 4126726261955238054339581)
                    ·
                      refine ⟨1547522348233214270377343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4126726261955238054339581 1547522348233214270377343)
                      ·
                        rfl

theorem cell23_3013789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_3013789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013789 prefixEnd_3013789 := by exact prefixLift 3013789
  have htrace : WordTrace (prefixWord ++ tailWord_3013789) baseStart_3013789 baseEnd_3013789 := by
    simpa [prefixWord, tailWord_3013789, baseEnd_3013789] using wordTrace_append hprefix tailTrace_3013789
  have hstable : (prefixWord ++ tailWord_3013789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013789).length < 2 ^ (prefixWord ++ tailWord_3013789).sum := by decide
  have hdescent : baseEnd_3013789 < baseStart_3013789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013808 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_3013808 : Nat := 118140960795 + 3013808 * 2 ^ 59
def prefixEnd_3013808 : Nat := 4983230072969 + 3 ^ 40 * 3013808 * 2
def baseEnd_3013808 : Nat := 1547532104365649696039755

theorem tailTrace_3013808 : CollatzResearch.WordTrace tailWord_3013808 prefixEnd_3013808 1547532104365649696039755 := by
  unfold tailWord_3013808
  simp only [CollatzResearch.WordTrace]
  refine ⟨54961304132747904136381039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73281738843663872181841385 54961304132747904136381039)
  ·
    refine ⟨82441956199121856204571559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54961304132747904136381039 82441956199121856204571559)
    ·
      refine ⟨123662934298682784306857339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82441956199121856204571559 123662934298682784306857339)
      ·
        refine ⟨185494401448024176460286009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123662934298682784306857339 185494401448024176460286009)
        ·
          refine ⟨139120801086018132345214507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185494401448024176460286009 139120801086018132345214507)
          ·
            refine ⟨208681201629027198517821761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139120801086018132345214507 208681201629027198517821761)
            ·
              refine ⟨156510901221770398888366321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208681201629027198517821761 156510901221770398888366321)
              ·
                refine ⟨117383175916327799166274741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156510901221770398888366321 117383175916327799166274741)
                ·
                  refine ⟨11004672742155731171838257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117383175916327799166274741 11004672742155731171838257)
                  ·
                    refine ⟨8253504556616798378878693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11004672742155731171838257 8253504556616798378878693)
                    ·
                      refine ⟨1547532104365649696039755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8253504556616798378878693 1547532104365649696039755)
                      ·
                        rfl

theorem cell23_3013808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_3013808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013808 prefixEnd_3013808 := by exact prefixLift 3013808
  have htrace : WordTrace (prefixWord ++ tailWord_3013808) baseStart_3013808 baseEnd_3013808 := by
    simpa [prefixWord, tailWord_3013808, baseEnd_3013808] using wordTrace_append hprefix tailTrace_3013808
  have hstable : (prefixWord ++ tailWord_3013808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013808).length < 2 ^ (prefixWord ++ tailWord_3013808).sum := by decide
  have hdescent : baseEnd_3013808 < baseStart_3013808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013815 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_3013815 : Nat := 118140960795 + 3013815 * 2 ^ 59
def prefixEnd_3013815 : Nat := 4983230072969 + 3 ^ 40 * 3013815 * 2
def baseEnd_3013815 : Nat := 1547535698730231168652223

theorem tailTrace_3013815 : CollatzResearch.WordTrace tailWord_3013815 prefixEnd_3013815 1547535698730231168652223 := by
  unfold tailWord_3013815
  simp only [CollatzResearch.WordTrace]
  refine ⟨109922863576470448468266899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73281909050980298978844599 109922863576470448468266899)
  ·
    refine ⟨164884295364705672702400349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109922863576470448468266899 164884295364705672702400349)
    ·
      refine ⟨61831610761764627263400131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164884295364705672702400349 61831610761764627263400131)
      ·
        refine ⟨92747416142646940895100197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61831610761764627263400131 92747416142646940895100197)
        ·
          refine ⟨17390140526746301417831287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92747416142646940895100197 17390140526746301417831287)
          ·
            refine ⟨26085210790119452126746931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17390140526746301417831287 26085210790119452126746931)
            ·
              refine ⟨39127816185179178190120397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26085210790119452126746931 39127816185179178190120397)
              ·
                refine ⟨14672931069442191821295149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39127816185179178190120397 14672931069442191821295149)
                ·
                  refine ⟨5502349151040821932985681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14672931069442191821295149 5502349151040821932985681)
                  ·
                    refine ⟨4126761863280616449739261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5502349151040821932985681 4126761863280616449739261)
                    ·
                      refine ⟨1547535698730231168652223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4126761863280616449739261 1547535698730231168652223)
                      ·
                        rfl

theorem cell23_3013815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_3013815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013815 prefixEnd_3013815 := by exact prefixLift 3013815
  have htrace : WordTrace (prefixWord ++ tailWord_3013815) baseStart_3013815 baseEnd_3013815 := by
    simpa [prefixWord, tailWord_3013815, baseEnd_3013815] using wordTrace_append hprefix tailTrace_3013815
  have hstable : (prefixWord ++ tailWord_3013815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013815).length < 2 ^ (prefixWord ++ tailWord_3013815).sum := by decide
  have hdescent : baseEnd_3013815 < baseStart_3013815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013826 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3013826 : Nat := 118140960795 + 3013826 * 2 ^ 59
def prefixEnd_3013826 : Nat := 4983230072969 + 3 ^ 40 * 3013826 * 2
def baseEnd_3013826 : Nat := 515847115672476875204891

theorem tailTrace_3013826 : CollatzResearch.WordTrace tailWord_3013826 prefixEnd_3013826 515847115672476875204891 := by
  unfold tailWord_3013826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27480816194857649336729333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73282176519620398231278221 27480816194857649336729333)
  ·
    refine ⟨2576326518267904625318375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27480816194857649336729333 2576326518267904625318375)
    ·
      refine ⟨3864489777401856937977563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576326518267904625318375 3864489777401856937977563)
      ·
        refine ⟨5796734666102785406966345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3864489777401856937977563 5796734666102785406966345)
        ·
          refine ⟨4347550999577089055224759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5796734666102785406966345 4347550999577089055224759)
          ·
            refine ⟨6521326499365633582837139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347550999577089055224759 6521326499365633582837139)
            ·
              refine ⟨9781989749048450374255709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521326499365633582837139 9781989749048450374255709)
              ·
                refine ⟨3668246155893168890345891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9781989749048450374255709 3668246155893168890345891)
                ·
                  refine ⟨5502369233839753335518837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668246155893168890345891 5502369233839753335518837)
                  ·
                    refine ⟨515847115672476875204891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5502369233839753335518837 515847115672476875204891)
                    ·
                      rfl

theorem cell23_3013826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3013826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013826 prefixEnd_3013826 := by exact prefixLift 3013826
  have htrace : WordTrace (prefixWord ++ tailWord_3013826) baseStart_3013826 baseEnd_3013826 := by
    simpa [prefixWord, tailWord_3013826, baseEnd_3013826] using wordTrace_append hprefix tailTrace_3013826
  have hstable : (prefixWord ++ tailWord_3013826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013826).length < 2 ^ (prefixWord ++ tailWord_3013826).sum := by decide
  have hdescent : baseEnd_3013826 < baseStart_3013826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013889 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_3013889 : Nat := 118140960795 + 3013889 * 2 ^ 59
def prefixEnd_3013889 : Nat := 4983230072969 + 3 ^ 40 * 3013889 * 2
def baseEnd_3013889 : Nat := 1547573696298663879126883

theorem tailTrace_3013889 : CollatzResearch.WordTrace tailWord_3013889 prefixEnd_3013889 1547573696298663879126883 := by
  unfold tailWord_3013889
  simp only [CollatzResearch.WordTrace]
  refine ⟨109925562578202359106460721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73283708385468239404307147 109925562578202359106460721)
  ·
    refine ⟨82444171933651769329845541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109925562578202359106460721 82444171933651769329845541)
    ·
      refine ⟨15458282237559706749346039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82444171933651769329845541 15458282237559706749346039)
      ·
        refine ⟨23187423356339560124019059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15458282237559706749346039 23187423356339560124019059)
        ·
          refine ⟨34781135034509340186028589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23187423356339560124019059 34781135034509340186028589)
          ·
            refine ⟨13042925637941002569760721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34781135034509340186028589 13042925637941002569760721)
            ·
              refine ⟨9782194228455751927320541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13042925637941002569760721 9782194228455751927320541)
              ·
                refine ⟨3668322835670906972745203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9782194228455751927320541 3668322835670906972745203)
                ·
                  refine ⟨5502484253506360459117805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668322835670906972745203 5502484253506360459117805)
                  ·
                    refine ⟨2063431595064885172169177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5502484253506360459117805 2063431595064885172169177)
                    ·
                      refine ⟨1547573696298663879126883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063431595064885172169177 1547573696298663879126883)
                      ·
                        rfl

theorem cell23_3013889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_3013889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013889 prefixEnd_3013889 := by exact prefixLift 3013889
  have htrace : WordTrace (prefixWord ++ tailWord_3013889) baseStart_3013889 baseEnd_3013889 := by
    simpa [prefixWord, tailWord_3013889, baseEnd_3013889] using wordTrace_append hprefix tailTrace_3013889
  have hstable : (prefixWord ++ tailWord_3013889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013889).length < 2 ^ (prefixWord ++ tailWord_3013889).sum := by decide
  have hdescent : baseEnd_3013889 < baseStart_3013889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013905 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_3013905 : Nat := 118140960795 + 3013905 * 2 ^ 59
def prefixEnd_3013905 : Nat := 4983230072969 + 3 ^ 40 * 3013905 * 2
def baseEnd_3013905 : Nat := 1547581911989135816526809

theorem tailTrace_3013905 : CollatzResearch.WordTrace tailWord_3013905 prefixEnd_3013905 1547581911989135816526809 := by
  unfold tailWord_3013905
  simp only [CollatzResearch.WordTrace]
  refine ⟨109926146146144393839043169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73284097430762929226028779 109926146146144393839043169)
  ·
    refine ⟨82444609609608295379282377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109926146146144393839043169 82444609609608295379282377)
    ·
      refine ⟨61833457207206221534461783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82444609609608295379282377 61833457207206221534461783)
      ·
        refine ⟨92750185810809332301692675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61833457207206221534461783 92750185810809332301692675)
        ·
          refine ⟨139125278716213998452539013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92750185810809332301692675 139125278716213998452539013)
          ·
            refine ⟨26085989759290124709851065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139125278716213998452539013 26085989759290124709851065)
            ·
              refine ⟨19564492319467593532388299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26085989759290124709851065 19564492319467593532388299)
              ·
                refine ⟨29346738479201390298582449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19564492319467593532388299 29346738479201390298582449)
                ·
                  refine ⟨22010053859401042723936837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29346738479201390298582449 22010053859401042723936837)
                  ·
                    refine ⟨4126885098637695510738157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22010053859401042723936837 4126885098637695510738157)
                    ·
                      refine ⟨1547581911989135816526809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4126885098637695510738157 1547581911989135816526809)
                      ·
                        rfl

theorem cell23_3013905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_3013905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013905 prefixEnd_3013905 := by exact prefixLift 3013905
  have htrace : WordTrace (prefixWord ++ tailWord_3013905) baseStart_3013905 baseEnd_3013905 := by
    simpa [prefixWord, tailWord_3013905, baseEnd_3013905] using wordTrace_append hprefix tailTrace_3013905
  have hstable : (prefixWord ++ tailWord_3013905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013905).length < 2 ^ (prefixWord ++ tailWord_3013905).sum := by decide
  have hdescent : baseEnd_3013905 < baseStart_3013905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013935 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_3013935 : Nat := 118140960795 + 3013935 * 2 ^ 59
def prefixEnd_3013935 : Nat := 4983230072969 + 3 ^ 40 * 3013935 * 2
def baseEnd_3013935 : Nat := 1547597316408770699151671

theorem tailTrace_3013935 : CollatzResearch.WordTrace tailWord_3013935 prefixEnd_3013935 1547597316408770699151671 := by
  unfold tailWord_3013935
  simp only [CollatzResearch.WordTrace]
  refine ⟨109927240336035708962635259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73284826890690472641756839 109927240336035708962635259)
  ·
    refine ⟨164890860504053563443952889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109927240336035708962635259 164890860504053563443952889)
    ·
      refine ⟨123668145378040172582964667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164890860504053563443952889 123668145378040172582964667)
      ·
        refine ⟨185502218067060258874447001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123668145378040172582964667 185502218067060258874447001)
        ·
          refine ⟨139126663550295194155835251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185502218067060258874447001 139126663550295194155835251)
          ·
            refine ⟨208689995325442791233752877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139126663550295194155835251 208689995325442791233752877)
            ·
              refine ⟨78258748247041046712657329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208689995325442791233752877 78258748247041046712657329)
              ·
                refine ⟨58694061185280785034492997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78258748247041046712657329 58694061185280785034492997)
                ·
                  refine ⟨11005136472240147193967437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58694061185280785034492997 11005136472240147193967437)
                  ·
                    refine ⟨4126926177090055197737789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11005136472240147193967437 4126926177090055197737789)
                    ·
                      refine ⟨1547597316408770699151671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4126926177090055197737789 1547597316408770699151671)
                      ·
                        rfl

theorem cell23_3013935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_3013935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013935 prefixEnd_3013935 := by exact prefixLift 3013935
  have htrace : WordTrace (prefixWord ++ tailWord_3013935) baseStart_3013935 baseEnd_3013935 := by
    simpa [prefixWord, tailWord_3013935, baseEnd_3013935] using wordTrace_append hprefix tailTrace_3013935
  have hstable : (prefixWord ++ tailWord_3013935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013935).length < 2 ^ (prefixWord ++ tailWord_3013935).sum := by decide
  have hdescent : baseEnd_3013935 < baseStart_3013935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013953 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3013953 : Nat := 118140960795 + 3013953 * 2 ^ 59
def prefixEnd_3013953 : Nat := 4983230072969 + 3 ^ 40 * 3013953 * 2
def baseEnd_3013953 : Nat := 1547606559060551628726589

theorem tailTrace_3013953 : CollatzResearch.WordTrace tailWord_3013953 prefixEnd_3013953 1547606559060551628726589 := by
  unfold tailWord_3013953
  simp only [CollatzResearch.WordTrace]
  refine ⟨109927896849970498036790513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73285264566646998691193675 109927896849970498036790513)
  ·
    refine ⟨82445922637477873527592885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109927896849970498036790513 82445922637477873527592885)
    ·
      refine ⟨7729305247263550643211833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82445922637477873527592885 7729305247263550643211833)
      ·
        refine ⟨5796978935447662982408875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7729305247263550643211833 5796978935447662982408875)
        ·
          refine ⟨8695468403171494473613313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796978935447662982408875 8695468403171494473613313)
          ·
            refine ⟨6521601302378620855209985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8695468403171494473613313 6521601302378620855209985)
            ·
              refine ⟨4891200976783965641407489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6521601302378620855209985 4891200976783965641407489)
              ·
                refine ⟨3668400732587974231055617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891200976783965641407489 3668400732587974231055617)
                ·
                  refine ⟨2751300549440980673291713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668400732587974231055617 2751300549440980673291713)
                  ·
                    refine ⟨2063475412080735504968785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2751300549440980673291713 2063475412080735504968785)
                    ·
                      refine ⟨1547606559060551628726589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063475412080735504968785 1547606559060551628726589)
                      ·
                        rfl

theorem cell23_3013953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3013953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013953 prefixEnd_3013953 := by exact prefixLift 3013953
  have htrace : WordTrace (prefixWord ++ tailWord_3013953) baseStart_3013953 baseEnd_3013953 := by
    simpa [prefixWord, tailWord_3013953, baseEnd_3013953] using wordTrace_append hprefix tailTrace_3013953
  have hstable : (prefixWord ++ tailWord_3013953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013953).length < 2 ^ (prefixWord ++ tailWord_3013953).sum := by decide
  have hdescent : baseEnd_3013953 < baseStart_3013953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013959 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 5]
def baseStart_3013959 : Nat := 118140960795 + 3013959 * 2 ^ 59
def prefixEnd_3013959 : Nat := 4983230072969 + 3 ^ 40 * 3013959 * 2
def baseEnd_3013959 : Nat := 171956626660497622805729

theorem tailTrace_3013959 : CollatzResearch.WordTrace tailWord_3013959 prefixEnd_3013959 171956626660497622805729 := by
  unfold tailWord_3013959
  simp only [CollatzResearch.WordTrace]
  refine ⟨109928115687948761061508931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73285410458632507374339287 109928115687948761061508931)
  ·
    refine ⟨164892173531923141592263397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109928115687948761061508931 164892173531923141592263397)
    ·
      refine ⟨30917282537235589048549387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164892173531923141592263397 30917282537235589048549387)
      ·
        refine ⟨46375923805853383572824081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30917282537235589048549387 46375923805853383572824081)
        ·
          refine ⟨34781942854390037679618061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46375923805853383572824081 34781942854390037679618061)
          ·
            refine ⟨13043228570396264129856773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34781942854390037679618061 13043228570396264129856773)
            ·
              refine ⟨2445605356949299524348145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13043228570396264129856773 2445605356949299524348145)
              ·
                refine ⟨1834204017711974643261109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445605356949299524348145 1834204017711974643261109)
                ·
                  refine ⟨171956626660497622805729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1834204017711974643261109 171956626660497622805729)
                  ·
                    rfl

theorem cell23_3013959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 5].length) (baseStart_3013959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3013959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3013959 prefixEnd_3013959 := by exact prefixLift 3013959
  have htrace : WordTrace (prefixWord ++ tailWord_3013959) baseStart_3013959 baseEnd_3013959 := by
    simpa [prefixWord, tailWord_3013959, baseEnd_3013959] using wordTrace_append hprefix tailTrace_3013959
  have hstable : (prefixWord ++ tailWord_3013959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013959).length < 2 ^ (prefixWord ++ tailWord_3013959).sum := by decide
  have hdescent : baseEnd_3013959 < baseStart_3013959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014002 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3014002 : Nat := 118140960795 + 3014002 * 2 ^ 59
def prefixEnd_3014002 : Nat := 4983230072969 + 3 ^ 40 * 3014002 * 2
def baseEnd_3014002 : Nat := 515877239870873979004621

theorem tailTrace_3014002 : CollatzResearch.WordTrace tailWord_3014002 prefixEnd_3014002 515877239870873979004621 := by
  unfold tailWord_3014002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27482421006698244851331065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73286456017861986270216173 27482421006698244851331065)
  ·
    refine ⟨20611815755023683638498299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27482421006698244851331065 20611815755023683638498299)
    ·
      refine ⟨30917723632535525457747449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20611815755023683638498299 30917723632535525457747449)
      ·
        refine ⟨23188292724401644093310587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30917723632535525457747449 23188292724401644093310587)
        ·
          refine ⟨34782439086602466139965881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23188292724401644093310587 34782439086602466139965881)
          ·
            refine ⟨26086829314951849604974411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34782439086602466139965881 26086829314951849604974411)
            ·
              refine ⟨39130243972427774407461617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26086829314951849604974411 39130243972427774407461617)
              ·
                refine ⟨29347682979320830805596213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39130243972427774407461617 29347682979320830805596213)
                ·
                  refine ⟨2751345279311327888024645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29347682979320830805596213 2751345279311327888024645)
                  ·
                    refine ⟨515877239870873979004621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751345279311327888024645 515877239870873979004621)
                    ·
                      rfl

theorem cell23_3014002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3014002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014002 prefixEnd_3014002 := by exact prefixLift 3014002
  have htrace : WordTrace (prefixWord ++ tailWord_3014002) baseStart_3014002 baseEnd_3014002 := by
    simpa [prefixWord, tailWord_3014002, baseEnd_3014002] using wordTrace_append hprefix tailTrace_3014002
  have hstable : (prefixWord ++ tailWord_3014002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014002).length < 2 ^ (prefixWord ++ tailWord_3014002).sum := by decide
  have hdescent : baseEnd_3014002 < baseStart_3014002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014012 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_3014012 : Nat := 118140960795 + 3014012 * 2 ^ 59
def prefixEnd_3014012 : Nat := 4983230072969 + 3 ^ 40 * 3014012 * 2
def baseEnd_3014012 : Nat := 1547636854419166897888817

theorem tailTrace_3014012 : CollatzResearch.WordTrace tailWord_3014012 prefixEnd_3014012 1547636854419166897888817 := by
  unfold tailWord_3014012
  simp only [CollatzResearch.WordTrace]
  refine ⟨54965024378378375556594145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73286699171171167408792193 54965024378378375556594145)
  ·
    refine ⟨41223768283783781667445609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54965024378378375556594145 41223768283783781667445609)
    ·
      refine ⟨30917826212837836250584207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41223768283783781667445609 30917826212837836250584207)
      ·
        refine ⟨46376739319256754375876311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30917826212837836250584207 46376739319256754375876311)
        ·
          refine ⟨69565108978885131563814467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46376739319256754375876311 69565108978885131563814467)
          ·
            refine ⟨104347663468327697345721701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69565108978885131563814467 104347663468327697345721701)
            ·
              refine ⟨19565186900311443252322819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104347663468327697345721701 19565186900311443252322819)
              ·
                refine ⟨29347780350467164878484229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19565186900311443252322819 29347780350467164878484229)
                ·
                  refine ⟨5502708815712593414715793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29347780350467164878484229 5502708815712593414715793)
                  ·
                    refine ⟨4127031611784445061036845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5502708815712593414715793 4127031611784445061036845)
                    ·
                      refine ⟨1547636854419166897888817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4127031611784445061036845 1547636854419166897888817)
                      ·
                        rfl

theorem cell23_3014012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_3014012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014012 prefixEnd_3014012 := by exact prefixLift 3014012
  have htrace : WordTrace (prefixWord ++ tailWord_3014012) baseStart_3014012 baseEnd_3014012 := by
    simpa [prefixWord, tailWord_3014012, baseEnd_3014012] using wordTrace_append hprefix tailTrace_3014012
  have hstable : (prefixWord ++ tailWord_3014012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014012).length < 2 ^ (prefixWord ++ tailWord_3014012).sum := by decide
  have hdescent : baseEnd_3014012 < baseStart_3014012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014019 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 3, 4]
def baseStart_3014019 : Nat := 118140960795 + 3014019 * 2 ^ 59
def prefixEnd_3014019 : Nat := 4983230072969 + 3 ^ 40 * 3014019 * 2
def baseEnd_3014019 : Nat := 515880149594582790167095

theorem tailTrace_3014019 : CollatzResearch.WordTrace tailWord_3014019 prefixEnd_3014019 515880149594582790167095 := by
  unfold tailWord_3014019
  simp only [CollatzResearch.WordTrace]
  refine ⟨109930304067731391308693111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73286869378487594205795407 109930304067731391308693111)
  ·
    refine ⟨164895456101597086963039667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109930304067731391308693111 164895456101597086963039667)
    ·
      refine ⟨247343184152395630444559501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164895456101597086963039667 247343184152395630444559501)
      ·
        refine ⟨92753694057148361416709813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247343184152395630444559501 92753694057148361416709813)
        ·
          refine ⟨8695658817857658882816545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92753694057148361416709813 8695658817857658882816545)
          ·
            refine ⟨6521744113393244162112409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8695658817857658882816545 6521744113393244162112409)
            ·
              refine ⟨4891308085044933121584307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6521744113393244162112409 4891308085044933121584307)
              ·
                refine ⟨7336962127567399682376461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4891308085044933121584307 7336962127567399682376461)
                ·
                  refine ⟨2751360797837774880891173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7336962127567399682376461 2751360797837774880891173)
                  ·
                    refine ⟨515880149594582790167095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751360797837774880891173 515880149594582790167095)
                    ·
                      rfl

theorem cell23_3014019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 4].length) (baseStart_3014019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014019 prefixEnd_3014019 := by exact prefixLift 3014019
  have htrace : WordTrace (prefixWord ++ tailWord_3014019) baseStart_3014019 baseEnd_3014019 := by
    simpa [prefixWord, tailWord_3014019, baseEnd_3014019] using wordTrace_append hprefix tailTrace_3014019
  have hstable : (prefixWord ++ tailWord_3014019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014019).length < 2 ^ (prefixWord ++ tailWord_3014019).sum := by decide
  have hdescent : baseEnd_3014019 < baseStart_3014019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014042 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3014042 : Nat := 118140960795 + 3014042 * 2 ^ 59
def prefixEnd_3014042 : Nat := 4983230072969 + 3 ^ 40 * 3014042 * 2
def baseEnd_3014042 : Nat := 1547652258838801780513679

theorem tailTrace_3014042 : CollatzResearch.WordTrace tailWord_3014042 prefixEnd_3014042 1547652258838801780513679 := by
  unfold tailWord_3014042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27482785736662016559195095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73287428631098710824520253 27482785736662016559195095)
  ·
    refine ⟨41224178604993024838792643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27482785736662016559195095 41224178604993024838792643)
    ·
      refine ⟨61836267907489537258188965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41224178604993024838792643 61836267907489537258188965)
      ·
        refine ⟨11594300232654288235910431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61836267907489537258188965 11594300232654288235910431)
        ·
          refine ⟨17391450348981432353865647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594300232654288235910431 17391450348981432353865647)
          ·
            refine ⟨26087175523472148530798471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17391450348981432353865647 26087175523472148530798471)
            ·
              refine ⟨39130763285208222796197707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26087175523472148530798471 39130763285208222796197707)
              ·
                refine ⟨58696144927812334194296561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39130763285208222796197707 58696144927812334194296561)
                ·
                  refine ⟨44022108695859250645722421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58696144927812334194296561 44022108695859250645722421)
                  ·
                    refine ⟨4127072690236804748036477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44022108695859250645722421 4127072690236804748036477)
                    ·
                      refine ⟨1547652258838801780513679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4127072690236804748036477 1547652258838801780513679)
                      ·
                        rfl

theorem cell23_3014042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3014042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014042 prefixEnd_3014042 := by exact prefixLift 3014042
  have htrace : WordTrace (prefixWord ++ tailWord_3014042) baseStart_3014042 baseEnd_3014042 := by
    simpa [prefixWord, tailWord_3014042, baseEnd_3014042] using wordTrace_append hprefix tailTrace_3014042
  have hstable : (prefixWord ++ tailWord_3014042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014042).length < 2 ^ (prefixWord ++ tailWord_3014042).sum := by decide
  have hdescent : baseEnd_3014042 < baseStart_3014042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014109 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3014109 : Nat := 118140960795 + 3014109 * 2 ^ 59
def prefixEnd_3014109 : Nat := 4983230072969 + 3 ^ 40 * 3014109 * 2
def baseEnd_3014109 : Nat := 515895554014217672791957

theorem tailTrace_3014109 : CollatzResearch.WordTrace tailWord_3014109 prefixEnd_3014109 515895554014217672791957 := by
  unfold tailWord_3014109
  simp only [CollatzResearch.WordTrace]
  refine ⟨109933586637405336679469381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73289057758270224452979587 109933586637405336679469381)
  ·
    refine ⟨20612547494513500627400509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109933586637405336679469381 20612547494513500627400509)
    ·
      refine ⟨7729705310442562735275191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20612547494513500627400509 7729705310442562735275191)
      ·
        refine ⟨11594557965663844102912787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729705310442562735275191 11594557965663844102912787)
        ·
          refine ⟨17391836948495766154369181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594557965663844102912787 17391836948495766154369181)
          ·
            refine ⟨6521938855685912307888443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17391836948495766154369181 6521938855685912307888443)
            ·
              refine ⟨9782908283528868461832665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521938855685912307888443 9782908283528868461832665)
              ·
                refine ⟨7337181212646651346374499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9782908283528868461832665 7337181212646651346374499)
                ·
                  refine ⟨11005771818969977019561749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7337181212646651346374499 11005771818969977019561749)
                  ·
                    refine ⟨515895554014217672791957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11005771818969977019561749 515895554014217672791957)
                    ·
                      rfl

theorem cell23_3014109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3014109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014109 prefixEnd_3014109 := by exact prefixLift 3014109
  have htrace : WordTrace (prefixWord ++ tailWord_3014109) baseStart_3014109 baseEnd_3014109 := by
    simpa [prefixWord, tailWord_3014109, baseEnd_3014109] using wordTrace_append hprefix tailTrace_3014109
  have hstable : (prefixWord ++ tailWord_3014109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014109).length < 2 ^ (prefixWord ++ tailWord_3014109).sum := by decide
  have hdescent : baseEnd_3014109 < baseStart_3014109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014119 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3014119 : Nat := 118140960795 + 3014119 * 2 ^ 59
def prefixEnd_3014119 : Nat := 4983230072969 + 3 ^ 40 * 3014119 * 2
def baseEnd_3014119 : Nat := 1547691796849197979250825

theorem tailTrace_3014119 : CollatzResearch.WordTrace tailWord_3014119 prefixEnd_3014119 1547691796849197979250825 := by
  unfold tailWord_3014119
  simp only [CollatzResearch.WordTrace]
  refine ⟨109933951367369108387333411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73289300911579405591555607 109933951367369108387333411)
  ·
    refine ⟨164900927051053662581000117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109933951367369108387333411 164900927051053662581000117)
    ·
      refine ⟨15459461911036280866968761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164900927051053662581000117 15459461911036280866968761)
      ·
        refine ⟨11594596433277210650226571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15459461911036280866968761 11594596433277210650226571)
        ·
          refine ⟨17391894649915815975339857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594596433277210650226571 17391894649915815975339857)
          ·
            refine ⟨13043920987436861981504893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17391894649915815975339857 13043920987436861981504893)
            ·
              refine ⟨4891470370288823243064335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13043920987436861981504893 4891470370288823243064335)
              ·
                refine ⟨7337205555433234864596503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4891470370288823243064335 7337205555433234864596503)
                ·
                  refine ⟨11005808333149852296894755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7337205555433234864596503 11005808333149852296894755)
                  ·
                    refine ⟨16508712499724778445342133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11005808333149852296894755 16508712499724778445342133)
                    ·
                      refine ⟨1547691796849197979250825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16508712499724778445342133 1547691796849197979250825)
                      ·
                        rfl

theorem cell23_3014119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3014119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014119 prefixEnd_3014119 := by exact prefixLift 3014119
  have htrace : WordTrace (prefixWord ++ tailWord_3014119) baseStart_3014119 baseEnd_3014119 := by
    simpa [prefixWord, tailWord_3014119, baseEnd_3014119] using wordTrace_append hprefix tailTrace_3014119
  have hstable : (prefixWord ++ tailWord_3014119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014119).length < 2 ^ (prefixWord ++ tailWord_3014119).sum := by decide
  have hdescent : baseEnd_3014119 < baseStart_3014119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014122 : List Nat := [3, 1, 3, 1, 4, 11]
def baseStart_3014122 : Nat := 118140960795 + 3014122 * 2 ^ 59
def prefixEnd_3014122 : Nat := 4983230072969 + 3 ^ 40 * 3014122 * 2
def baseEnd_3014122 : Nat := 6369108383914244722277

theorem tailTrace_3014122 : CollatzResearch.WordTrace tailWord_3014122 prefixEnd_3014122 6369108383914244722277 := by
  unfold tailWord_3014122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27483515196589559974923155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73289373857572159933128413 27483515196589559974923155)
  ·
    refine ⟨41225272794884339962384733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27483515196589559974923155 41225272794884339962384733)
    ·
      refine ⟨15459477298081627485894275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41225272794884339962384733 15459477298081627485894275)
      ·
        refine ⟨23189215947122441228841413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15459477298081627485894275 23189215947122441228841413)
        ·
          refine ⟨4347977990085457730407765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23189215947122441228841413 4347977990085457730407765)
          ·
            refine ⟨6369108383914244722277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4347977990085457730407765 6369108383914244722277)
            ·
              rfl

theorem cell23_3014122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 11].length) (baseStart_3014122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014122 prefixEnd_3014122 := by exact prefixLift 3014122
  have htrace : WordTrace (prefixWord ++ tailWord_3014122) baseStart_3014122 baseEnd_3014122 := by
    simpa [prefixWord, tailWord_3014122, baseEnd_3014122] using wordTrace_append hprefix tailTrace_3014122
  have hstable : (prefixWord ++ tailWord_3014122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014122).length < 2 ^ (prefixWord ++ tailWord_3014122).sum := by decide
  have hdescent : baseEnd_3014122 < baseStart_3014122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014126 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3014126 : Nat := 118140960795 + 3014126 * 2 ^ 59
def prefixEnd_3014126 : Nat := 4983230072969 + 3 ^ 40 * 3014126 * 2
def baseEnd_3014126 : Nat := 515898463737926483954431

theorem tailTrace_3014126 : CollatzResearch.WordTrace tailWord_3014126 prefixEnd_3014126 515898463737926483954431 := by
  unfold tailWord_3014126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13741775834792968572854779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73289471118895832388558821 13741775834792968572854779)
  ·
    refine ⟨20612663752189452859282169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13741775834792968572854779 20612663752189452859282169)
    ·
      refine ⟨15459497814142089644461627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20612663752189452859282169 15459497814142089644461627)
      ·
        refine ⟨23189246721213134466692441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15459497814142089644461627 23189246721213134466692441)
        ·
          refine ⟨17391935040909850850019331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23189246721213134466692441 17391935040909850850019331)
          ·
            refine ⟨26087902561364776275028997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17391935040909850850019331 26087902561364776275028997)
            ·
              refine ⟨4891481730255895551567937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26087902561364776275028997 4891481730255895551567937)
              ·
                refine ⟨3668611297691921663675953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891481730255895551567937 3668611297691921663675953)
                ·
                  refine ⟨2751458473268941247756965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668611297691921663675953 2751458473268941247756965)
                  ·
                    refine ⟨515898463737926483954431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751458473268941247756965 515898463737926483954431)
                    ·
                      rfl

theorem cell23_3014126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3014126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014126 prefixEnd_3014126 := by exact prefixLift 3014126
  have htrace : WordTrace (prefixWord ++ tailWord_3014126) baseStart_3014126 baseEnd_3014126 := by
    simpa [prefixWord, tailWord_3014126, baseEnd_3014126] using wordTrace_append hprefix tailTrace_3014126
  have hstable : (prefixWord ++ tailWord_3014126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014126).length < 2 ^ (prefixWord ++ tailWord_3014126).sum := by decide
  have hdescent : baseEnd_3014126 < baseStart_3014126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014146 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3014146 : Nat := 118140960795 + 3014146 * 2 ^ 59
def prefixEnd_3014146 : Nat := 4983230072969 + 3 ^ 40 * 3014146 * 2
def baseEnd_3014146 : Nat := 1547705660826869373613201

theorem tailTrace_3014146 : CollatzResearch.WordTrace tailWord_3014146 prefixEnd_3014146 1547705660826869373613201 := by
  unfold tailWord_3014146
  simp only [CollatzResearch.WordTrace]
  refine ⟨27483734034567822999641573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73289957425514194665710861 27483734034567822999641573)
  ·
    refine ⟨5153200131481466812432795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27483734034567822999641573 5153200131481466812432795)
    ·
      refine ⟨7729800197222200218649193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153200131481466812432795 7729800197222200218649193)
      ·
        refine ⟨5797350147916650163986895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7729800197222200218649193 5797350147916650163986895)
        ·
          refine ⟨8696025221874975245980343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797350147916650163986895 8696025221874975245980343)
          ·
            refine ⟨13044037832812462868970515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8696025221874975245980343 13044037832812462868970515)
            ·
              refine ⟨19566056749218694303455773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13044037832812462868970515 19566056749218694303455773)
              ·
                refine ⟨7337271280957010363795915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19566056749218694303455773 7337271280957010363795915)
                ·
                  refine ⟨11005906921435515545693873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7337271280957010363795915 11005906921435515545693873)
                  ·
                    refine ⟨8254430191076636659270405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11005906921435515545693873 8254430191076636659270405)
                    ·
                      refine ⟨1547705660826869373613201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8254430191076636659270405 1547705660826869373613201)
                      ·
                        rfl

theorem cell23_3014146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3014146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014146 prefixEnd_3014146 := by exact prefixLift 3014146
  have htrace : WordTrace (prefixWord ++ tailWord_3014146) baseStart_3014146 baseEnd_3014146 := by
    simpa [prefixWord, tailWord_3014146, baseEnd_3014146] using wordTrace_append hprefix tailTrace_3014146
  have hstable : (prefixWord ++ tailWord_3014146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014146).length < 2 ^ (prefixWord ++ tailWord_3014146).sum := by decide
  have hdescent : baseEnd_3014146 < baseStart_3014146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014149 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_3014149 : Nat := 118140960795 + 3014149 * 2 ^ 59
def prefixEnd_3014149 : Nat := 4983230072969 + 3 ^ 40 * 3014149 * 2
def baseEnd_3014149 : Nat := 1547707201268832861875687

theorem tailTrace_3014149 : CollatzResearch.WordTrace tailWord_3014149 prefixEnd_3014149 1547707201268832861875687 := by
  unfold tailWord_3014149
  simp only [CollatzResearch.WordTrace]
  refine ⟨109935045557260423510925501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73290030371506949007283667 109935045557260423510925501)
  ·
    refine ⟨41225642083972658816597063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109935045557260423510925501 41225642083972658816597063)
    ·
      refine ⟨61838463125958988224895595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41225642083972658816597063 61838463125958988224895595)
      ·
        refine ⟨92757694688938482337343393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61838463125958988224895595 92757694688938482337343393)
        ·
          refine ⟨69568271016703861753007545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92757694688938482337343393 69568271016703861753007545)
          ·
            refine ⟨52176203262527896314755659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69568271016703861753007545 52176203262527896314755659)
            ·
              refine ⟨78264304893791844472133489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52176203262527896314755659 78264304893791844472133489)
              ·
                refine ⟨58698228670343883354100117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78264304893791844472133489 58698228670343883354100117)
                ·
                  refine ⟨2751479468922369532223443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58698228670343883354100117 2751479468922369532223443)
                  ·
                    refine ⟨4127219203383554298335165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2751479468922369532223443 4127219203383554298335165)
                    ·
                      refine ⟨1547707201268832861875687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4127219203383554298335165 1547707201268832861875687)
                      ·
                        rfl

theorem cell23_3014149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_3014149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014149 prefixEnd_3014149 := by exact prefixLift 3014149
  have htrace : WordTrace (prefixWord ++ tailWord_3014149) baseStart_3014149 baseEnd_3014149 := by
    simpa [prefixWord, tailWord_3014149, baseEnd_3014149] using wordTrace_append hprefix tailTrace_3014149
  have hstable : (prefixWord ++ tailWord_3014149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014149).length < 2 ^ (prefixWord ++ tailWord_3014149).sum := by decide
  have hdescent : baseEnd_3014149 < baseStart_3014149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014159 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 7, 3, 2]
def baseStart_3014159 : Nat := 118140960795 + 3014159 * 2 ^ 59
def prefixEnd_3014159 : Nat := 4983230072969 + 3 ^ 40 * 3014159 * 2
def baseEnd_3014159 : Nat := 1547712336075377822750641

theorem tailTrace_3014159 : CollatzResearch.WordTrace tailWord_3014159 prefixEnd_3014159 1547712336075377822750641 := by
  unfold tailWord_3014159
  simp only [CollatzResearch.WordTrace]
  refine ⟨109935410287224195218789531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73290273524816130145859687 109935410287224195218789531)
  ·
    refine ⟨164903115430836292828184297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109935410287224195218789531 164903115430836292828184297)
    ·
      refine ⟨123677336573127219621138223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164903115430836292828184297 123677336573127219621138223)
      ·
        refine ⟨185516004859690829431707335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123677336573127219621138223 185516004859690829431707335)
        ·
          refine ⟨278274007289536244147561003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185516004859690829431707335 278274007289536244147561003)
          ·
            refine ⟨417411010934304366221341505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278274007289536244147561003 417411010934304366221341505)
            ·
              refine ⟨313058258200728274666006129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417411010934304366221341505 313058258200728274666006129)
              ·
                refine ⟨234793693650546205999504597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313058258200728274666006129 234793693650546205999504597)
                ·
                  refine ⟨5502977194934676703113389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 234793693650546205999504597 5502977194934676703113389)
                  ·
                    refine ⟨2063616448100503763667521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5502977194934676703113389 2063616448100503763667521)
                    ·
                      refine ⟨1547712336075377822750641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063616448100503763667521 1547712336075377822750641)
                      ·
                        rfl

theorem cell23_3014159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3, 2].length) (baseStart_3014159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014159 prefixEnd_3014159 := by exact prefixLift 3014159
  have htrace : WordTrace (prefixWord ++ tailWord_3014159) baseStart_3014159 baseEnd_3014159 := by
    simpa [prefixWord, tailWord_3014159, baseEnd_3014159] using wordTrace_append hprefix tailTrace_3014159
  have hstable : (prefixWord ++ tailWord_3014159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014159).length < 2 ^ (prefixWord ++ tailWord_3014159).sum := by decide
  have hdescent : baseEnd_3014159 < baseStart_3014159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014192 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_3014192 : Nat := 118140960795 + 3014192 * 2 ^ 59
def prefixEnd_3014192 : Nat := 4983230072969 + 3 ^ 40 * 3014192 * 2
def baseEnd_3014192 : Nat := 1547729280936976193637989

theorem tailTrace_3014192 : CollatzResearch.WordTrace tailWord_3014192 prefixEnd_3014192 1547729280936976193637989 := by
  unfold tailWord_3014192
  simp only [CollatzResearch.WordTrace]
  refine ⟨54968306948052320927370415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73291075930736427903160553 54968306948052320927370415)
  ·
    refine ⟨82452460422078481391055623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54968306948052320927370415 82452460422078481391055623)
    ·
      refine ⟨123678690633117722086583435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82452460422078481391055623 123678690633117722086583435)
      ·
        refine ⟨185518035949676583129875153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123678690633117722086583435 185518035949676583129875153)
        ·
          refine ⟨139138526962257437347406365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185518035949676583129875153 139138526962257437347406365)
          ·
            refine ⟨52176947610846539005277387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139138526962257437347406365 52176947610846539005277387)
            ·
              refine ⟨78265421416269808507916081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52176947610846539005277387 78265421416269808507916081)
              ·
                refine ⟨58699066062202356380937061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78265421416269808507916081 58699066062202356380937061)
                ·
                  refine ⟨11006074886662941821425699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58699066062202356380937061 11006074886662941821425699)
                  ·
                    refine ⟨16509112329994412732138549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11006074886662941821425699 16509112329994412732138549)
                    ·
                      refine ⟨1547729280936976193637989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16509112329994412732138549 1547729280936976193637989)
                      ·
                        rfl

theorem cell23_3014192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_3014192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014192 prefixEnd_3014192 := by exact prefixLift 3014192
  have htrace : WordTrace (prefixWord ++ tailWord_3014192) baseStart_3014192 baseEnd_3014192 := by
    simpa [prefixWord, tailWord_3014192, baseEnd_3014192] using wordTrace_append hprefix tailTrace_3014192
  have hstable : (prefixWord ++ tailWord_3014192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014192).length < 2 ^ (prefixWord ++ tailWord_3014192).sum := by decide
  have hdescent : baseEnd_3014192 < baseStart_3014192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014209 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3014209 : Nat := 118140960795 + 3014209 * 2 ^ 59
def prefixEnd_3014209 : Nat := 4983230072969 + 3 ^ 40 * 3014209 * 2
def baseEnd_3014209 : Nat := 1547738010108102627125411

theorem tailTrace_3014209 : CollatzResearch.WordTrace tailWord_3014209 prefixEnd_3014209 1547738010108102627125411 := by
  unfold tailWord_3014209
  simp only [CollatzResearch.WordTrace]
  refine ⟨109937233937043053758109681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73291489291362035838739787 109937233937043053758109681)
  ·
    refine ⟨82452925452782290318582261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109937233937043053758109681 82452925452782290318582261)
    ·
      refine ⟨7729961761198339717367087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82452925452782290318582261 7729961761198339717367087)
      ·
        refine ⟨11594942641797509576050631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729961761198339717367087 11594942641797509576050631)
        ·
          refine ⟨17392413962696264364075947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594942641797509576050631 17392413962696264364075947)
          ·
            refine ⟨26088620944044396546113921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17392413962696264364075947 26088620944044396546113921)
            ·
              refine ⟨19566465708033297409585441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26088620944044396546113921 19566465708033297409585441)
              ·
                refine ⟨14674849281024973057189081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19566465708033297409585441 14674849281024973057189081)
                ·
                  refine ⟨11006136960768729792891811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14674849281024973057189081 11006136960768729792891811)
                  ·
                    refine ⟨16509205441153094689337717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11006136960768729792891811 16509205441153094689337717)
                    ·
                      refine ⟨1547738010108102627125411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16509205441153094689337717 1547738010108102627125411)
                      ·
                        rfl

theorem cell23_3014209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3014209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014209 prefixEnd_3014209 := by exact prefixLift 3014209
  have htrace : WordTrace (prefixWord ++ tailWord_3014209) baseStart_3014209 baseEnd_3014209 := by
    simpa [prefixWord, tailWord_3014209, baseEnd_3014209] using wordTrace_append hprefix tailTrace_3014209
  have hstable : (prefixWord ++ tailWord_3014209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014209).length < 2 ^ (prefixWord ++ tailWord_3014209).sum := by decide
  have hdescent : baseEnd_3014209 < baseStart_3014209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014289 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 7, 4]
def baseStart_3014289 : Nat := 118140960795 + 3014289 * 2 ^ 59
def prefixEnd_3014289 : Nat := 4983230072969 + 3 ^ 40 * 3014289 * 2
def baseEnd_3014289 : Nat := 515926362853487438041681

theorem tailTrace_3014289 : CollatzResearch.WordTrace tailWord_3014289 prefixEnd_3014289 515926362853487438041681 := by
  unfold tailWord_3014289
  simp only [CollatzResearch.WordTrace]
  refine ⟨109940151776753227421021921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73293434517835484947347947 109940151776753227421021921)
  ·
    refine ⟨82455113832564920565766441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109940151776753227421021921 82455113832564920565766441)
    ·
      refine ⟨61841335374423690424324831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82455113832564920565766441 61841335374423690424324831)
      ·
        refine ⟨92762003061635535636487247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61841335374423690424324831 92762003061635535636487247)
        ·
          refine ⟨139143004592453303454730871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92762003061635535636487247 139143004592453303454730871)
          ·
            refine ⟨208714506888679955182096307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139143004592453303454730871 208714506888679955182096307)
            ·
              refine ⟨313071760333019932773144461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208714506888679955182096307 313071760333019932773144461)
              ·
                refine ⟨117401910124882474789929173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313071760333019932773144461 117401910124882474789929173)
                ·
                  refine ⟨2751607268551933002888965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117401910124882474789929173 2751607268551933002888965)
                  ·
                    refine ⟨515926362853487438041681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751607268551933002888965 515926362853487438041681)
                    ·
                      rfl

theorem cell23_3014289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_3014289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014289 prefixEnd_3014289 := by exact prefixLift 3014289
  have htrace : WordTrace (prefixWord ++ tailWord_3014289) baseStart_3014289 baseEnd_3014289 := by
    simpa [prefixWord, tailWord_3014289, baseEnd_3014289] using wordTrace_append hprefix tailTrace_3014289
  have hstable : (prefixWord ++ tailWord_3014289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014289).length < 2 ^ (prefixWord ++ tailWord_3014289).sum := by decide
  have hdescent : baseEnd_3014289 < baseStart_3014289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014296 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3014296 : Nat := 118140960795 + 3014296 * 2 ^ 59
def prefixEnd_3014296 : Nat := 4983230072969 + 3 ^ 40 * 3014296 * 2
def baseEnd_3014296 : Nat := 1547782682925043786737511

theorem tailTrace_3014296 : CollatzResearch.WordTrace tailWord_3014296 prefixEnd_3014296 1547782682925043786737511 := by
  unfold tailWord_3014296
  simp only [CollatzResearch.WordTrace]
  refine ⟨54970203543863933808263371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73293604725151911744351161 54970203543863933808263371)
  ·
    refine ⟨82455305315795900712395057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54970203543863933808263371 82455305315795900712395057)
    ·
      refine ⟨61841478986846925534296293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82455305315795900712395057 61841478986846925534296293)
      ·
        refine ⟨11595277310033798537680555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61841478986846925534296293 11595277310033798537680555)
        ·
          refine ⟨17392915965050697806520833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595277310033798537680555 17392915965050697806520833)
          ·
            refine ⟨13044686973788023354890625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17392915965050697806520833 13044686973788023354890625)
            ·
              refine ⟨9783515230341017516167969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13044686973788023354890625 9783515230341017516167969)
              ·
                refine ⟨7337636422755763137125977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9783515230341017516167969 7337636422755763137125977)
                ·
                  refine ⟨5503227317066822352844483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7337636422755763137125977 5503227317066822352844483)
                  ·
                    refine ⟨8254840975600233529266725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5503227317066822352844483 8254840975600233529266725)
                    ·
                      refine ⟨1547782682925043786737511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8254840975600233529266725 1547782682925043786737511)
                      ·
                        rfl

theorem cell23_3014296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3014296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014296 prefixEnd_3014296 := by exact prefixLift 3014296
  have htrace : WordTrace (prefixWord ++ tailWord_3014296) baseStart_3014296 baseEnd_3014296 := by
    simpa [prefixWord, tailWord_3014296, baseEnd_3014296] using wordTrace_append hprefix tailTrace_3014296
  have hstable : (prefixWord ++ tailWord_3014296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014296).length < 2 ^ (prefixWord ++ tailWord_3014296).sum := by decide
  have hdescent : baseEnd_3014296 < baseStart_3014296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014319 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 6]
def baseStart_3014319 : Nat := 118140960795 + 3014319 * 2 ^ 59
def prefixEnd_3014319 : Nat := 4983230072969 + 3 ^ 40 * 3014319 * 2
def baseEnd_3014319 : Nat := 171977165886677466305545

theorem tailTrace_3014319 : CollatzResearch.WordTrace tailWord_3014319 prefixEnd_3014319 171977165886677466305545 := by
  unfold tailWord_3014319
  simp only [CollatzResearch.WordTrace]
  refine ⟨109941245966644542544614011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73294163977763028363076007 109941245966644542544614011)
  ·
    refine ⟨164911868949966813816921017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109941245966644542544614011 164911868949966813816921017)
    ·
      refine ⟨123683901712475110362690763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164911868949966813816921017 123683901712475110362690763)
      ·
        refine ⟨185525852568712665544036145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123683901712475110362690763 185525852568712665544036145)
        ·
          refine ⟨139144389426534499158027109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185525852568712665544036145 139144389426534499158027109)
          ·
            refine ⟨26089573017475218592130083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139144389426534499158027109 26089573017475218592130083)
            ·
              refine ⟨39134359526212827888195125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26089573017475218592130083 39134359526212827888195125)
              ·
                refine ⟨3668846205582452614518293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39134359526212827888195125 3668846205582452614518293)
                ·
                  refine ⟨171977165886677466305545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3668846205582452614518293 171977165886677466305545)
                  ·
                    rfl

theorem cell23_3014319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 6].length) (baseStart_3014319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014319 prefixEnd_3014319 := by exact prefixLift 3014319
  have htrace : WordTrace (prefixWord ++ tailWord_3014319) baseStart_3014319 baseEnd_3014319 := by
    simpa [prefixWord, tailWord_3014319, baseEnd_3014319] using wordTrace_append hprefix tailTrace_3014319
  have hstable : (prefixWord ++ tailWord_3014319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014319).length < 2 ^ (prefixWord ++ tailWord_3014319).sum := by decide
  have hdescent : baseEnd_3014319 < baseStart_3014319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014340 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3014340 : Nat := 118140960795 + 3014340 * 2 ^ 59
def prefixEnd_3014340 : Nat := 4983230072969 + 3 ^ 40 * 3014340 * 2
def baseEnd_3014340 : Nat := 515935092024613871529103

theorem tailTrace_3014340 : CollatzResearch.WordTrace tailWord_3014340 prefixEnd_3014340 515935092024613871529103 := by
  unfold tailWord_3014340
  simp only [CollatzResearch.WordTrace]
  refine ⟨54971005949784231565564237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73294674599712308754085649 54971005949784231565564237)
  ·
    refine ⟨20614127231169086837086589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54971005949784231565564237 20614127231169086837086589)
    ·
      refine ⟨7730297711688407563907471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20614127231169086837086589 7730297711688407563907471)
      ·
        refine ⟨11595446567532611345861207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730297711688407563907471 11595446567532611345861207)
        ·
          refine ⟨17393169851298917018791811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595446567532611345861207 17393169851298917018791811)
          ·
            refine ⟨26089754776948375528187717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17393169851298917018791811 26089754776948375528187717)
            ·
              refine ⟨4891829020677820411535197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26089754776948375528187717 4891829020677820411535197)
              ·
                refine ⟨1834435882754182654325699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891829020677820411535197 1834435882754182654325699)
                ·
                  refine ⟨2751653824131273981488549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834435882754182654325699 2751653824131273981488549)
                  ·
                    refine ⟨515935092024613871529103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751653824131273981488549 515935092024613871529103)
                    ·
                      rfl

theorem cell23_3014340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3014340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014340 prefixEnd_3014340 := by exact prefixLift 3014340
  have htrace : WordTrace (prefixWord ++ tailWord_3014340) baseStart_3014340 baseEnd_3014340 := by
    simpa [prefixWord, tailWord_3014340, baseEnd_3014340] using wordTrace_append hprefix tailTrace_3014340
  have hstable : (prefixWord ++ tailWord_3014340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014340).length < 2 ^ (prefixWord ++ tailWord_3014340).sum := by decide
  have hdescent : baseEnd_3014340 < baseStart_3014340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014356 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3014356 : Nat := 118140960795 + 3014356 * 2 ^ 59
def prefixEnd_3014356 : Nat := 4983230072969 + 3 ^ 40 * 3014356 * 2
def baseEnd_3014356 : Nat := 1547813491764313551987235

theorem tailTrace_3014356 : CollatzResearch.WordTrace tailWord_3014356 prefixEnd_3014356 1547813491764313551987235 := by
  unfold tailWord_3014356
  simp only [CollatzResearch.WordTrace]
  refine ⟨54971297733755248931855461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73295063645006998575807281 54971297733755248931855461)
  ·
    refine ⟨10307118325079109174722899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54971297733755248931855461 10307118325079109174722899)
    ·
      refine ⟨15460677487618663762084349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10307118325079109174722899 15460677487618663762084349)
      ·
        refine ⟨5797754057856998910781631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15460677487618663762084349 5797754057856998910781631)
        ·
          refine ⟨8696631086785498366172447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797754057856998910781631 8696631086785498366172447)
          ·
            refine ⟨13044946630178247549258671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8696631086785498366172447 13044946630178247549258671)
            ·
              refine ⟨19567419945267371323888007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13044946630178247549258671 19567419945267371323888007)
              ·
                refine ⟨29351129917901056985832011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19567419945267371323888007 29351129917901056985832011)
                ·
                  refine ⟨44026694876851585478748017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29351129917901056985832011 44026694876851585478748017)
                  ·
                    refine ⟨33020021157638689109061013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44026694876851585478748017 33020021157638689109061013)
                    ·
                      refine ⟨1547813491764313551987235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33020021157638689109061013 1547813491764313551987235)
                      ·
                        rfl

theorem cell23_3014356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3014356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014356 prefixEnd_3014356 := by exact prefixLift 3014356
  have htrace : WordTrace (prefixWord ++ tailWord_3014356) baseStart_3014356 baseEnd_3014356 := by
    simpa [prefixWord, tailWord_3014356, baseEnd_3014356] using wordTrace_append hprefix tailTrace_3014356
  have hstable : (prefixWord ++ tailWord_3014356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014356).length < 2 ^ (prefixWord ++ tailWord_3014356).sum := by decide
  have hdescent : baseEnd_3014356 < baseStart_3014356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014396 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_3014396 : Nat := 118140960795 + 3014396 * 2 ^ 59
def prefixEnd_3014396 : Nat := 4983230072969 + 3 ^ 40 * 3014396 * 2
def baseEnd_3014396 : Nat := 515944676996831131829017

theorem tailTrace_3014396 : CollatzResearch.WordTrace tailWord_3014396 prefixEnd_3014396 515944676996831131829017 := by
  unfold tailWord_3014396
  simp only [CollatzResearch.WordTrace]
  refine ⟨54972027193682792347583521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73296036258243723130111361 54972027193682792347583521)
  ·
    refine ⟨41229020395262094260687641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54972027193682792347583521 41229020395262094260687641)
    ·
      refine ⟨30921765296446570695515731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41229020395262094260687641 30921765296446570695515731)
      ·
        refine ⟨46382647944669856043273597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30921765296446570695515731 46382647944669856043273597)
        ·
          refine ⟨17393492979251196016227599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46382647944669856043273597 17393492979251196016227599)
          ·
            refine ⟨26090239468876794024341399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17393492979251196016227599 26090239468876794024341399)
            ·
              refine ⟨39135359203315191036512099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26090239468876794024341399 39135359203315191036512099)
              ·
                refine ⟨58703038804972786554768149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39135359203315191036512099 58703038804972786554768149)
                ·
                  refine ⟨2751704943983099369754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58703038804972786554768149 2751704943983099369754757)
                  ·
                    refine ⟨515944676996831131829017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751704943983099369754757 515944676996831131829017)
                    ·
                      rfl

theorem cell23_3014396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_3014396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014396 prefixEnd_3014396 := by exact prefixLift 3014396
  have htrace : WordTrace (prefixWord ++ tailWord_3014396) baseStart_3014396 baseEnd_3014396 := by
    simpa [prefixWord, tailWord_3014396, baseEnd_3014396] using wordTrace_append hprefix tailTrace_3014396
  have hstable : (prefixWord ++ tailWord_3014396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014396).length < 2 ^ (prefixWord ++ tailWord_3014396).sum := by decide
  have hdescent : baseEnd_3014396 < baseStart_3014396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014403 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 5, 2, 2]
def baseStart_3014403 : Nat := 118140960795 + 3014403 * 2 ^ 59
def prefixEnd_3014403 : Nat := 4983230072969 + 3 ^ 40 * 3014403 * 2
def baseEnd_3014403 : Nat := 1547837625355074868099519

theorem tailTrace_3014403 : CollatzResearch.WordTrace tailWord_3014403 prefixEnd_3014403 1547837625355074868099519 := by
  unfold tailWord_3014403
  simp only [CollatzResearch.WordTrace]
  refine ⟨109944309698340224890671863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73296206465560149927114575 109944309698340224890671863)
  ·
    refine ⟨164916464547510337336007795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109944309698340224890671863 164916464547510337336007795)
    ·
      refine ⟨247374696821265506004011693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164916464547510337336007795 247374696821265506004011693)
      ·
        refine ⟨92765511307974564751504385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247374696821265506004011693 92765511307974564751504385)
        ·
          refine ⟨69574133480980923563628289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92765511307974564751504385 69574133480980923563628289)
          ·
            refine ⟨52180600110735692672721217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69574133480980923563628289 52180600110735692672721217)
            ·
              refine ⟨39135450083051769504540913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52180600110735692672721217 39135450083051769504540913)
              ·
                refine ⟨29351587562288827128405685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39135450083051769504540913 29351587562288827128405685)
                ·
                  refine ⟨2751711333964577543288033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29351587562288827128405685 2751711333964577543288033)
                  ·
                    refine ⟨2063783500473433157466025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2751711333964577543288033 2063783500473433157466025)
                    ·
                      refine ⟨1547837625355074868099519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063783500473433157466025 1547837625355074868099519)
                      ·
                        rfl

theorem cell23_3014403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_3014403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014403 prefixEnd_3014403 := by exact prefixLift 3014403
  have htrace : WordTrace (prefixWord ++ tailWord_3014403) baseStart_3014403 baseEnd_3014403 := by
    simpa [prefixWord, tailWord_3014403, baseEnd_3014403] using wordTrace_append hprefix tailTrace_3014403
  have hstable : (prefixWord ++ tailWord_3014403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014403).length < 2 ^ (prefixWord ++ tailWord_3014403).sum := by decide
  have hdescent : baseEnd_3014403 < baseStart_3014403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014426 : List Nat := [3, 1, 1, 3, 2, 3, 2, 8]
def baseStart_3014426 : Nat := 118140960795 + 3014426 * 2 ^ 59
def prefixEnd_3014426 : Nat := 4983230072969 + 3 ^ 40 * 3014426 * 2
def baseEnd_3014426 : Nat := 57327756867041788078219

theorem tailTrace_3014426 : CollatzResearch.WordTrace tailWord_3014426 prefixEnd_3014426 57327756867041788078219 := by
  unfold tailWord_3014426
  simp only [CollatzResearch.WordTrace]
  refine ⟨27486287144314224954689783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73296765718171266545839421 27486287144314224954689783)
  ·
    refine ⟨41229430716471337432034675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27486287144314224954689783 41229430716471337432034675)
    ·
      refine ⟨61844146074707006148052013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41229430716471337432034675 61844146074707006148052013)
      ·
        refine ⟨23191554778015127305519505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61844146074707006148052013 23191554778015127305519505)
        ·
          refine ⟨17393666083511345479139629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23191554778015127305519505 17393666083511345479139629)
          ·
            refine ⟨6522624781316754554677361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17393666083511345479139629 6522624781316754554677361)
            ·
              refine ⟨4891968585987565916008021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6522624781316754554677361 4891968585987565916008021)
              ·
                refine ⟨57327756867041788078219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4891968585987565916008021 57327756867041788078219)
                ·
                  rfl

theorem cell23_3014426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_3014426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014426 prefixEnd_3014426 := by exact prefixLift 3014426
  have htrace : WordTrace (prefixWord ++ tailWord_3014426) baseStart_3014426 baseEnd_3014426 := by
    simpa [prefixWord, tailWord_3014426, baseEnd_3014426] using wordTrace_append hprefix tailTrace_3014426
  have hstable : (prefixWord ++ tailWord_3014426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014426).length < 2 ^ (prefixWord ++ tailWord_3014426).sum := by decide
  have hdescent : baseEnd_3014426 < baseStart_3014426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014440 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3014440 : Nat := 118140960795 + 3014440 * 2 ^ 59
def prefixEnd_3014440 : Nat := 4983230072969 + 3 ^ 40 * 3014440 * 2
def baseEnd_3014440 : Nat := 1547856624139291223336849

theorem tailTrace_3014440 : CollatzResearch.WordTrace tailWord_3014440 prefixEnd_3014440 1547856624139291223336849 := by
  unfold tailWord_3014440
  simp only [CollatzResearch.WordTrace]
  refine ⟨54972829599603090104884387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73297106132804120139845849 54972829599603090104884387)
  ·
    refine ⟨82459244399404635157326581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54972829599603090104884387 82459244399404635157326581)
    ·
      refine ⟨7730554162444184545999367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82459244399404635157326581 7730554162444184545999367)
      ·
        refine ⟨11595831243666276818999051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730554162444184545999367 11595831243666276818999051)
        ·
          refine ⟨17393746865499415228498577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595831243666276818999051 17393746865499415228498577)
          ·
            refine ⟨13045310149124561421373933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17393746865499415228498577 13045310149124561421373933)
            ·
              refine ⟨4891991305921710533015225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13045310149124561421373933 4891991305921710533015225)
              ·
                refine ⟨3668993479441282899761419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891991305921710533015225 3668993479441282899761419)
                ·
                  refine ⟨5503490219161924349642129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668993479441282899761419 5503490219161924349642129)
                  ·
                    refine ⟨4127617664371443262231597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503490219161924349642129 4127617664371443262231597)
                    ·
                      refine ⟨1547856624139291223336849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4127617664371443262231597 1547856624139291223336849)
                      ·
                        rfl

theorem cell23_3014440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3014440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014440 prefixEnd_3014440 := by exact prefixLift 3014440
  have htrace : WordTrace (prefixWord ++ tailWord_3014440) baseStart_3014440 baseEnd_3014440 := by
    simpa [prefixWord, tailWord_3014440, baseEnd_3014440] using wordTrace_append hprefix tailTrace_3014440
  have hstable : (prefixWord ++ tailWord_3014440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014440).length < 2 ^ (prefixWord ++ tailWord_3014440).sum := by decide
  have hdescent : baseEnd_3014440 < baseStart_3014440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014457 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3014457 : Nat := 118140960795 + 3014457 * 2 ^ 59
def prefixEnd_3014457 : Nat := 4983230072969 + 3 ^ 40 * 3014457 * 2
def baseEnd_3014457 : Nat := 1547865353310417656824271

theorem tailTrace_3014457 : CollatzResearch.WordTrace tailWord_3014457 prefixEnd_3014457 1547865353310417656824271 := by
  unfold tailWord_3014457
  simp only [CollatzResearch.WordTrace]
  refine ⟨109946279240144592113137625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73297519493429728075425083 109946279240144592113137625)
  ·
    refine ⟨82459709430108444084853219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109946279240144592113137625 82459709430108444084853219)
    ·
      refine ⟨123689564145162666127279829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82459709430108444084853219 123689564145162666127279829)
      ·
        refine ⟨2898974159652249987358121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 123689564145162666127279829 2898974159652249987358121)
        ·
          refine ⟨2174230619739187490518591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2898974159652249987358121 2174230619739187490518591)
          ·
            refine ⟨3261345929608781235777887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174230619739187490518591 3261345929608781235777887)
            ·
              refine ⟨4892018894413171853666831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261345929608781235777887 4892018894413171853666831)
              ·
                refine ⟨7338028341619757780500247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892018894413171853666831 7338028341619757780500247)
                ·
                  refine ⟨11007042512429636670750371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338028341619757780500247 11007042512429636670750371)
                  ·
                    refine ⟨16510563768644455006125557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11007042512429636670750371 16510563768644455006125557)
                    ·
                      refine ⟨1547865353310417656824271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16510563768644455006125557 1547865353310417656824271)
                      ·
                        rfl

theorem cell23_3014457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3014457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014457 prefixEnd_3014457 := by exact prefixLift 3014457
  have htrace : WordTrace (prefixWord ++ tailWord_3014457) baseStart_3014457 baseEnd_3014457 := by
    simpa [prefixWord, tailWord_3014457, baseEnd_3014457] using wordTrace_append hprefix tailTrace_3014457
  have hstable : (prefixWord ++ tailWord_3014457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014457).length < 2 ^ (prefixWord ++ tailWord_3014457).sum := by decide
  have hdescent : baseEnd_3014457 < baseStart_3014457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014533 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 5]
def baseStart_3014533 : Nat := 118140960795 + 3014533 * 2 ^ 59
def prefixEnd_3014533 : Nat := 4983230072969 + 3 ^ 40 * 3014533 * 2
def baseEnd_3014533 : Nat := 171989375315573262163769

theorem tailTrace_3014533 : CollatzResearch.WordTrace tailWord_3014533 prefixEnd_3014533 171989375315573262163769 := by
  unfold tailWord_3014533
  simp only [CollatzResearch.WordTrace]
  refine ⟨109949051187869257092904253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73299367458579504728602835 109949051187869257092904253)
  ·
    refine ⟨41230894195450971409839095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109949051187869257092904253 41230894195450971409839095)
    ·
      refine ⟨61846341293176457114758643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41230894195450971409839095 61846341293176457114758643)
      ·
        refine ⟨92769511939764685672137965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61846341293176457114758643 92769511939764685672137965)
        ·
          refine ⟨34788566977411757127051737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92769511939764685672137965 34788566977411757127051737)
          ·
            refine ⟨26091425233058817845288803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34788566977411757127051737 26091425233058817845288803)
            ·
              refine ⟨39137137849588226767933205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26091425233058817845288803 39137137849588226767933205)
              ·
                refine ⟨1834553336699448129746869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39137137849588226767933205 1834553336699448129746869)
                ·
                  refine ⟨171989375315573262163769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1834553336699448129746869 171989375315573262163769)
                  ·
                    rfl

theorem cell23_3014533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_3014533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014533 prefixEnd_3014533 := by exact prefixLift 3014533
  have htrace : WordTrace (prefixWord ++ tailWord_3014533) baseStart_3014533 baseEnd_3014533 := by
    simpa [prefixWord, tailWord_3014533, baseEnd_3014533] using wordTrace_append hprefix tailTrace_3014533
  have hstable : (prefixWord ++ tailWord_3014533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014533).length < 2 ^ (prefixWord ++ tailWord_3014533).sum := by decide
  have hdescent : baseEnd_3014533 < baseStart_3014533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014553 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 2, 5, 2]
def baseStart_3014553 : Nat := 118140960795 + 3014553 * 2 ^ 59
def prefixEnd_3014553 : Nat := 4983230072969 + 3 ^ 40 * 3014553 * 2
def baseEnd_3014553 : Nat := 1547914647453249281223829

theorem tailTrace_3014553 : CollatzResearch.WordTrace tailWord_3014553 prefixEnd_3014553 1547914647453249281223829 := by
  unfold tailWord_3014553
  simp only [CollatzResearch.WordTrace]
  refine ⟨109949780647796800508632313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73299853765197867005754875 109949780647796800508632313)
  ·
    refine ⟨82462335485847600381474235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109949780647796800508632313 82462335485847600381474235)
    ·
      refine ⟨123693503228771400572211353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82462335485847600381474235 123693503228771400572211353)
      ·
        refine ⟨92770127421578550429158515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123693503228771400572211353 92770127421578550429158515)
        ·
          refine ⟨139155191132367825643737773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92770127421578550429158515 139155191132367825643737773)
          ·
            refine ⟨52183196674637934616401665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139155191132367825643737773 52183196674637934616401665)
            ·
              refine ⟨39137397505978450962301249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52183196674637934616401665 39137397505978450962301249)
              ·
                refine ⟨29353048129483838221725937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39137397505978450962301249 29353048129483838221725937)
                ·
                  refine ⟨22014786097112878666294453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29353048129483838221725937 22014786097112878666294453)
                  ·
                    refine ⟨2063886196604332374965105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22014786097112878666294453 2063886196604332374965105)
                    ·
                      refine ⟨1547914647453249281223829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063886196604332374965105 1547914647453249281223829)
                      ·
                        rfl

theorem cell23_3014553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_3014553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014553 prefixEnd_3014553 := by exact prefixLift 3014553
  have htrace : WordTrace (prefixWord ++ tailWord_3014553) baseStart_3014553 baseEnd_3014553 := by
    simpa [prefixWord, tailWord_3014553, baseEnd_3014553] using wordTrace_append hprefix tailTrace_3014553
  have hstable : (prefixWord ++ tailWord_3014553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014553).length < 2 ^ (prefixWord ++ tailWord_3014553).sum := by decide
  have hdescent : baseEnd_3014553 < baseStart_3014553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014567 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 5]
def baseStart_3014567 : Nat := 118140960795 + 3014567 * 2 ^ 59
def prefixEnd_3014567 : Nat := 4983230072969 + 3 ^ 40 * 3014567 * 2
def baseEnd_3014567 : Nat := 171991315131379136272085

theorem tailTrace_3014567 : CollatzResearch.WordTrace tailWord_3014567 prefixEnd_3014567 171991315131379136272085 := by
  unfold tailWord_3014567
  simp only [CollatzResearch.WordTrace]
  refine ⟨109950291269746080899641955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73300194179830720599761303 109950291269746080899641955)
  ·
    refine ⟨164925436904619121349462933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109950291269746080899641955 164925436904619121349462933)
    ·
      refine ⟨7730879854904021313256075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164925436904619121349462933 7730879854904021313256075)
      ·
        refine ⟨11596319782356031969884113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730879854904021313256075 11596319782356031969884113)
        ·
          refine ⟨8697239836767023977413085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11596319782356031969884113 8697239836767023977413085)
          ·
            refine ⟨3261464938787633991529907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8697239836767023977413085 3261464938787633991529907)
            ·
              refine ⟨4892197408181450987294861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261464938787633991529907 4892197408181450987294861)
              ·
                refine ⟨1834574028068044120235573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4892197408181450987294861 1834574028068044120235573)
                ·
                  refine ⟨171991315131379136272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1834574028068044120235573 171991315131379136272085)
                  ·
                    rfl

theorem cell23_3014567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 5].length) (baseStart_3014567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014567 prefixEnd_3014567 := by exact prefixLift 3014567
  have htrace : WordTrace (prefixWord ++ tailWord_3014567) baseStart_3014567 baseEnd_3014567 := by
    simpa [prefixWord, tailWord_3014567, baseEnd_3014567] using wordTrace_append hprefix tailTrace_3014567
  have hstable : (prefixWord ++ tailWord_3014567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014567).length < 2 ^ (prefixWord ++ tailWord_3014567).sum := by decide
  have hdescent : baseEnd_3014567 < baseStart_3014567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014586 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_3014586 : Nat := 118140960795 + 3014586 * 2 ^ 59
def prefixEnd_3014586 : Nat := 4983230072969 + 3 ^ 40 * 3014586 * 2
def baseEnd_3014586 : Nat := 1547931592314847652111177

theorem tailTrace_3014586 : CollatzResearch.WordTrace tailWord_3014586 prefixEnd_3014586 1547931592314847652111177 := by
  unfold tailWord_3014586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27487746064169311786145903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73300656171118164763055741 27487746064169311786145903)
  ·
    refine ⟨41231619096253967679218855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27487746064169311786145903 41231619096253967679218855)
    ·
      refine ⟨61847428644380951518828283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41231619096253967679218855 61847428644380951518828283)
      ·
        refine ⟨92771142966571427278242425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61847428644380951518828283 92771142966571427278242425)
        ·
          refine ⟨69578357224928570458681819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92771142966571427278242425 69578357224928570458681819)
          ·
            refine ⟨104367535837392855688022729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69578357224928570458681819 104367535837392855688022729)
            ·
              refine ⟨78275651878044641766017047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104367535837392855688022729 78275651878044641766017047)
              ·
                refine ⟨117413477817066962649025571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78275651878044641766017047 117413477817066962649025571)
                ·
                  refine ⟨176120216725600443973538357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117413477817066962649025571 176120216725600443973538357)
                  ·
                    refine ⟨16511270318025041622519221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176120216725600443973538357 16511270318025041622519221)
                    ·
                      refine ⟨1547931592314847652111177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16511270318025041622519221 1547931592314847652111177)
                      ·
                        rfl

theorem cell23_3014586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_3014586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014586 prefixEnd_3014586 := by exact prefixLift 3014586
  have htrace : WordTrace (prefixWord ++ tailWord_3014586) baseStart_3014586 baseEnd_3014586 := by
    simpa [prefixWord, tailWord_3014586, baseEnd_3014586] using wordTrace_append hprefix tailTrace_3014586
  have hstable : (prefixWord ++ tailWord_3014586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014586).length < 2 ^ (prefixWord ++ tailWord_3014586).sum := by decide
  have hdescent : baseEnd_3014586 < baseStart_3014586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014603 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 3]
def baseStart_3014603 : Nat := 118140960795 + 3014603 * 2 ^ 59
def prefixEnd_3014603 : Nat := 4983230072969 + 3 ^ 40 * 3014603 * 2
def baseEnd_3014603 : Nat := 1547940321485974085598599

theorem tailTrace_3014603 : CollatzResearch.WordTrace tailWord_3014603 prefixEnd_3014603 1547940321485974085598599 := by
  unfold tailWord_3014603
  simp only [CollatzResearch.WordTrace]
  refine ⟨109951604297615659047952463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73301069531743772698634975 109951604297615659047952463)
  ·
    refine ⟨164927406446423488571928695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109951604297615659047952463 164927406446423488571928695)
    ·
      refine ⟨247391109669635232857893043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164927406446423488571928695 247391109669635232857893043)
      ·
        refine ⟨371086664504452849286839565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247391109669635232857893043 371086664504452849286839565)
        ·
          refine ⟨139157499189169818482564837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371086664504452849286839565 139157499189169818482564837)
          ·
            refine ⟨26092031097969340965480907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139157499189169818482564837 26092031097969340965480907)
            ·
              refine ⟨39138046646954011448221361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26092031097969340965480907 39138046646954011448221361)
              ·
                refine ⟨29353534985215508586166021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39138046646954011448221361 29353534985215508586166021)
                ·
                  refine ⟨5503787809727907859906129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29353534985215508586166021 5503787809727907859906129)
                  ·
                    refine ⟨4127840857295930894929597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503787809727907859906129 4127840857295930894929597)
                    ·
                      refine ⟨1547940321485974085598599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4127840857295930894929597 1547940321485974085598599)
                      ·
                        rfl

theorem cell23_3014603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 3].length) (baseStart_3014603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014603 prefixEnd_3014603 := by exact prefixLift 3014603
  have htrace : WordTrace (prefixWord ++ tailWord_3014603) baseStart_3014603 baseEnd_3014603 := by
    simpa [prefixWord, tailWord_3014603, baseEnd_3014603] using wordTrace_append hprefix tailTrace_3014603
  have hstable : (prefixWord ++ tailWord_3014603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014603).length < 2 ^ (prefixWord ++ tailWord_3014603).sum := by decide
  have hdescent : baseEnd_3014603 < baseStart_3014603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014653 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_3014653 : Nat := 118140960795 + 3014653 * 2 ^ 59
def prefixEnd_3014653 : Nat := 4983230072969 + 3 ^ 40 * 3014653 * 2
def baseEnd_3014653 : Nat := 515988665172899629991123

theorem tailTrace_3014653 : CollatzResearch.WordTrace tailWord_3014653 prefixEnd_3014653 515988665172899629991123 := by
  unfold tailWord_3014653
  simp only [CollatzResearch.WordTrace]
  refine ⟨109953427947434517587272613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73302285298289678391515075 109953427947434517587272613)
  ·
    refine ⟨20616267740143972047613615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109953427947434517587272613 20616267740143972047613615)
    ·
      refine ⟨30924401610215958071420423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20616267740143972047613615 30924401610215958071420423)
      ·
        refine ⟨46386602415323937107130635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30924401610215958071420423 46386602415323937107130635)
        ·
          refine ⟨69579903622985905660695953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46386602415323937107130635 69579903622985905660695953)
          ·
            refine ⟨52184927717239429245521965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69579903622985905660695953 52184927717239429245521965)
            ·
              refine ⟨19569347893964785967070737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52184927717239429245521965 19569347893964785967070737)
              ·
                refine ⟨14677010920473589475303053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19569347893964785967070737 14677010920473589475303053)
                ·
                  refine ⟨5503879095177596053238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14677010920473589475303053 5503879095177596053238645)
                  ·
                    refine ⟨515988665172899629991123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5503879095177596053238645 515988665172899629991123)
                    ·
                      rfl

theorem cell23_3014653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_3014653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014653 prefixEnd_3014653 := by exact prefixLift 3014653
  have htrace : WordTrace (prefixWord ++ tailWord_3014653) baseStart_3014653 baseEnd_3014653 := by
    simpa [prefixWord, tailWord_3014653, baseEnd_3014653] using wordTrace_append hprefix tailTrace_3014653
  have hstable : (prefixWord ++ tailWord_3014653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014653).length < 2 ^ (prefixWord ++ tailWord_3014653).sum := by decide
  have hdescent : baseEnd_3014653 < baseStart_3014653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014670 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3014670 : Nat := 118140960795 + 3014670 * 2 ^ 59
def prefixEnd_3014670 : Nat := 4983230072969 + 3 ^ 40 * 3014670 * 2
def baseEnd_3014670 : Nat := 515991574896608441153597

theorem tailTrace_3014670 : CollatzResearch.WordTrace tailWord_3014670 prefixEnd_3014670 515991574896608441153597 := by
  unfold tailWord_3014670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744255998546616186330183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73302698658915286327094309 13744255998546616186330183)
  ·
    refine ⟨20616383997819924279495275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13744255998546616186330183 20616383997819924279495275)
    ·
      refine ⟨30924575996729886419242913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20616383997819924279495275 30924575996729886419242913)
      ·
        refine ⟨23193431997547414814432185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30924575996729886419242913 23193431997547414814432185)
        ·
          refine ⟨17395073998160561110824139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23193431997547414814432185 17395073998160561110824139)
          ·
            refine ⟨26092610997240841666236209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17395073998160561110824139 26092610997240841666236209)
            ·
              refine ⟨19569458247930631249677157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26092610997240841666236209 19569458247930631249677157)
              ·
                refine ⟨3669273421486993359314467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19569458247930631249677157 3669273421486993359314467)
                ·
                  refine ⟨5503910132230490038971701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669273421486993359314467 5503910132230490038971701)
                  ·
                    refine ⟨515991574896608441153597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5503910132230490038971701 515991574896608441153597)
                    ·
                      rfl

theorem cell23_3014670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3014670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014670 prefixEnd_3014670 := by exact prefixLift 3014670
  have htrace : WordTrace (prefixWord ++ tailWord_3014670) baseStart_3014670 baseEnd_3014670 := by
    simpa [prefixWord, tailWord_3014670, baseEnd_3014670] using wordTrace_append hprefix tailTrace_3014670
  have hstable : (prefixWord ++ tailWord_3014670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014670).length < 2 ^ (prefixWord ++ tailWord_3014670).sum := by decide
  have hdescent : baseEnd_3014670 < baseStart_3014670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014677 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_3014677 : Nat := 118140960795 + 3014677 * 2 ^ 59
def prefixEnd_3014677 : Nat := 4983230072969 + 3 ^ 40 * 3014677 * 2
def baseEnd_3014677 : Nat := 1547978319054406796073259

theorem tailTrace_3014677 : CollatzResearch.WordTrace tailWord_3014677 prefixEnd_3014677 1547978319054406796073259 := by
  unfold tailWord_3014677
  simp only [CollatzResearch.WordTrace]
  refine ⟨109954303299347569686146285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73302868866231713124097523 109954303299347569686146285)
  ·
    refine ⟨41232863737255338632304857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109954303299347569686146285 41232863737255338632304857)
    ·
      refine ⟨30924647802941503974228643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41232863737255338632304857 30924647802941503974228643)
      ·
        refine ⟨46386971704412255961342965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30924647802941503974228643 46386971704412255961342965)
        ·
          refine ⟨4348778597288648996375903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46386971704412255961342965 4348778597288648996375903)
          ·
            refine ⟨6523167895932973494563855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4348778597288648996375903 6523167895932973494563855)
            ·
              refine ⟨9784751843899460241845783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6523167895932973494563855 9784751843899460241845783)
              ·
                refine ⟨14677127765849190362768675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9784751843899460241845783 14677127765849190362768675)
                ·
                  refine ⟨22015691648773785544153013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14677127765849190362768675 22015691648773785544153013)
                  ·
                    refine ⟨2063971092072542394764345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22015691648773785544153013 2063971092072542394764345)
                    ·
                      refine ⟨1547978319054406796073259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063971092072542394764345 1547978319054406796073259)
                      ·
                        rfl

theorem cell23_3014677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_3014677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014677 prefixEnd_3014677 := by exact prefixLift 3014677
  have htrace : WordTrace (prefixWord ++ tailWord_3014677) baseStart_3014677 baseEnd_3014677 := by
    simpa [prefixWord, tailWord_3014677, baseEnd_3014677] using wordTrace_append hprefix tailTrace_3014677
  have hstable : (prefixWord ++ tailWord_3014677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014677).length < 2 ^ (prefixWord ++ tailWord_3014677).sum := by decide
  have hdescent : baseEnd_3014677 < baseStart_3014677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014684 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_3014684 : Nat := 118140960795 + 3014684 * 2 ^ 59
def prefixEnd_3014684 : Nat := 4983230072969 + 3 ^ 40 * 3014684 * 2
def baseEnd_3014684 : Nat := 1547981913418988268685727

theorem tailTrace_3014684 : CollatzResearch.WordTrace tailWord_3014684 prefixEnd_3014684 1547981913418988268685727 := by
  unfold tailWord_3014684
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977279305161104940825553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73303039073548139921100737 54977279305161104940825553)
  ·
    refine ⟨41232959478870828705619165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54977279305161104940825553 41232959478870828705619165)
    ·
      refine ⟨15462359804576560764607187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41232959478870828705619165 15462359804576560764607187)
      ·
        refine ⟨23193539706864841146910781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15462359804576560764607187 23193539706864841146910781)
        ·
          refine ⟨8697577390074315430091543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23193539706864841146910781 8697577390074315430091543)
          ·
            refine ⟨13046366085111473145137315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697577390074315430091543 13046366085111473145137315)
            ·
              refine ⟨19569549127667209717705973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13046366085111473145137315 19569549127667209717705973)
              ·
                refine ⟨1834645230718800911034935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19569549127667209717705973 1834645230718800911034935)
                ·
                  refine ⟨2751967846078201366552403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834645230718800911034935 2751967846078201366552403)
                  ·
                    refine ⟨4127951769117302049828605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2751967846078201366552403 4127951769117302049828605)
                    ·
                      refine ⟨1547981913418988268685727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4127951769117302049828605 1547981913418988268685727)
                      ·
                        rfl

theorem cell23_3014684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_3014684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014684 prefixEnd_3014684 := by exact prefixLift 3014684
  have htrace : WordTrace (prefixWord ++ tailWord_3014684) baseStart_3014684 baseEnd_3014684 := by
    simpa [prefixWord, tailWord_3014684, baseEnd_3014684] using wordTrace_append hprefix tailTrace_3014684
  have hstable : (prefixWord ++ tailWord_3014684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014684).length < 2 ^ (prefixWord ++ tailWord_3014684).sum := by decide
  have hdescent : baseEnd_3014684 < baseStart_3014684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014700 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_3014700 : Nat := 118140960795 + 3014700 * 2 ^ 59
def prefixEnd_3014700 : Nat := 4983230072969 + 3 ^ 40 * 3014700 * 2
def baseEnd_3014700 : Nat := 515996709703153402028551

theorem tailTrace_3014700 : CollatzResearch.WordTrace tailWord_3014700 prefixEnd_3014700 515996709703153402028551 := by
  unfold tailWord_3014700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977571089132122307116777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73303428118842829742822369 54977571089132122307116777)
  ·
    refine ⟨41233178316849091730337583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54977571089132122307116777 41233178316849091730337583)
    ·
      refine ⟨61849767475273637595506375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41233178316849091730337583 61849767475273637595506375)
      ·
        refine ⟨92774651212910456393259563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61849767475273637595506375 92774651212910456393259563)
        ·
          refine ⟨139161976819365684589889345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92774651212910456393259563 139161976819365684589889345)
          ·
            refine ⟨104371482614524263442417009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139161976819365684589889345 104371482614524263442417009)
            ·
              refine ⟨78278611960893197581812757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104371482614524263442417009 78278611960893197581812757)
              ·
                refine ⟨3669309935666868636647473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78278611960893197581812757 3669309935666868636647473)
                ·
                  refine ⟨2751982451750151477485605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3669309935666868636647473 2751982451750151477485605)
                  ·
                    refine ⟨515996709703153402028551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751982451750151477485605 515996709703153402028551)
                    ·
                      rfl

theorem cell23_3014700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_3014700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014700 prefixEnd_3014700 := by exact prefixLift 3014700
  have htrace : WordTrace (prefixWord ++ tailWord_3014700) baseStart_3014700 baseEnd_3014700 := by
    simpa [prefixWord, tailWord_3014700, baseEnd_3014700] using wordTrace_append hprefix tailTrace_3014700
  have hstable : (prefixWord ++ tailWord_3014700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014700).length < 2 ^ (prefixWord ++ tailWord_3014700).sum := by decide
  have hdescent : baseEnd_3014700 < baseStart_3014700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014707 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 3, 2, 2]
def baseStart_3014707 : Nat := 118140960795 + 3014707 * 2 ^ 59
def prefixEnd_3014707 : Nat := 4983230072969 + 3 ^ 40 * 3014707 * 2
def baseEnd_3014707 : Nat := 1547993723474041678698121

theorem tailTrace_3014707 : CollatzResearch.WordTrace tailWord_3014707 prefixEnd_3014707 1547993723474041678698121 := by
  unfold tailWord_3014707
  simp only [CollatzResearch.WordTrace]
  refine ⟨109955397489238884809738375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73303598326159256539825583 109955397489238884809738375)
  ·
    refine ⟨164933096233858327214607563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109955397489238884809738375 164933096233858327214607563)
    ·
      refine ⟨247399644350787490821911345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164933096233858327214607563 247399644350787490821911345)
      ·
        refine ⟨185549733263090618116433509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247399644350787490821911345 185549733263090618116433509)
        ·
          refine ⟨34790574986829490896831283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185549733263090618116433509 34790574986829490896831283)
          ·
            refine ⟨52185862480244236345246925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34790574986829490896831283 52185862480244236345246925)
            ·
              refine ⟨19569698430091588629467597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52185862480244236345246925 19569698430091588629467597)
              ·
                refine ⟨7338636911284345736050349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19569698430091588629467597 7338636911284345736050349)
                ·
                  refine ⟨2751988841731629651018881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7338636911284345736050349 2751988841731629651018881)
                  ·
                    refine ⟨2063991631298722238264161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2751988841731629651018881 2063991631298722238264161)
                    ·
                      refine ⟨1547993723474041678698121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2063991631298722238264161 1547993723474041678698121)
                      ·
                        rfl

theorem cell23_3014707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 2, 2].length) (baseStart_3014707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014707 prefixEnd_3014707 := by exact prefixLift 3014707
  have htrace : WordTrace (prefixWord ++ tailWord_3014707) baseStart_3014707 baseEnd_3014707 := by
    simpa [prefixWord, tailWord_3014707, baseEnd_3014707] using wordTrace_append hprefix tailTrace_3014707
  have hstable : (prefixWord ++ tailWord_3014707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014707).length < 2 ^ (prefixWord ++ tailWord_3014707).sum := by decide
  have hdescent : baseEnd_3014707 < baseStart_3014707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014720 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_3014720 : Nat := 118140960795 + 3014720 * 2 ^ 59
def prefixEnd_3014720 : Nat := 4983230072969 + 3 ^ 40 * 3014720 * 2
def baseEnd_3014720 : Nat := 1548000398722550127835561

theorem tailTrace_3014720 : CollatzResearch.WordTrace tailWord_3014720 prefixEnd_3014720 1548000398722550127835561 := by
  unfold tailWord_3014720
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977935819095894014980807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73303914425461192019974409 54977935819095894014980807)
  ·
    refine ⟨82466903728643841022471211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54977935819095894014980807 82466903728643841022471211)
    ·
      refine ⟨123700355592965761533706817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82466903728643841022471211 123700355592965761533706817)
      ·
        refine ⟨92775266694724321150280113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123700355592965761533706817 92775266694724321150280113)
        ·
          refine ⟨69581450021043240862710085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92775266694724321150280113 69581450021043240862710085)
          ·
            refine ⟨13046521878945607661758141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69581450021043240862710085 13046521878945607661758141)
            ·
              refine ⟨4892445704604602873159303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13046521878945607661758141 4892445704604602873159303)
              ·
                refine ⟨7338668556906904309738955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892445704604602873159303 7338668556906904309738955)
                ·
                  refine ⟨11008002835360356464608433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338668556906904309738955 11008002835360356464608433)
                  ·
                    refine ⟨8256002126520267348456325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11008002835360356464608433 8256002126520267348456325)
                    ·
                      refine ⟨1548000398722550127835561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8256002126520267348456325 1548000398722550127835561)
                      ·
                        rfl

theorem cell23_3014720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_3014720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014720 prefixEnd_3014720 := by exact prefixLift 3014720
  have htrace : WordTrace (prefixWord ++ tailWord_3014720) baseStart_3014720 baseEnd_3014720 := by
    simpa [prefixWord, tailWord_3014720, baseEnd_3014720] using wordTrace_append hprefix tailTrace_3014720
  have hstable : (prefixWord ++ tailWord_3014720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014720).length < 2 ^ (prefixWord ++ tailWord_3014720).sum := by decide
  have hdescent : baseEnd_3014720 < baseStart_3014720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014727 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_3014727 : Nat := 118140960795 + 3014727 * 2 ^ 59
def prefixEnd_3014727 : Nat := 4983230072969 + 3 ^ 40 * 3014727 * 2
def baseEnd_3014727 : Nat := 1548003993087131600448029

theorem tailTrace_3014727 : CollatzResearch.WordTrace tailWord_3014727 prefixEnd_3014727 1548003993087131600448029 := by
  unfold tailWord_3014727
  simp only [CollatzResearch.WordTrace]
  refine ⟨109956126949166428225466435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73304084632777618816977623 109956126949166428225466435)
  ·
    refine ⟨164934190423749642338199653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109956126949166428225466435 164934190423749642338199653)
    ·
      refine ⟨30925160704453057938412435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164934190423749642338199653 30925160704453057938412435)
      ·
        refine ⟨46387741056679586907618653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30925160704453057938412435 46387741056679586907618653)
        ·
          refine ⟨17395402896254845090356995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46387741056679586907618653 17395402896254845090356995)
          ·
            refine ⟨26093104344382267635535493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17395402896254845090356995 26093104344382267635535493)
            ·
              refine ⟨4892457064571675181662905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26093104344382267635535493 4892457064571675181662905)
              ·
                refine ⟨3669342798428756386247179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892457064571675181662905 3669342798428756386247179)
                ·
                  refine ⟨5504014197643134579370769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669342798428756386247179 5504014197643134579370769)
                  ·
                    refine ⟨4128010648232350934528077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5504014197643134579370769 4128010648232350934528077)
                    ·
                      refine ⟨1548003993087131600448029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4128010648232350934528077 1548003993087131600448029)
                      ·
                        rfl

theorem cell23_3014727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_3014727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014727 prefixEnd_3014727 := by exact prefixLift 3014727
  have htrace : WordTrace (prefixWord ++ tailWord_3014727) baseStart_3014727 baseEnd_3014727 := by
    simpa [prefixWord, tailWord_3014727, baseEnd_3014727] using wordTrace_append hprefix tailTrace_3014727
  have hstable : (prefixWord ++ tailWord_3014727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014727).length < 2 ^ (prefixWord ++ tailWord_3014727).sum := by decide
  have hdescent : baseEnd_3014727 < baseStart_3014727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014740 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3014740 : Nat := 118140960795 + 3014740 * 2 ^ 59
def prefixEnd_3014740 : Nat := 4983230072969 + 3 ^ 40 * 3014740 * 2
def baseEnd_3014740 : Nat := 1548010668335640049585469

theorem tailTrace_3014740 : CollatzResearch.WordTrace tailWord_3014740 prefixEnd_3014740 1548010668335640049585469 := by
  unfold tailWord_3014740
  simp only [CollatzResearch.WordTrace]
  refine ⟨54978300549059665722844837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73304400732079554297126449 54978300549059665722844837)
  ·
    refine ⟨10308431352948687323033407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54978300549059665722844837 10308431352948687323033407)
    ·
      refine ⟨15462647029423030984550111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10308431352948687323033407 15462647029423030984550111)
      ·
        refine ⟨23193970544134546476825167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15462647029423030984550111 23193970544134546476825167)
        ·
          refine ⟨34790955816201819715237751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23193970544134546476825167 34790955816201819715237751)
          ·
            refine ⟨52186433724302729572856627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34790955816201819715237751 52186433724302729572856627)
            ·
              refine ⟨78279650586454094359284941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52186433724302729572856627 78279650586454094359284941)
              ·
                refine ⟨29354868969920285384731853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78279650586454094359284941 29354868969920285384731853)
                ·
                  refine ⟨11008075863720107019274445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29354868969920285384731853 11008075863720107019274445)
                  ·
                    refine ⟨4128028448895040132227917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11008075863720107019274445 4128028448895040132227917)
                    ·
                      refine ⟨1548010668335640049585469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4128028448895040132227917 1548010668335640049585469)
                      ·
                        rfl

theorem cell23_3014740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3014740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014740 prefixEnd_3014740 := by exact prefixLift 3014740
  have htrace : WordTrace (prefixWord ++ tailWord_3014740) baseStart_3014740 baseEnd_3014740 := by
    simpa [prefixWord, tailWord_3014740, baseEnd_3014740] using wordTrace_append hprefix tailTrace_3014740
  have hstable : (prefixWord ++ tailWord_3014740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014740).length < 2 ^ (prefixWord ++ tailWord_3014740).sum := by decide
  have hdescent : baseEnd_3014740 < baseStart_3014740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014741 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_3014741 : Nat := 118140960795 + 3014741 * 2 ^ 59
def prefixEnd_3014741 : Nat := 4983230072969 + 3 ^ 40 * 3014741 * 2
def baseEnd_3014741 : Nat := 1548011181816294545672965

theorem tailTrace_3014741 : CollatzResearch.WordTrace tailWord_3014741 prefixEnd_3014741 1548011181816294545672965 := by
  unfold tailWord_3014741
  simp only [CollatzResearch.WordTrace]
  refine ⟨109956637571115708616476077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73304425047410472410984051 109956637571115708616476077)
  ·
    refine ⟨41233739089168390731178529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109956637571115708616476077 41233739089168390731178529)
    ·
      refine ⟨30925304316876293048383897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41233739089168390731178529 30925304316876293048383897)
      ·
        refine ⟨23193978237657219786287923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30925304316876293048383897 23193978237657219786287923)
        ·
          refine ⟨34790967356485829679431885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23193978237657219786287923 34790967356485829679431885)
          ·
            refine ⟨13046612758682186129786957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34790967356485829679431885 13046612758682186129786957)
            ·
              refine ⟨4892479784505819798670109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13046612758682186129786957 4892479784505819798670109)
              ·
                refine ⟨1834679919189682424501291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4892479784505819798670109 1834679919189682424501291)
                ·
                  refine ⟨2752019878784523636751937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834679919189682424501291 2752019878784523636751937)
                  ·
                    refine ⟨2064014909088392727563953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2752019878784523636751937 2064014909088392727563953)
                    ·
                      refine ⟨1548011181816294545672965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064014909088392727563953 1548011181816294545672965)
                      ·
                        rfl

theorem cell23_3014741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_3014741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014741 prefixEnd_3014741 := by exact prefixLift 3014741
  have htrace : WordTrace (prefixWord ++ tailWord_3014741) baseStart_3014741 baseEnd_3014741 := by
    simpa [prefixWord, tailWord_3014741, baseEnd_3014741] using wordTrace_append hprefix tailTrace_3014741
  have hstable : (prefixWord ++ tailWord_3014741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014741).length < 2 ^ (prefixWord ++ tailWord_3014741).sum := by decide
  have hdescent : baseEnd_3014741 < baseStart_3014741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014753 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3014753 : Nat := 118140960795 + 3014753 * 2 ^ 59
def prefixEnd_3014753 : Nat := 4983230072969 + 3 ^ 40 * 3014753 * 2
def baseEnd_3014753 : Nat := 1548017343584148498722909

theorem tailTrace_3014753 : CollatzResearch.WordTrace tailWord_3014753 prefixEnd_3014753 1548017343584148498722909 := by
  unfold tailWord_3014753
  simp only [CollatzResearch.WordTrace]
  refine ⟨109957075247072234665912913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73304716831381489777275275 109957075247072234665912913)
  ·
    refine ⟨82467806435304175999434685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109957075247072234665912913 82467806435304175999434685)
    ·
      refine ⟨30925427413239065999788007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82467806435304175999434685 30925427413239065999788007)
      ·
        refine ⟨46388141119858598999682011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30925427413239065999788007 46388141119858598999682011)
        ·
          refine ⟨69582211679787898499523017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46388141119858598999682011 69582211679787898499523017)
          ·
            refine ⟨52186658759840923874642263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69582211679787898499523017 52186658759840923874642263)
            ·
              refine ⟨78279988139761385811963395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52186658759840923874642263 78279988139761385811963395)
              ·
                refine ⟨117419982209642078717945093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78279988139761385811963395 117419982209642078717945093)
                ·
                  refine ⟨22016246664307889759614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117419982209642078717945093 22016246664307889759614705)
                  ·
                    refine ⟨16512184998230917319711029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22016246664307889759614705 16512184998230917319711029)
                    ·
                      refine ⟨1548017343584148498722909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16512184998230917319711029 1548017343584148498722909)
                      ·
                        rfl

theorem cell23_3014753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3014753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014753 prefixEnd_3014753 := by exact prefixLift 3014753
  have htrace : WordTrace (prefixWord ++ tailWord_3014753) baseStart_3014753 baseEnd_3014753 := by
    simpa [prefixWord, tailWord_3014753, baseEnd_3014753] using wordTrace_append hprefix tailTrace_3014753
  have hstable : (prefixWord ++ tailWord_3014753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014753).length < 2 ^ (prefixWord ++ tailWord_3014753).sum := by decide
  have hdescent : baseEnd_3014753 < baseStart_3014753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014757 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_3014757 : Nat := 118140960795 + 3014757 * 2 ^ 59
def prefixEnd_3014757 : Nat := 4983230072969 + 3 ^ 40 * 3014757 * 2
def baseEnd_3014757 : Nat := 1548019397506766483072891

theorem tailTrace_3014757 : CollatzResearch.WordTrace tailWord_3014757 prefixEnd_3014757 1548019397506766483072891 := by
  unfold tailWord_3014757
  simp only [CollatzResearch.WordTrace]
  refine ⟨109957221139057743349058525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73304814092705162232705683 109957221139057743349058525)
  ·
    refine ⟨41233957927146653755896947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109957221139057743349058525 41233957927146653755896947)
    ·
      refine ⟨61850936890719980633845421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41233957927146653755896947 61850936890719980633845421)
      ·
        refine ⟨23194101334019992737692033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61850936890719980633845421 23194101334019992737692033)
        ·
          refine ⟨17395576000514994553269025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23194101334019992737692033 17395576000514994553269025)
          ·
            refine ⟨13046682000386245914951769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17395576000514994553269025 13046682000386245914951769)
            ·
              refine ⟨9785011500289684436213827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13046682000386245914951769 9785011500289684436213827)
              ·
                refine ⟨14677517250434526654320741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9785011500289684436213827 14677517250434526654320741)
                ·
                  refine ⟨2752034484456473747685139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14677517250434526654320741 2752034484456473747685139)
                  ·
                    refine ⟨4128051726684710621527709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2752034484456473747685139 4128051726684710621527709)
                    ·
                      refine ⟨1548019397506766483072891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4128051726684710621527709 1548019397506766483072891)
                      ·
                        rfl

theorem cell23_3014757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_3014757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014757 prefixEnd_3014757 := by exact prefixLift 3014757
  have htrace : WordTrace (prefixWord ++ tailWord_3014757) baseStart_3014757 baseEnd_3014757 := by
    simpa [prefixWord, tailWord_3014757, baseEnd_3014757] using wordTrace_append hprefix tailTrace_3014757
  have hstable : (prefixWord ++ tailWord_3014757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014757).length < 2 ^ (prefixWord ++ tailWord_3014757).sum := by decide
  have hdescent : baseEnd_3014757 < baseStart_3014757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014882 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3014882 : Nat := 118140960795 + 3014882 * 2 ^ 59
def prefixEnd_3014882 : Nat := 4983230072969 + 3 ^ 40 * 3014882 * 2
def baseEnd_3014882 : Nat := 1548083582588578494009817

theorem tailTrace_3014882 : CollatzResearch.WordTrace tailWord_3014882 prefixEnd_3014882 1548083582588578494009817 := by
  unfold tailWord_3014882
  simp only [CollatzResearch.WordTrace]
  refine ⟨27490445065901222424339725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73307853509069926464905933 27490445065901222424339725)
  ·
    refine ⟨10308916899712958409127397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27490445065901222424339725 10308916899712958409127397)
    ·
      refine ⟨1932921918696179701711387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10308916899712958409127397 1932921918696179701711387)
      ·
        refine ⟨2899382878044269552567081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932921918696179701711387 2899382878044269552567081)
        ·
          refine ⟨2174537158533202164425311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2899382878044269552567081 2174537158533202164425311)
          ·
            refine ⟨3261805737799803246637967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174537158533202164425311 3261805737799803246637967)
            ·
              refine ⟨4892708606699704869956951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261805737799803246637967 4892708606699704869956951)
              ·
                refine ⟨7339062910049557304935427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892708606699704869956951 7339062910049557304935427)
                ·
                  refine ⟨11008594365074335957403141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7339062910049557304935427 11008594365074335957403141)
                  ·
                    refine ⟨2064111443451437992013089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11008594365074335957403141 2064111443451437992013089)
                    ·
                      refine ⟨1548083582588578494009817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064111443451437992013089 1548083582588578494009817)
                      ·
                        rfl

theorem cell23_3014882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3014882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014882 prefixEnd_3014882 := by exact prefixLift 3014882
  have htrace : WordTrace (prefixWord ++ tailWord_3014882) baseStart_3014882 baseEnd_3014882 := by
    simpa [prefixWord, tailWord_3014882, baseEnd_3014882] using wordTrace_append hprefix tailTrace_3014882
  have hstable : (prefixWord ++ tailWord_3014882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014882).length < 2 ^ (prefixWord ++ tailWord_3014882).sum := by decide
  have hdescent : baseEnd_3014882 < baseStart_3014882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014887 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3014887 : Nat := 118140960795 + 3014887 * 2 ^ 59
def prefixEnd_3014887 : Nat := 4983230072969 + 3 ^ 40 * 3014887 * 2
def baseEnd_3014887 : Nat := 1548086149991850974447293

theorem tailTrace_3014887 : CollatzResearch.WordTrace tailWord_3014887 prefixEnd_3014887 1548086149991850974447293 := by
  unfold tailWord_3014887
  simp only [CollatzResearch.WordTrace]
  refine ⟨109961962628586775551290915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73307975085724517034193943 109961962628586775551290915)
  ·
    refine ⟨164942943942880163326936373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109961962628586775551290915 164942943942880163326936373)
    ·
      refine ⟨15463400994645015311900285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164942943942880163326936373 15463400994645015311900285)
      ·
        refine ⟨5798775372991880741962607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15463400994645015311900285 5798775372991880741962607)
        ·
          refine ⟨8698163059487821112943911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798775372991880741962607 8698163059487821112943911)
          ·
            refine ⟨13047244589231731669415867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698163059487821112943911 13047244589231731669415867)
            ·
              refine ⟨19570866883847597504123801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13047244589231731669415867 19570866883847597504123801)
              ·
                refine ⟨14678150162885698128092851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19570866883847597504123801 14678150162885698128092851)
                ·
                  refine ⟨22017225244328547192139277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14678150162885698128092851 22017225244328547192139277)
                  ·
                    refine ⟨8256459466623205197052229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22017225244328547192139277 8256459466623205197052229)
                    ·
                      refine ⟨1548086149991850974447293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8256459466623205197052229 1548086149991850974447293)
                      ·
                        rfl

theorem cell23_3014887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3014887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014887 prefixEnd_3014887 := by exact prefixLift 3014887
  have htrace : WordTrace (prefixWord ++ tailWord_3014887) baseStart_3014887 baseEnd_3014887 := by
    simpa [prefixWord, tailWord_3014887, baseEnd_3014887] using wordTrace_append hprefix tailTrace_3014887
  have hstable : (prefixWord ++ tailWord_3014887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014887).length < 2 ^ (prefixWord ++ tailWord_3014887).sum := by decide
  have hdescent : baseEnd_3014887 < baseStart_3014887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014897 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 3, 4]
def baseStart_3014897 : Nat := 118140960795 + 3014897 * 2 ^ 59
def prefixEnd_3014897 : Nat := 4983230072969 + 3 ^ 40 * 3014897 * 2
def baseEnd_3014897 : Nat := 516030428266131978440749

theorem tailTrace_3014897 : CollatzResearch.WordTrace tailWord_3014897 prefixEnd_3014897 516030428266131978440749 := by
  unfold tailWord_3014897
  simp only [CollatzResearch.WordTrace]
  refine ⟨109962327358550547259154945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73308218239033698172769963 109962327358550547259154945)
  ·
    refine ⟨82471745518912910444366209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109962327358550547259154945 82471745518912910444366209)
    ·
      refine ⟨61853809139184682833274657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82471745518912910444366209 61853809139184682833274657)
      ·
        refine ⟨46390356854388512124955993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61853809139184682833274657 46390356854388512124955993)
        ·
          refine ⟨34792767640791384093716995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46390356854388512124955993 34792767640791384093716995)
          ·
            refine ⟨52189151461187076140575493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34792767640791384093716995 52189151461187076140575493)
            ·
              refine ⟨9785465898972576776357905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52189151461187076140575493 9785465898972576776357905)
              ·
                refine ⟨7339099424229432582268429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9785465898972576776357905 7339099424229432582268429)
                ·
                  refine ⟨2752162284086037218350661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7339099424229432582268429 2752162284086037218350661)
                  ·
                    refine ⟨516030428266131978440749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2752162284086037218350661 516030428266131978440749)
                    ·
                      rfl

theorem cell23_3014897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_3014897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014897 prefixEnd_3014897 := by exact prefixLift 3014897
  have htrace : WordTrace (prefixWord ++ tailWord_3014897) baseStart_3014897 baseEnd_3014897 := by
    simpa [prefixWord, tailWord_3014897, baseEnd_3014897] using wordTrace_append hprefix tailTrace_3014897
  have hstable : (prefixWord ++ tailWord_3014897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014897).length < 2 ^ (prefixWord ++ tailWord_3014897).sum := by decide
  have hdescent : baseEnd_3014897 < baseStart_3014897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014940 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_3014940 : Nat := 118140960795 + 3014940 * 2 ^ 59
def prefixEnd_3014940 : Nat := 4983230072969 + 3 ^ 40 * 3014940 * 2
def baseEnd_3014940 : Nat := 516037788155513089028183

theorem tailTrace_3014940 : CollatzResearch.WordTrace tailWord_3014940 prefixEnd_3014940 516037788155513089028183 := by
  unfold tailWord_3014940
  simp only [CollatzResearch.WordTrace]
  refine ⟨54981947848697382801485137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73309263798263177068646849 54981947848697382801485137)
  ·
    refine ⟨41236460886523037101113853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54981947848697382801485137 41236460886523037101113853)
    ·
      refine ⟨15463672832446138912917695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41236460886523037101113853 15463672832446138912917695)
      ·
        refine ⟨23195509248669208369376543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15463672832446138912917695 23195509248669208369376543)
        ·
          refine ⟨34793263873003812554064815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23195509248669208369376543 34793263873003812554064815)
          ·
            refine ⟨52189895809505718831097223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34793263873003812554064815 52189895809505718831097223)
            ·
              refine ⟨78284843714258578246645835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52189895809505718831097223 78284843714258578246645835)
              ·
                refine ⟨117427265571387867369968753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78284843714258578246645835 117427265571387867369968753)
                ·
                  refine ⟨88070449178540900527476565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117427265571387867369968753 88070449178540900527476565)
                  ·
                    refine ⟨516037788155513089028183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 88070449178540900527476565 516037788155513089028183)
                    ·
                      rfl

theorem cell23_3014940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_3014940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014940 prefixEnd_3014940 := by exact prefixLift 3014940
  have htrace : WordTrace (prefixWord ++ tailWord_3014940) baseStart_3014940 baseEnd_3014940 := by
    simpa [prefixWord, tailWord_3014940, baseEnd_3014940] using wordTrace_append hprefix tailTrace_3014940
  have hstable : (prefixWord ++ tailWord_3014940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014940).length < 2 ^ (prefixWord ++ tailWord_3014940).sum := by decide
  have hdescent : baseEnd_3014940 < baseStart_3014940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014944 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 6]
def baseStart_3014944 : Nat := 118140960795 + 3014944 * 2 ^ 59
def prefixEnd_3014944 : Nat := 4983230072969 + 3 ^ 40 * 3014944 * 2
def baseEnd_3014944 : Nat := 172012824265461916826059

theorem tailTrace_3014944 : CollatzResearch.WordTrace tailWord_3014944 prefixEnd_3014944 172012824265461916826059 := by
  unfold tailWord_3014944
  simp only [CollatzResearch.WordTrace]
  refine ⟨54982020794690137143057943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73309361059586849524077257 54982020794690137143057943)
  ·
    refine ⟨82473031192035205714586915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54982020794690137143057943 82473031192035205714586915)
    ·
      refine ⟨123709546788052808571880373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82473031192035205714586915 123709546788052808571880373)
      ·
        refine ⟨11597770011379950803613785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123709546788052808571880373 11597770011379950803613785)
        ·
          refine ⟨8698327508534963102710339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11597770011379950803613785 8698327508534963102710339)
          ·
            refine ⟨13047491262802444654065509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698327508534963102710339 13047491262802444654065509)
            ·
              refine ⟨2446404611775458372637283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13047491262802444654065509 2446404611775458372637283)
              ·
                refine ⟨3669606917663187558955925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446404611775458372637283 3669606917663187558955925)
                ·
                  refine ⟨172012824265461916826059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3669606917663187558955925 172012824265461916826059)
                  ·
                    rfl

theorem cell23_3014944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 6].length) (baseStart_3014944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014944 prefixEnd_3014944 := by exact prefixLift 3014944
  have htrace : WordTrace (prefixWord ++ tailWord_3014944) baseStart_3014944 baseEnd_3014944 := by
    simpa [prefixWord, tailWord_3014944, baseEnd_3014944] using wordTrace_append hprefix tailTrace_3014944
  have hstable : (prefixWord ++ tailWord_3014944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014944).length < 2 ^ (prefixWord ++ tailWord_3014944).sum := by decide
  have hdescent : baseEnd_3014944 < baseStart_3014944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3014958 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3014958 : Nat := 118140960795 + 3014958 * 2 ^ 59
def prefixEnd_3014958 : Nat := 4983230072969 + 3 ^ 40 * 3014958 * 2
def baseEnd_3014958 : Nat := 1548122607118320196659467

theorem tailTrace_3014958 : CollatzResearch.WordTrace tailWord_3014958 prefixEnd_3014958 1548122607118320196659467 := by
  unfold tailWord_3014958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745569026416194334640691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73309701474219703118083685 13745569026416194334640691)
  ·
    refine ⟨20618353539624291501961037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13745569026416194334640691 20618353539624291501961037)
    ·
      refine ⟨7731882577359109313235389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20618353539624291501961037 7731882577359109313235389)
      ·
        refine ⟨2899455966509665992463271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7731882577359109313235389 2899455966509665992463271)
        ·
          refine ⟨4349183949764498988694907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899455966509665992463271 4349183949764498988694907)
          ·
            refine ⟨6523775924646748483042361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349183949764498988694907 6523775924646748483042361)
            ·
              refine ⟨4892831943485061362281771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6523775924646748483042361 4892831943485061362281771)
              ·
                refine ⟨7339247915227592043422657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892831943485061362281771 7339247915227592043422657)
                ·
                  refine ⟨5504435936420694032566993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339247915227592043422657 5504435936420694032566993)
                  ·
                    refine ⟨4128326952315520524425245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5504435936420694032566993 4128326952315520524425245)
                    ·
                      refine ⟨1548122607118320196659467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4128326952315520524425245 1548122607118320196659467)
                      ·
                        rfl

theorem cell23_3014958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3014958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3014958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3014958 prefixEnd_3014958 := by exact prefixLift 3014958
  have htrace : WordTrace (prefixWord ++ tailWord_3014958) baseStart_3014958 baseEnd_3014958 := by
    simpa [prefixWord, tailWord_3014958, baseEnd_3014958] using wordTrace_append hprefix tailTrace_3014958
  have hstable : (prefixWord ++ tailWord_3014958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3014958).length < 2 ^ (prefixWord ++ tailWord_3014958).sum := by decide
  have hdescent : baseEnd_3014958 < baseStart_3014958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3014958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015000 : List Nat := [2, 1, 2, 2, 1, 1, 2, 12]
def baseStart_3015000 : Nat := 118140960795 + 3015000 * 2 ^ 59
def prefixEnd_3015000 : Nat := 4983230072969 + 3 ^ 40 * 3015000 * 2
def baseEnd_3015000 : Nat := 57338673085400334530899

theorem tailTrace_3015000 : CollatzResearch.WordTrace tailWord_3015000 prefixEnd_3015000 57338673085400334530899 := by
  unfold tailWord_3015000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54983042038588697925077227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73310722718118263900102969 54983042038588697925077227)
  ·
    refine ⟨82474563057883046887615841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54983042038588697925077227 82474563057883046887615841)
    ·
      refine ⟨61855922293412285165711881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82474563057883046887615841 61855922293412285165711881)
      ·
        refine ⟨46391941720059213874283911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61855922293412285165711881 46391941720059213874283911)
        ·
          refine ⟨69587912580088820811425867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46391941720059213874283911 69587912580088820811425867)
          ·
            refine ⟨104381868870133231217138801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69587912580088820811425867 104381868870133231217138801)
            ·
              refine ⟨78286401652599923412854101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104381868870133231217138801 78286401652599923412854101)
              ·
                refine ⟨57338673085400334530899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 78286401652599923412854101 57338673085400334530899)
                ·
                  rfl

theorem cell23_3015000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 12].length) (baseStart_3015000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015000 prefixEnd_3015000 := by exact prefixLift 3015000
  have htrace : WordTrace (prefixWord ++ tailWord_3015000) baseStart_3015000 baseEnd_3015000 := by
    simpa [prefixWord, tailWord_3015000, baseEnd_3015000] using wordTrace_append hprefix tailTrace_3015000
  have hstable : (prefixWord ++ tailWord_3015000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015000).length < 2 ^ (prefixWord ++ tailWord_3015000).sum := by decide
  have hdescent : baseEnd_3015000 < baseStart_3015000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015007 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3015007 : Nat := 118140960795 + 3015007 * 2 ^ 59
def prefixEnd_3015007 : Nat := 4983230072969 + 3 ^ 40 * 3015007 * 2
def baseEnd_3015007 : Nat := 1548147767670390504946741

theorem tailTrace_3015007 : CollatzResearch.WordTrace tailWord_3015007 prefixEnd_3015007 1548147767670390504946741 := by
  unfold tailWord_3015007
  simp only [CollatzResearch.WordTrace]
  refine ⟨109966339388152036045659275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73310892925434690697106183 109966339388152036045659275)
  ·
    refine ⟨164949509082228054068488913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109966339388152036045659275 164949509082228054068488913)
    ·
      refine ⟨123712131811671040551366685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164949509082228054068488913 123712131811671040551366685)
      ·
        refine ⟨46392049429376640206762507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123712131811671040551366685 46392049429376640206762507)
        ·
          refine ⟨69588074144064960310143761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46392049429376640206762507 69588074144064960310143761)
          ·
            refine ⟨52191055608048720232607821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69588074144064960310143761 52191055608048720232607821)
            ·
              refine ⟨19571645853018270087227933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52191055608048720232607821 19571645853018270087227933)
              ·
                refine ⟨7339367194881851282710475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19571645853018270087227933 7339367194881851282710475)
                ·
                  refine ⟨11009050792322776924065713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7339367194881851282710475 11009050792322776924065713)
                  ·
                    refine ⟨8256788094242082693049285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11009050792322776924065713 8256788094242082693049285)
                    ·
                      refine ⟨1548147767670390504946741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8256788094242082693049285 1548147767670390504946741)
                      ·
                        rfl

theorem cell23_3015007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3015007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015007 prefixEnd_3015007 := by exact prefixLift 3015007
  have htrace : WordTrace (prefixWord ++ tailWord_3015007) baseStart_3015007 baseEnd_3015007 := by
    simpa [prefixWord, tailWord_3015007, baseEnd_3015007] using wordTrace_append hprefix tailTrace_3015007
  have hstable : (prefixWord ++ tailWord_3015007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015007).length < 2 ^ (prefixWord ++ tailWord_3015007).sum := by decide
  have hdescent : baseEnd_3015007 < baseStart_3015007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015011 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 3, 2, 2]
def baseStart_3015011 : Nat := 118140960795 + 3015011 * 2 ^ 59
def prefixEnd_3015011 : Nat := 4983230072969 + 3 ^ 40 * 3015011 * 2
def baseEnd_3015011 : Nat := 1548149821593008489296723

theorem tailTrace_3015011 : CollatzResearch.WordTrace tailWord_3015011 prefixEnd_3015011 1548149821593008489296723 := by
  unfold tailWord_3015011
  simp only [CollatzResearch.WordTrace]
  refine ⟨109966485280137544728804887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73310990186758363152536591 109966485280137544728804887)
  ·
    refine ⟨164949727920206317093207331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109966485280137544728804887 164949727920206317093207331)
    ·
      refine ⟨247424591880309475639810997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164949727920206317093207331 247424591880309475639810997)
      ·
        refine ⟨23196055488779013341232281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247424591880309475639810997 23196055488779013341232281)
        ·
          refine ⟨17397041616584260005924211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23196055488779013341232281 17397041616584260005924211)
          ·
            refine ⟨26095562424876390008886317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17397041616584260005924211 26095562424876390008886317)
            ·
              refine ⟨9785835909328646253332369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26095562424876390008886317 9785835909328646253332369)
              ·
                refine ⟨7339376931996484689999277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9785835909328646253332369 7339376931996484689999277)
                ·
                  refine ⟨2752266349498681758749729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7339376931996484689999277 2752266349498681758749729)
                  ·
                    refine ⟨2064199762124011319062297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2752266349498681758749729 2064199762124011319062297)
                    ·
                      refine ⟨1548149821593008489296723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064199762124011319062297 1548149821593008489296723)
                      ·
                        rfl

theorem cell23_3015011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_3015011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015011 prefixEnd_3015011 := by exact prefixLift 3015011
  have htrace : WordTrace (prefixWord ++ tailWord_3015011) baseStart_3015011 baseEnd_3015011 := by
    simpa [prefixWord, tailWord_3015011, baseEnd_3015011] using wordTrace_append hprefix tailTrace_3015011
  have hstable : (prefixWord ++ tailWord_3015011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015011).length < 2 ^ (prefixWord ++ tailWord_3015011).sum := by decide
  have hdescent : baseEnd_3015011 < baseStart_3015011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015017 : List Nat := [1, 2, 1, 1, 1, 3, 7, 7]
def baseStart_3015017 : Nat := 118140960795 + 3015017 * 2 ^ 59
def prefixEnd_3015017 : Nat := 4983230072969 + 3 ^ 40 * 3015017 * 2
def baseEnd_3015017 : Nat := 57338996388034646882285

theorem tailTrace_3015017 : CollatzResearch.WordTrace tailWord_3015017 prefixEnd_3015017 57338996388034646882285 := by
  unfold tailWord_3015017
  simp only [CollatzResearch.WordTrace]
  refine ⟨109966704118115807753523305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73311136078743871835682203 109966704118115807753523305)
  ·
    refine ⟨82475028088586855815142479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109966704118115807753523305 82475028088586855815142479)
    ·
      refine ⟨123712542132880283722713719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82475028088586855815142479 123712542132880283722713719)
      ·
        refine ⟨185568813199320425584070579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123712542132880283722713719 185568813199320425584070579)
        ·
          refine ⟨278353219798980638376105869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185568813199320425584070579 278353219798980638376105869)
          ·
            refine ⟨104382457424617739391039701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278353219798980638376105869 104382457424617739391039701)
            ·
              refine ⟨2446463845889478266977493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 104382457424617739391039701 2446463845889478266977493)
              ·
                refine ⟨57338996388034646882285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2446463845889478266977493 57338996388034646882285)
                ·
                  rfl

theorem cell23_3015017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 7].length) (baseStart_3015017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015017 prefixEnd_3015017 := by exact prefixLift 3015017
  have htrace : WordTrace (prefixWord ++ tailWord_3015017) baseStart_3015017 baseEnd_3015017 := by
    simpa [prefixWord, tailWord_3015017, baseEnd_3015017] using wordTrace_append hprefix tailTrace_3015017
  have hstable : (prefixWord ++ tailWord_3015017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015017).length < 2 ^ (prefixWord ++ tailWord_3015017).sum := by decide
  have hdescent : baseEnd_3015017 < baseStart_3015017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015062 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3015062 : Nat := 118140960795 + 3015062 * 2 ^ 59
def prefixEnd_3015062 : Nat := 4983230072969 + 3 ^ 40 * 3015062 * 2
def baseEnd_3015062 : Nat := 1548176009106387789758989

theorem tailTrace_3015062 : CollatzResearch.WordTrace tailWord_3015062 prefixEnd_3015062 1548176009106387789758989 := by
  unfold tailWord_3015062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6873021587684548777431965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73312230268635186959274293 6873021587684548777431965)
  ·
    refine ⟨2577383095381705791536987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6873021587684548777431965 2577383095381705791536987)
    ·
      refine ⟨3866074643072558687305481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577383095381705791536987 3866074643072558687305481)
      ·
        refine ⟨2899555982304419015479111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3866074643072558687305481 2899555982304419015479111)
        ·
          refine ⟨4349333973456628523218667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899555982304419015479111 4349333973456628523218667)
          ·
            refine ⟨6524000960184942784828001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349333973456628523218667 6524000960184942784828001)
            ·
              refine ⟨4893000720138707088621001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6524000960184942784828001 4893000720138707088621001)
              ·
                refine ⟨3669750540104030316465751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4893000720138707088621001 3669750540104030316465751)
                ·
                  refine ⟨5504625810156045474698627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669750540104030316465751 5504625810156045474698627)
                  ·
                    refine ⟨8256938715234068212047941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504625810156045474698627 8256938715234068212047941)
                    ·
                      refine ⟨1548176009106387789758989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8256938715234068212047941 1548176009106387789758989)
                      ·
                        rfl

theorem cell23_3015062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3015062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015062 prefixEnd_3015062 := by exact prefixLift 3015062
  have htrace : WordTrace (prefixWord ++ tailWord_3015062) baseStart_3015062 baseEnd_3015062 := by
    simpa [prefixWord, tailWord_3015062, baseEnd_3015062] using wordTrace_append hprefix tailTrace_3015062
  have hstable : (prefixWord ++ tailWord_3015062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015062).length < 2 ^ (prefixWord ++ tailWord_3015062).sum := by decide
  have hdescent : baseEnd_3015062 < baseStart_3015062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015084 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 3, 4, 2]
def baseStart_3015084 : Nat := 118140960795 + 3015084 * 2 ^ 59
def prefixEnd_3015084 : Nat := 4983230072969 + 3 ^ 40 * 3015084 * 2
def baseEnd_3015084 : Nat := 1548187305680786703683887

theorem tailTrace_3015084 : CollatzResearch.WordTrace tailWord_3015084 prefixEnd_3015084 1548187305680786703683887 := by
  unfold tailWord_3015084
  simp only [CollatzResearch.WordTrace]
  refine ⟨54984573904436539098106153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73312765205915385464141537 54984573904436539098106153)
  ·
    refine ⟨41238430428327404323579615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54984573904436539098106153 41238430428327404323579615)
    ·
      refine ⟨61857645642491106485369423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41238430428327404323579615 61857645642491106485369423)
      ·
        refine ⟨92786468463736659728054135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61857645642491106485369423 92786468463736659728054135)
        ·
          refine ⟨139179702695604989592081203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92786468463736659728054135 139179702695604989592081203)
          ·
            refine ⟨208769554043407484388121805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139179702695604989592081203 208769554043407484388121805)
            ·
              refine ⟨78288582766277806645545677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208769554043407484388121805 78288582766277806645545677)
              ·
                refine ⟨29358218537354177492079629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78288582766277806645545677 29358218537354177492079629)
                ·
                  refine ⟨11009331951507816559529861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29358218537354177492079629 11009331951507816559529861)
                  ·
                    refine ⟨2064249740907715604911849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11009331951507816559529861 2064249740907715604911849)
                    ·
                      refine ⟨1548187305680786703683887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064249740907715604911849 1548187305680786703683887)
                      ·
                        rfl

theorem cell23_3015084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_3015084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015084 prefixEnd_3015084 := by exact prefixLift 3015084
  have htrace : WordTrace (prefixWord ++ tailWord_3015084) baseStart_3015084 baseEnd_3015084 := by
    simpa [prefixWord, tailWord_3015084, baseEnd_3015084] using wordTrace_append hprefix tailTrace_3015084
  have hstable : (prefixWord ++ tailWord_3015084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015084).length < 2 ^ (prefixWord ++ tailWord_3015084).sum := by decide
  have hdescent : baseEnd_3015084 < baseStart_3015084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015087 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_3015087 : Nat := 118140960795 + 3015087 * 2 ^ 59
def prefixEnd_3015087 : Nat := 4983230072969 + 3 ^ 40 * 3015087 * 2
def baseEnd_3015087 : Nat := 1548188846122750191946373

theorem tailTrace_3015087 : CollatzResearch.WordTrace tailWord_3015087 prefixEnd_3015087 1548188846122750191946373 := by
  unfold tailWord_3015087
  simp only [CollatzResearch.WordTrace]
  refine ⟨109969257227862209708571515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73312838151908139805714343 109969257227862209708571515)
  ·
    refine ⟨164953885841793314562857273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109969257227862209708571515 164953885841793314562857273)
    ·
      refine ⟨123715414381344985922142955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164953885841793314562857273 123715414381344985922142955)
      ·
        refine ⟨185573121572017478883214433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123715414381344985922142955 185573121572017478883214433)
        ·
          refine ⟨139179841179013109162410825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185573121572017478883214433 139179841179013109162410825)
          ·
            refine ⟨104384880884259831871808119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139179841179013109162410825 104384880884259831871808119)
            ·
              refine ⟨156577321326389747807712179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104384880884259831871808119 156577321326389747807712179)
              ·
                refine ⟨234865981989584621711568269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156577321326389747807712179 234865981989584621711568269)
                ·
                  refine ⟨88074743246094233141838101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234865981989584621711568269 88074743246094233141838101)
                  ·
                    refine ⟨4128503589660667178523661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88074743246094233141838101 4128503589660667178523661)
                    ·
                      refine ⟨1548188846122750191946373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4128503589660667178523661 1548188846122750191946373)
                      ·
                        rfl

theorem cell23_3015087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_3015087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015087 prefixEnd_3015087 := by exact prefixLift 3015087
  have htrace : WordTrace (prefixWord ++ tailWord_3015087) baseStart_3015087 baseEnd_3015087 := by
    simpa [prefixWord, tailWord_3015087, baseEnd_3015087] using wordTrace_append hprefix tailTrace_3015087
  have hstable : (prefixWord ++ tailWord_3015087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015087).length < 2 ^ (prefixWord ++ tailWord_3015087).sum := by decide
  have hdescent : baseEnd_3015087 < baseStart_3015087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015122 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3015122 : Nat := 118140960795 + 3015122 * 2 ^ 59
def prefixEnd_3015122 : Nat := 4983230072969 + 3 ^ 40 * 3015122 * 2
def baseEnd_3015122 : Nat := 1548206817945657555008713

theorem tailTrace_3015122 : CollatzResearch.WordTrace tailWord_3015122 prefixEnd_3015122 1548206817945657555008713 := by
  unfold tailWord_3015122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27492633445683852671523905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73313689188490273790730413 27492633445683852671523905)
  ·
    refine ⟨20619475084262889503642929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27492633445683852671523905 20619475084262889503642929)
    ·
      refine ⟨15464606313197167127732197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20619475084262889503642929 15464606313197167127732197)
      ·
        refine ⟨2899613683724468836449787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15464606313197167127732197 2899613683724468836449787)
        ·
          refine ⟨4349420525586703254674681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899613683724468836449787 4349420525586703254674681)
          ·
            refine ⟨3262065394190027441006011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4349420525586703254674681 3262065394190027441006011)
            ·
              refine ⟨4893098091285041161509017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262065394190027441006011 4893098091285041161509017)
              ·
                refine ⟨3669823568463780871131763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4893098091285041161509017 3669823568463780871131763)
                ·
                  refine ⟨5504735352695671306697645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669823568463780871131763 5504735352695671306697645)
                  ·
                    refine ⟨2064275757260876740011617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5504735352695671306697645 2064275757260876740011617)
                    ·
                      refine ⟨1548206817945657555008713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064275757260876740011617 1548206817945657555008713)
                      ·
                        rfl

theorem cell23_3015122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3015122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015122 prefixEnd_3015122 := by exact prefixLift 3015122
  have htrace : WordTrace (prefixWord ++ tailWord_3015122) baseStart_3015122 baseEnd_3015122 := by
    simpa [prefixWord, tailWord_3015122, baseEnd_3015122] using wordTrace_append hprefix tailTrace_3015122
  have hstable : (prefixWord ++ tailWord_3015122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015122).length < 2 ^ (prefixWord ++ tailWord_3015122).sum := by decide
  have hdescent : baseEnd_3015122 < baseStart_3015122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015147 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_3015147 : Nat := 118140960795 + 3015147 * 2 ^ 59
def prefixEnd_3015147 : Nat := 4983230072969 + 3 ^ 40 * 3015147 * 2
def baseEnd_3015147 : Nat := 1548219654962019957196097

theorem tailTrace_3015147 : CollatzResearch.WordTrace tailWord_3015147 prefixEnd_3015147 1548219654962019957196097 := by
  unfold tailWord_3015147
  simp only [CollatzResearch.WordTrace]
  refine ⟨109971445607644839955755695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73314297071763226637170463 109971445607644839955755695)
  ·
    refine ⟨164957168411467259933633543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109971445607644839955755695 164957168411467259933633543)
    ·
      refine ⟨247435752617200889900450315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164957168411467259933633543 247435752617200889900450315)
      ·
        refine ⟨371153628925801334850675473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247435752617200889900450315 371153628925801334850675473)
        ·
          refine ⟨278365221694351001138006605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371153628925801334850675473 278365221694351001138006605)
          ·
            refine ⟨104386958135381625426752477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278365221694351001138006605 104386958135381625426752477)
            ·
              refine ⟨39145109300768109535032179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104386958135381625426752477 39145109300768109535032179)
              ·
                refine ⟨58717663951152164302548269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39145109300768109535032179 58717663951152164302548269)
                ·
                  refine ⟨22019123981682061613455601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58717663951152164302548269 22019123981682061613455601)
                  ·
                    refine ⟨16514342986261546210091701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22019123981682061613455601 16514342986261546210091701)
                    ·
                      refine ⟨1548219654962019957196097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16514342986261546210091701 1548219654962019957196097)
                      ·
                        rfl

theorem cell23_3015147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_3015147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015147 prefixEnd_3015147 := by exact prefixLift 3015147
  have htrace : WordTrace (prefixWord ++ tailWord_3015147) baseStart_3015147 baseEnd_3015147 := by
    simpa [prefixWord, tailWord_3015147, baseEnd_3015147] using wordTrace_append hprefix tailTrace_3015147
  have hstable : (prefixWord ++ tailWord_3015147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015147).length < 2 ^ (prefixWord ++ tailWord_3015147).sum := by decide
  have hdescent : baseEnd_3015147 < baseStart_3015147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015188 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3015188 : Nat := 118140960795 + 3015188 * 2 ^ 59
def prefixEnd_3015188 : Nat := 4983230072969 + 3 ^ 40 * 3015188 * 2
def baseEnd_3015188 : Nat := 516080235889618098927803

theorem tailTrace_3015188 : CollatzResearch.WordTrace tailWord_3015188 prefixEnd_3015188 516080235889618098927803 := by
  unfold tailWord_3015188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54986470500248151978999109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73315294000330869305332145 54986470500248151978999109)
  ·
    refine ⟨10309963218796528496062333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54986470500248151978999109 10309963218796528496062333)
    ·
      refine ⟨3866236207048698186023375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10309963218796528496062333 3866236207048698186023375)
      ·
        refine ⟨5799354310573047279035063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866236207048698186023375 5799354310573047279035063)
        ·
          refine ⟨8699031465859570918552595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799354310573047279035063 8699031465859570918552595)
          ·
            refine ⟨13048547198789356377828893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699031465859570918552595 13048547198789356377828893)
            ·
              refine ⟨4893205199546008641685835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13048547198789356377828893 4893205199546008641685835)
              ·
                refine ⟨7339807799319012962528753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893205199546008641685835 7339807799319012962528753)
                ·
                  refine ⟨5504855849489259721896565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339807799319012962528753 5504855849489259721896565)
                  ·
                    refine ⟨516080235889618098927803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5504855849489259721896565 516080235889618098927803)
                    ·
                      rfl

theorem cell23_3015188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3015188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015188 prefixEnd_3015188 := by exact prefixLift 3015188
  have htrace : WordTrace (prefixWord ++ tailWord_3015188) baseStart_3015188 baseEnd_3015188 := by
    simpa [prefixWord, tailWord_3015188, baseEnd_3015188] using wordTrace_append hprefix tailTrace_3015188
  have hstable : (prefixWord ++ tailWord_3015188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015188).length < 2 ^ (prefixWord ++ tailWord_3015188).sum := by decide
  have hdescent : baseEnd_3015188 < baseStart_3015188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015208 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3015208 : Nat := 118140960795 + 3015208 * 2 ^ 59
def prefixEnd_3015208 : Nat := 4983230072969 + 3 ^ 40 * 3015208 * 2
def baseEnd_3015208 : Nat := 1548250977281944218533317

theorem tailTrace_3015208 : CollatzResearch.WordTrace tailWord_3015208 prefixEnd_3015208 1548250977281944218533317 := by
  unfold tailWord_3015208
  simp only [CollatzResearch.WordTrace]
  refine ⟨54986835230211923686863139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73315780306949231582484185 54986835230211923686863139)
  ·
    refine ⟨82480252845317885530294709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54986835230211923686863139 82480252845317885530294709)
    ·
      refine ⟨7732523704248551768465129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82480252845317885530294709 7732523704248551768465129)
      ·
        refine ⟨5799392778186413826348847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7732523704248551768465129 5799392778186413826348847)
        ·
          refine ⟨8699089167279620739523271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799392778186413826348847 8699089167279620739523271)
          ·
            refine ⟨13048633750919431109284907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699089167279620739523271 13048633750919431109284907)
            ·
              refine ⟨19572950626379146663927361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13048633750919431109284907 19572950626379146663927361)
              ·
                refine ⟨14679712969784359997945521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19572950626379146663927361 14679712969784359997945521)
                ·
                  refine ⟨11009784727338269998459141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14679712969784359997945521 11009784727338269998459141)
                  ·
                    refine ⟨2064334636375925624711089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11009784727338269998459141 2064334636375925624711089)
                    ·
                      refine ⟨1548250977281944218533317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064334636375925624711089 1548250977281944218533317)
                      ·
                        rfl

theorem cell23_3015208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3015208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015208 prefixEnd_3015208 := by exact prefixLift 3015208
  have htrace : WordTrace (prefixWord ++ tailWord_3015208) baseStart_3015208 baseEnd_3015208 := by
    simpa [prefixWord, tailWord_3015208, baseEnd_3015208] using wordTrace_append hprefix tailTrace_3015208
  have hstable : (prefixWord ++ tailWord_3015208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015208).length < 2 ^ (prefixWord ++ tailWord_3015208).sum := by decide
  have hdescent : baseEnd_3015208 < baseStart_3015208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015218 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_3015218 : Nat := 118140960795 + 3015218 * 2 ^ 59
def prefixEnd_3015218 : Nat := 4983230072969 + 3 ^ 40 * 3015218 * 2
def baseEnd_3015218 : Nat := 516085370696163059802757

theorem tailTrace_3015218 : CollatzResearch.WordTrace tailWord_3015218 prefixEnd_3015218 516085370696163059802757 := by
  unfold tailWord_3015218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27493508797596904770397577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73316023460258412721060205 27493508797596904770397577)
  ·
    refine ⟨20620131598197678577798183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27493508797596904770397577 20620131598197678577798183)
    ·
      refine ⟨30930197397296517866697275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20620131598197678577798183 30930197397296517866697275)
      ·
        refine ⟨46395296095944776800045913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30930197397296517866697275 46395296095944776800045913)
        ·
          refine ⟨34796472071958582600034435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46395296095944776800045913 34796472071958582600034435)
          ·
            refine ⟨52194708107937873900051653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34796472071958582600034435 52194708107937873900051653)
            ·
              refine ⟨9786507770238351356259685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52194708107937873900051653 9786507770238351356259685)
              ·
                refine ⟨1834970206919690879298691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9786507770238351356259685 1834970206919690879298691)
                ·
                  refine ⟨2752455310379536318948037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834970206919690879298691 2752455310379536318948037)
                  ·
                    refine ⟨516085370696163059802757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2752455310379536318948037 516085370696163059802757)
                    ·
                      rfl

theorem cell23_3015218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_3015218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015218 prefixEnd_3015218 := by exact prefixLift 3015218
  have htrace : WordTrace (prefixWord ++ tailWord_3015218) baseStart_3015218 baseEnd_3015218 := by
    simpa [prefixWord, tailWord_3015218, baseEnd_3015218] using wordTrace_append hprefix tailTrace_3015218
  have hstable : (prefixWord ++ tailWord_3015218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015218).length < 2 ^ (prefixWord ++ tailWord_3015218).sum := by decide
  have hdescent : baseEnd_3015218 < baseStart_3015218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015231 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 6]
def baseStart_3015231 : Nat := 118140960795 + 3015231 * 2 ^ 59
def prefixEnd_3015231 : Nat := 4983230072969 + 3 ^ 40 * 3015231 * 2
def baseEnd_3015231 : Nat := 172029198592999736505079

theorem tailTrace_3015231 : CollatzResearch.WordTrace tailWord_3015231 prefixEnd_3015231 172029198592999736505079 := by
  unfold tailWord_3015231
  simp only [CollatzResearch.WordTrace]
  refine ⟨109974509339340522301813547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73316339559560348201209031 109974509339340522301813547)
  ·
    refine ⟨164961764009010783452720321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109974509339340522301813547 164961764009010783452720321)
    ·
      refine ⟨123721323006758087589540241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164961764009010783452720321 123721323006758087589540241)
      ·
        refine ⟨92790992255068565692155181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123721323006758087589540241 92790992255068565692155181)
        ·
          refine ⟨34796622095650712134558193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92790992255068565692155181 34796622095650712134558193)
          ·
            refine ⟨26097466571738034100918645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34796622095650712134558193 26097466571738034100918645)
            ·
              refine ⟨2446637491100440696961123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26097466571738034100918645 2446637491100440696961123)
              ·
                refine ⟨3669956236650661045441685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446637491100440696961123 3669956236650661045441685)
                ·
                  refine ⟨172029198592999736505079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3669956236650661045441685 172029198592999736505079)
                  ·
                    rfl

theorem cell23_3015231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 6].length) (baseStart_3015231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015231 prefixEnd_3015231 := by exact prefixLift 3015231
  have htrace : WordTrace (prefixWord ++ tailWord_3015231) baseStart_3015231 baseEnd_3015231 := by
    simpa [prefixWord, tailWord_3015231, baseEnd_3015231] using wordTrace_append hprefix tailTrace_3015231
  have hstable : (prefixWord ++ tailWord_3015231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015231).length < 2 ^ (prefixWord ++ tailWord_3015231).sum := by decide
  have hdescent : baseEnd_3015231 < baseStart_3015231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015268 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_3015268 : Nat := 118140960795 + 3015268 * 2 ^ 59
def prefixEnd_3015268 : Nat := 4983230072969 + 3 ^ 40 * 3015268 * 2
def baseEnd_3015268 : Nat := 1548281786121213983783041

theorem tailTrace_3015268 : CollatzResearch.WordTrace tailWord_3015268 prefixEnd_3015268 1548281786121213983783041 := by
  unfold tailWord_3015268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54987929420103238810455229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73317239226804318413940305 54987929420103238810455229)
  ·
    refine ⟨20620473532538714553920711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54987929420103238810455229 20620473532538714553920711)
    ·
      refine ⟨30930710298808071830881067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20620473532538714553920711 30930710298808071830881067)
      ·
        refine ⟨46396065448212107746321601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30930710298808071830881067 46396065448212107746321601)
        ·
          refine ⟨34797049086159080809741201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46396065448212107746321601 34797049086159080809741201)
          ·
            refine ⟨26097786814619310607305901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34797049086159080809741201 26097786814619310607305901)
            ·
              refine ⟨9786670055482241477739713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26097786814619310607305901 9786670055482241477739713)
              ·
                refine ⟨7340002541611681108304785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9786670055482241477739713 7340002541611681108304785)
                ·
                  refine ⟨5505001906208760831228589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7340002541611681108304785 5505001906208760831228589)
                  ·
                    refine ⟨2064375714828285311710721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5505001906208760831228589 2064375714828285311710721)
                    ·
                      refine ⟨1548281786121213983783041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064375714828285311710721 1548281786121213983783041)
                      ·
                        rfl

theorem cell23_3015268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_3015268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015268 prefixEnd_3015268 := by exact prefixLift 3015268
  have htrace : WordTrace (prefixWord ++ tailWord_3015268) baseStart_3015268 baseEnd_3015268 := by
    simpa [prefixWord, tailWord_3015268, baseEnd_3015268] using wordTrace_append hprefix tailTrace_3015268
  have hstable : (prefixWord ++ tailWord_3015268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015268).length < 2 ^ (prefixWord ++ tailWord_3015268).sum := by decide
  have hdescent : baseEnd_3015268 < baseStart_3015268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015332 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_3015332 : Nat := 118140960795 + 3015332 * 2 ^ 59
def prefixEnd_3015332 : Nat := 4983230072969 + 3 ^ 40 * 3015332 * 2
def baseEnd_3015332 : Nat := 1548314648883101733382747

theorem tailTrace_3015332 : CollatzResearch.WordTrace tailWord_3015332 prefixEnd_3015332 1548314648883101733382747 := by
  unfold tailWord_3015332
  simp only [CollatzResearch.WordTrace]
  refine ⟨54989096555987308275620125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73318795407983077700826833 54989096555987308275620125)
  ·
    refine ⟨20620911208495240603357547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54989096555987308275620125 20620911208495240603357547)
    ·
      refine ⟨30931366812742860905036321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20620911208495240603357547 30931366812742860905036321)
      ·
        refine ⟨23198525109557145678777241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30931366812742860905036321 23198525109557145678777241)
        ·
          refine ⟨17398893832167859259082931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23198525109557145678777241 17398893832167859259082931)
          ·
            refine ⟨26098340748251788888624397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17398893832167859259082931 26098340748251788888624397)
            ·
              refine ⟨9786877780594420833234149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26098340748251788888624397 9786877780594420833234149)
              ·
                refine ⟨1835039583861453906231403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9786877780594420833234149 1835039583861453906231403)
                ·
                  refine ⟨2752559375792180859347105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835039583861453906231403 2752559375792180859347105)
                  ·
                    refine ⟨2064419531844135644510329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2752559375792180859347105 2064419531844135644510329)
                    ·
                      refine ⟨1548314648883101733382747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064419531844135644510329 1548314648883101733382747)
                      ·
                        rfl

theorem cell23_3015332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_3015332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015332 prefixEnd_3015332 := by exact prefixLift 3015332
  have htrace : WordTrace (prefixWord ++ tailWord_3015332) baseStart_3015332 baseEnd_3015332 := by
    simpa [prefixWord, tailWord_3015332, baseEnd_3015332] using wordTrace_append hprefix tailTrace_3015332
  have hstable : (prefixWord ++ tailWord_3015332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015332).length < 2 ^ (prefixWord ++ tailWord_3015332).sum := by decide
  have hdescent : baseEnd_3015332 < baseStart_3015332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015344 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_3015344 : Nat := 118140960795 + 3015344 * 2 ^ 59
def prefixEnd_3015344 : Nat := 4983230072969 + 3 ^ 40 * 3015344 * 2
def baseEnd_3015344 : Nat := 1548320810650955686432691

theorem tailTrace_3015344 : CollatzResearch.WordTrace tailWord_3015344 prefixEnd_3015344 1548320810650955686432691 := by
  unfold tailWord_3015344
  simp only [CollatzResearch.WordTrace]
  refine ⟨54989315393965571300338543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73319087191954095067118057 54989315393965571300338543)
  ·
    refine ⟨82483973090948356950507815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54989315393965571300338543 82483973090948356950507815)
    ·
      refine ⟨123725959636422535425761723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82483973090948356950507815 123725959636422535425761723)
      ·
        refine ⟨185588939454633803138642585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123725959636422535425761723 185588939454633803138642585)
        ·
          refine ⟨139191704590975352353981939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185588939454633803138642585 139191704590975352353981939)
          ·
            refine ⟨208787556886463028530972909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139191704590975352353981939 208787556886463028530972909)
            ·
              refine ⟨78295333832423635699114841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208787556886463028530972909 78295333832423635699114841)
              ·
                refine ⟨58721500374317726774336131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78295333832423635699114841 58721500374317726774336131)
                ·
                  refine ⟨88082250561476590161504197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58721500374317726774336131 88082250561476590161504197)
                  ·
                    refine ⟨16515421980276860655282037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88082250561476590161504197 16515421980276860655282037)
                    ·
                      refine ⟨1548320810650955686432691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16515421980276860655282037 1548320810650955686432691)
                      ·
                        rfl

theorem cell23_3015344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_3015344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015344 prefixEnd_3015344 := by exact prefixLift 3015344
  have htrace : WordTrace (prefixWord ++ tailWord_3015344) baseStart_3015344 baseEnd_3015344 := by
    simpa [prefixWord, tailWord_3015344, baseEnd_3015344] using wordTrace_append hprefix tailTrace_3015344
  have hstable : (prefixWord ++ tailWord_3015344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015344).length < 2 ^ (prefixWord ++ tailWord_3015344).sum := by decide
  have hdescent : baseEnd_3015344 < baseStart_3015344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015345 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3015345 : Nat := 118140960795 + 3015345 * 2 ^ 59
def prefixEnd_3015345 : Nat := 4983230072969 + 3 ^ 40 * 3015345 * 2
def baseEnd_3015345 : Nat := 1548321324131610182520187

theorem tailTrace_3015345 : CollatzResearch.WordTrace tailWord_3015345 prefixEnd_3015345 1548321324131610182520187 := by
  unfold tailWord_3015345
  simp only [CollatzResearch.WordTrace]
  refine ⟨109978667260927519771463489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73319111507285013180975659 109978667260927519771463489)
  ·
    refine ⟨82484000445695639828597617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109978667260927519771463489 82484000445695639828597617)
    ·
      refine ⟨61863000334271729871448213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82484000445695639828597617 61863000334271729871448213)
      ·
        refine ⟨2899828140668987337724135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61863000334271729871448213 2899828140668987337724135)
        ·
          refine ⟨4349742211003481006586203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899828140668987337724135 4349742211003481006586203)
          ·
            refine ⟨6524613316505221509879305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349742211003481006586203 6524613316505221509879305)
            ·
              refine ⟨4893459987378916132409479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6524613316505221509879305 4893459987378916132409479)
              ·
                refine ⟨7340189981068374198614219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893459987378916132409479 7340189981068374198614219)
                ·
                  refine ⟨11010284971602561297921329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340189981068374198614219 11010284971602561297921329)
                  ·
                    refine ⟨8257713728701920973440997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11010284971602561297921329 8257713728701920973440997)
                    ·
                      refine ⟨1548321324131610182520187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8257713728701920973440997 1548321324131610182520187)
                      ·
                        rfl

theorem cell23_3015345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3015345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015345 prefixEnd_3015345 := by exact prefixLift 3015345
  have htrace : WordTrace (prefixWord ++ tailWord_3015345) baseStart_3015345 baseEnd_3015345 := by
    simpa [prefixWord, tailWord_3015345, baseEnd_3015345] using wordTrace_append hprefix tailTrace_3015345
  have hstable : (prefixWord ++ tailWord_3015345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015345).length < 2 ^ (prefixWord ++ tailWord_3015345).sum := by decide
  have hdescent : baseEnd_3015345 < baseStart_3015345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015366 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3015366 : Nat := 118140960795 + 3015366 * 2 ^ 59
def prefixEnd_3015366 : Nat := 4983230072969 + 3 ^ 40 * 3015366 * 2
def baseEnd_3015366 : Nat := 1548332107225354600357591

theorem tailTrace_3015366 : CollatzResearch.WordTrace tailWord_3015366 prefixEnd_3015366 1548332107225354600357591 := by
  unfold tailWord_3015366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436857287307857511186811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73319622129234293571985301 3436857287307857511186811)
  ·
    refine ⟨5155285930961786266780217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3436857287307857511186811 5155285930961786266780217)
    ·
      refine ⟨3866464448221339700085163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5155285930961786266780217 3866464448221339700085163)
      ·
        refine ⟨5799696672332009550127745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866464448221339700085163 5799696672332009550127745)
        ·
          refine ⟨4349772504249007162595809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5799696672332009550127745 4349772504249007162595809)
          ·
            refine ⟨3262329378186755371946857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4349772504249007162595809 3262329378186755371946857)
            ·
              refine ⟨2446747033640066528960143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262329378186755371946857 2446747033640066528960143)
              ·
                refine ⟨3670120550460099793440215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446747033640066528960143 3670120550460099793440215)
                ·
                  refine ⟨5505180825690149690160323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670120550460099793440215 5505180825690149690160323)
                  ·
                    refine ⟨8257771238535224535240485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5505180825690149690160323 8257771238535224535240485)
                    ·
                      refine ⟨1548332107225354600357591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8257771238535224535240485 1548332107225354600357591)
                      ·
                        rfl

theorem cell23_3015366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3015366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015366 prefixEnd_3015366 := by exact prefixLift 3015366
  have htrace : WordTrace (prefixWord ++ tailWord_3015366) baseStart_3015366 baseEnd_3015366 := by
    simpa [prefixWord, tailWord_3015366, baseEnd_3015366] using wordTrace_append hprefix tailTrace_3015366
  have hstable : (prefixWord ++ tailWord_3015366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015366).length < 2 ^ (prefixWord ++ tailWord_3015366).sum := by decide
  have hdescent : baseEnd_3015366 < baseStart_3015366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015401 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_3015401 : Nat := 118140960795 + 3015401 * 2 ^ 59
def prefixEnd_3015401 : Nat := 4983230072969 + 3 ^ 40 * 3015401 * 2
def baseEnd_3015401 : Nat := 1548350079048261963419929

theorem tailTrace_3015401 : CollatzResearch.WordTrace tailWord_3015401 prefixEnd_3015401 1548350079048261963419929 := by
  unfold tailWord_3015401
  simp only [CollatzResearch.WordTrace]
  refine ⟨109980709748724641335502057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73320473165816427557001371 109980709748724641335502057)
  ·
    refine ⟨82485532311543481001626543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109980709748724641335502057 82485532311543481001626543)
    ·
      refine ⟨123728298467315221502439815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82485532311543481001626543 123728298467315221502439815)
      ·
        refine ⟨185592447700972832253659723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123728298467315221502439815 185592447700972832253659723)
        ·
          refine ⟨278388671551459248380489585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185592447700972832253659723 278388671551459248380489585)
          ·
            refine ⟨208791503663594436285367189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278388671551459248380489585 208791503663594436285367189)
            ·
              refine ⟨9787101734230989200876587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208791503663594436285367189 9787101734230989200876587)
              ·
                refine ⟨14680652601346483801314881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9787101734230989200876587 14680652601346483801314881)
                ·
                  refine ⟨11010489451009862850986161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14680652601346483801314881 11010489451009862850986161)
                  ·
                    refine ⟨8257867088257397138239621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11010489451009862850986161 8257867088257397138239621)
                    ·
                      refine ⟨1548350079048261963419929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8257867088257397138239621 1548350079048261963419929)
                      ·
                        rfl

theorem cell23_3015401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_3015401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015401 prefixEnd_3015401 := by exact prefixLift 3015401
  have htrace : WordTrace (prefixWord ++ tailWord_3015401) baseStart_3015401 baseEnd_3015401 := by
    simpa [prefixWord, tailWord_3015401, baseEnd_3015401] using wordTrace_append hprefix tailTrace_3015401
  have hstable : (prefixWord ++ tailWord_3015401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015401).length < 2 ^ (prefixWord ++ tailWord_3015401).sum := by decide
  have hdescent : baseEnd_3015401 < baseStart_3015401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015422 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_3015422 : Nat := 118140960795 + 3015422 * 2 ^ 59
def prefixEnd_3015422 : Nat := 4983230072969 + 3 ^ 40 * 3015422 * 2
def baseEnd_3015422 : Nat := 1548360862142006381257333

theorem tailTrace_3015422 : CollatzResearch.WordTrace tailWord_3015422 prefixEnd_3015422 1548360862142006381257333 := by
  unfold tailWord_3015422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13747684460206070240252065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73320983787765707948011013 13747684460206070240252065)
  ·
    refine ⟨10310763345154552680189049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13747684460206070240252065 10310763345154552680189049)
    ·
      refine ⟨7733072508865914510141787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10310763345154552680189049 7733072508865914510141787)
      ·
        refine ⟨11599608763298871765212681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7733072508865914510141787 11599608763298871765212681)
        ·
          refine ⟨8699706572474153823909511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11599608763298871765212681 8699706572474153823909511)
          ·
            refine ⟨13049559858711230735864267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699706572474153823909511 13049559858711230735864267)
            ·
              refine ⟨19574339788066846103796401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13049559858711230735864267 19574339788066846103796401)
              ·
                refine ⟨14680754841050134577847301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19574339788066846103796401 14680754841050134577847301)
                ·
                  refine ⟨2752641532696900233346369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14680754841050134577847301 2752641532696900233346369)
                  ·
                    refine ⟨2064481149522675175009777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2752641532696900233346369 2064481149522675175009777)
                    ·
                      refine ⟨1548360862142006381257333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064481149522675175009777 1548360862142006381257333)
                      ·
                        rfl

theorem cell23_3015422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_3015422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015422 prefixEnd_3015422 := by exact prefixLift 3015422
  have htrace : WordTrace (prefixWord ++ tailWord_3015422) baseStart_3015422 baseEnd_3015422 := by
    simpa [prefixWord, tailWord_3015422, baseEnd_3015422] using wordTrace_append hprefix tailTrace_3015422
  have hstable : (prefixWord ++ tailWord_3015422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015422).length < 2 ^ (prefixWord ++ tailWord_3015422).sum := by decide
  have hdescent : baseEnd_3015422 < baseStart_3015422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015441 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_3015441 : Nat := 118140960795 + 3015441 * 2 ^ 59
def prefixEnd_3015441 : Nat := 4983230072969 + 3 ^ 40 * 3015441 * 2
def baseEnd_3015441 : Nat := 516123539424813935639915

theorem tailTrace_3015441 : CollatzResearch.WordTrace tailWord_3015441 prefixEnd_3015441 516123539424813935639915 := by
  unfold tailWord_3015441
  simp only [CollatzResearch.WordTrace]
  refine ⟨109982168668579728166958177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73321445779053152111305451 109982168668579728166958177)
  ·
    refine ⟨82486626501434796125218633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109982168668579728166958177 82486626501434796125218633)
    ·
      refine ⟨61864969876076097093913975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82486626501434796125218633 61864969876076097093913975)
      ·
        refine ⟨92797454814114145640870963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61864969876076097093913975 92797454814114145640870963)
        ·
          refine ⟨139196182221171218461306445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92797454814114145640870963 139196182221171218461306445)
          ·
            refine ⟨52198568332939206922989917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139196182221171218461306445 52198568332939206922989917)
            ·
              refine ⟨19574463124852202596121219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52198568332939206922989917 19574463124852202596121219)
              ·
                refine ⟨29361694687278303894181829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19574463124852202596121219 29361694687278303894181829)
                ·
                  refine ⟨5505317753864681980159093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29361694687278303894181829 5505317753864681980159093)
                  ·
                    refine ⟨516123539424813935639915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5505317753864681980159093 516123539424813935639915)
                    ·
                      rfl

theorem cell23_3015441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_3015441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015441 prefixEnd_3015441 := by exact prefixLift 3015441
  have htrace : WordTrace (prefixWord ++ tailWord_3015441) baseStart_3015441 baseEnd_3015441 := by
    simpa [prefixWord, tailWord_3015441, baseEnd_3015441] using wordTrace_append hprefix tailTrace_3015441
  have hstable : (prefixWord ++ tailWord_3015441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015441).length < 2 ^ (prefixWord ++ tailWord_3015441).sum := by decide
  have hdescent : baseEnd_3015441 < baseStart_3015441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015445 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 5]
def baseStart_3015445 : Nat := 118140960795 + 3015445 * 2 ^ 59
def prefixEnd_3015445 : Nat := 4983230072969 + 3 ^ 40 * 3015445 * 2
def baseEnd_3015445 : Nat := 172041408021895532363303

theorem tailTrace_3015445 : CollatzResearch.WordTrace tailWord_3015445 prefixEnd_3015445 172041408021895532363303 := by
  unfold tailWord_3015445
  simp only [CollatzResearch.WordTrace]
  refine ⟨109982314560565236850103789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73321543040376824566735859 109982314560565236850103789)
  ·
    refine ⟨41243367960211963818788921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109982314560565236850103789 41243367960211963818788921)
    ·
      refine ⟨30932525970158972864091691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41243367960211963818788921 30932525970158972864091691)
      ·
        refine ⟨46398788955238459296137537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30932525970158972864091691 46398788955238459296137537)
        ·
          refine ⟨34799091716428844472103153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46398788955238459296137537 34799091716428844472103153)
          ·
            refine ⟨26099318787321633354077365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34799091716428844472103153 26099318787321633354077365)
            ·
              refine ⟨2446811136311403126944753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26099318787321633354077365 2446811136311403126944753)
              ·
                refine ⟨1835108352233552345208565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446811136311403126944753 1835108352233552345208565)
                ·
                  refine ⟨172041408021895532363303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1835108352233552345208565 172041408021895532363303)
                  ·
                    rfl

theorem cell23_3015445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_3015445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015445 prefixEnd_3015445 := by exact prefixLift 3015445
  have htrace : WordTrace (prefixWord ++ tailWord_3015445) baseStart_3015445 baseEnd_3015445 := by
    simpa [prefixWord, tailWord_3015445, baseEnd_3015445] using wordTrace_append hprefix tailTrace_3015445
  have hstable : (prefixWord ++ tailWord_3015445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015445).length < 2 ^ (prefixWord ++ tailWord_3015445).sum := by decide
  have hdescent : baseEnd_3015445 < baseStart_3015445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015448 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3015448 : Nat := 118140960795 + 3015448 * 2 ^ 59
def prefixEnd_3015448 : Nat := 4983230072969 + 3 ^ 40 * 3015448 * 2
def baseEnd_3015448 : Nat := 1548374212639023279532213

theorem tailTrace_3015448 : CollatzResearch.WordTrace tailWord_3015448 prefixEnd_3015448 1548374212639023279532213 := by
  unfold tailWord_3015448
  simp only [CollatzResearch.WordTrace]
  refine ⟨54991211989777184181231499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73321615986369578908308665 54991211989777184181231499)
  ·
    refine ⟨82486817984665776271847249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54991211989777184181231499 82486817984665776271847249)
    ·
      refine ⟨61865113488499332203885437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82486817984665776271847249 61865113488499332203885437)
      ·
        refine ⟨23199417558187249576457039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61865113488499332203885437 23199417558187249576457039)
        ·
          refine ⟨34799126337280874364685559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23199417558187249576457039 34799126337280874364685559)
          ·
            refine ⟨52198689505921311547028339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34799126337280874364685559 52198689505921311547028339)
            ·
              refine ⟨78298034258881967320542509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52198689505921311547028339 78298034258881967320542509)
              ·
                refine ⟨29361762847080737745203441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78298034258881967320542509 29361762847080737745203441)
                ·
                  refine ⟨22021322135310553308902581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29361762847080737745203441 22021322135310553308902581)
                  ·
                    refine ⟨2064498950185364372709617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22021322135310553308902581 2064498950185364372709617)
                    ·
                      refine ⟨1548374212639023279532213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064498950185364372709617 1548374212639023279532213)
                      ·
                        rfl

theorem cell23_3015448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3015448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015448 prefixEnd_3015448 := by exact prefixLift 3015448
  have htrace : WordTrace (prefixWord ++ tailWord_3015448) baseStart_3015448 baseEnd_3015448 := by
    simpa [prefixWord, tailWord_3015448, baseEnd_3015448] using wordTrace_append hprefix tailTrace_3015448
  have hstable : (prefixWord ++ tailWord_3015448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015448).length < 2 ^ (prefixWord ++ tailWord_3015448).sum := by decide
  have hdescent : baseEnd_3015448 < baseStart_3015448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015491 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_3015491 : Nat := 118140960795 + 3015491 * 2 ^ 59
def prefixEnd_3015491 : Nat := 4983230072969 + 3 ^ 40 * 3015491 * 2
def baseEnd_3015491 : Nat := 1548396292307166611294515

theorem tailTrace_3015491 : CollatzResearch.WordTrace tailWord_3015491 prefixEnd_3015491 1548396292307166611294515 := by
  unfold tailWord_3015491
  simp only [CollatzResearch.WordTrace]
  refine ⟨109983992318398586706278327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73322661545599057804185551 109983992318398586706278327)
  ·
    refine ⟨164975988477597880059417491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109983992318398586706278327 164975988477597880059417491)
    ·
      refine ⟨247463982716396820089126237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164975988477597880059417491 247463982716396820089126237)
      ·
        refine ⟨92798993518648807533422339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247463982716396820089126237 92798993518648807533422339)
        ·
          refine ⟨139198490277973211300133509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92798993518648807533422339 139198490277973211300133509)
          ·
            refine ⟨26099716927119977118775033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139198490277973211300133509 26099716927119977118775033)
            ·
              refine ⟨19574787695339982839081275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26099716927119977118775033 19574787695339982839081275)
              ·
                refine ⟨29362181543009974258621913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19574787695339982839081275 29362181543009974258621913)
                ·
                  refine ⟨22021636157257480693966435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29362181543009974258621913 22021636157257480693966435)
                  ·
                    refine ⟨33032454235886221040949653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22021636157257480693966435 33032454235886221040949653)
                    ·
                      refine ⟨1548396292307166611294515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33032454235886221040949653 1548396292307166611294515)
                      ·
                        rfl

theorem cell23_3015491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_3015491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015491 prefixEnd_3015491 := by exact prefixLift 3015491
  have htrace : WordTrace (prefixWord ++ tailWord_3015491) baseStart_3015491 baseEnd_3015491 := by
    simpa [prefixWord, tailWord_3015491, baseEnd_3015491] using wordTrace_append hprefix tailTrace_3015491
  have hstable : (prefixWord ++ tailWord_3015491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015491).length < 2 ^ (prefixWord ++ tailWord_3015491).sum := by decide
  have hdescent : baseEnd_3015491 < baseStart_3015491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015498 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_3015498 : Nat := 118140960795 + 3015498 * 2 ^ 59
def prefixEnd_3015498 : Nat := 4983230072969 + 3 ^ 40 * 3015498 * 2
def baseEnd_3015498 : Nat := 1548399886671748083906983

theorem tailTrace_3015498 : CollatzResearch.WordTrace tailWord_3015498 prefixEnd_3015498 1548399886671748083906983 := by
  unfold tailWord_3015498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496061907343306725445787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73322831752915484601188765 27496061907343306725445787)
  ·
    refine ⟨41244092861014960088168681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27496061907343306725445787 41244092861014960088168681)
    ·
      refine ⟨30933069645761220066126511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41244092861014960088168681 30933069645761220066126511)
      ·
        refine ⟨46399604468641830099189767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30933069645761220066126511 46399604468641830099189767)
        ·
          refine ⟨69599406702962745148784651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46399604468641830099189767 69599406702962745148784651)
          ·
            refine ⟨104399110054444117723176977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69599406702962745148784651 104399110054444117723176977)
            ·
              refine ⟨78299332540833088292382733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104399110054444117723176977 78299332540833088292382733)
              ·
                refine ⟨29362249702812408109643525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78299332540833088292382733 29362249702812408109643525)
                ·
                  refine ⟨5505421819277326520558161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29362249702812408109643525 5505421819277326520558161)
                  ·
                    refine ⟨4129066364457994890418621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5505421819277326520558161 4129066364457994890418621)
                    ·
                      refine ⟨1548399886671748083906983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4129066364457994890418621 1548399886671748083906983)
                      ·
                        rfl

theorem cell23_3015498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_3015498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015498 prefixEnd_3015498 := by exact prefixLift 3015498
  have htrace : WordTrace (prefixWord ++ tailWord_3015498) baseStart_3015498 baseEnd_3015498 := by
    simpa [prefixWord, tailWord_3015498, baseEnd_3015498] using wordTrace_append hprefix tailTrace_3015498
  have hstable : (prefixWord ++ tailWord_3015498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015498).length < 2 ^ (prefixWord ++ tailWord_3015498).sum := by decide
  have hdescent : baseEnd_3015498 < baseStart_3015498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015521 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3015521 : Nat := 118140960795 + 3015521 * 2 ^ 59
def prefixEnd_3015521 : Nat := 4983230072969 + 3 ^ 40 * 3015521 * 2
def baseEnd_3015521 : Nat := 1548411696726801493919377

theorem tailTrace_3015521 : CollatzResearch.WordTrace tailWord_3015521 prefixEnd_3015521 1548411696726801493919377 := by
  unfold tailWord_3015521
  simp only [CollatzResearch.WordTrace]
  refine ⟨109985086508289901829870417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73323391005526601219913611 109985086508289901829870417)
  ·
    refine ⟨82488814881217426372402813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109985086508289901829870417 82488814881217426372402813)
    ·
      refine ⟨30933305580456534889651055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82488814881217426372402813 30933305580456534889651055)
      ·
        refine ⟨46399958370684802334476583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30933305580456534889651055 46399958370684802334476583)
        ·
          refine ⟨69599937556027203501714875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46399958370684802334476583 69599937556027203501714875)
          ·
            refine ⟨104399906334040805252572313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69599937556027203501714875 104399906334040805252572313)
            ·
              refine ⟨78299929750530603939429235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104399906334040805252572313 78299929750530603939429235)
              ·
                refine ⟨117449894625795905909143853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78299929750530603939429235 117449894625795905909143853)
                ·
                  refine ⟨44043710484673464715928945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117449894625795905909143853 44043710484673464715928945)
                  ·
                    refine ⟨33032782863505098536946709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44043710484673464715928945 33032782863505098536946709)
                    ·
                      refine ⟨1548411696726801493919377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33032782863505098536946709 1548411696726801493919377)
                      ·
                        rfl

theorem cell23_3015521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3015521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015521 prefixEnd_3015521 := by exact prefixLift 3015521
  have htrace : WordTrace (prefixWord ++ tailWord_3015521) baseStart_3015521 baseEnd_3015521 := by
    simpa [prefixWord, tailWord_3015521, baseEnd_3015521] using wordTrace_append hprefix tailTrace_3015521
  have hstable : (prefixWord ++ tailWord_3015521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015521).length < 2 ^ (prefixWord ++ tailWord_3015521).sum := by decide
  have hdescent : baseEnd_3015521 < baseStart_3015521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015522 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3015522 : Nat := 118140960795 + 3015522 * 2 ^ 59
def prefixEnd_3015522 : Nat := 4983230072969 + 3 ^ 40 * 3015522 * 2
def baseEnd_3015522 : Nat := 516137403402485330002291

theorem tailTrace_3015522 : CollatzResearch.WordTrace tailWord_3015522 prefixEnd_3015522 516137403402485330002291 := by
  unfold tailWord_3015522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496280745321569750164205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73323415320857519333771213 27496280745321569750164205)
  ·
    refine ⟨10311105279495588656311577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27496280745321569750164205 10311105279495588656311577)
    ·
      refine ⟨7733328959621691492233683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10311105279495588656311577 7733328959621691492233683)
      ·
        refine ⟨11599993439432537238350525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7733328959621691492233683 11599993439432537238350525)
        ·
          refine ⟨4349997539787201464381447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11599993439432537238350525 4349997539787201464381447)
          ·
            refine ⟨6524996309680802196572171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349997539787201464381447 6524996309680802196572171)
            ·
              refine ⟨9787494464521203294858257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524996309680802196572171 9787494464521203294858257)
              ·
                refine ⟨7340620848390902471143693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9787494464521203294858257 7340620848390902471143693)
                ·
                  refine ⟨2752732818146588426678885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7340620848390902471143693 2752732818146588426678885)
                  ·
                    refine ⟨516137403402485330002291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2752732818146588426678885 516137403402485330002291)
                    ·
                      rfl

theorem cell23_3015522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3015522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015522 prefixEnd_3015522 := by exact prefixLift 3015522
  have htrace : WordTrace (prefixWord ++ tailWord_3015522) baseStart_3015522 baseEnd_3015522 := by
    simpa [prefixWord, tailWord_3015522, baseEnd_3015522] using wordTrace_append hprefix tailTrace_3015522
  have hstable : (prefixWord ++ tailWord_3015522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015522).length < 2 ^ (prefixWord ++ tailWord_3015522).sum := by decide
  have hdescent : baseEnd_3015522 < baseStart_3015522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015555 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 4, 3, 2]
def baseStart_3015555 : Nat := 118140960795 + 3015555 * 2 ^ 59
def prefixEnd_3015555 : Nat := 4983230072969 + 3 ^ 40 * 3015555 * 2
def baseEnd_3015555 : Nat := 1548429155069054360894221

theorem tailTrace_3015555 : CollatzResearch.WordTrace tailWord_3015555 prefixEnd_3015555 1548429155069054360894221 := by
  unfold tailWord_3015555
  simp only [CollatzResearch.WordTrace]
  refine ⟨109986326590166725636608119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73324217726777817091072079 109986326590166725636608119)
  ·
    refine ⟨164979489885250088454912179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109986326590166725636608119 164979489885250088454912179)
    ·
      refine ⟨247469234827875132682368269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164979489885250088454912179 247469234827875132682368269)
      ·
        refine ⟨92800963060453174755888101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247469234827875132682368269 92800963060453174755888101)
        ·
          refine ⟨17400180573834970266729019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92800963060453174755888101 17400180573834970266729019)
          ·
            refine ⟨26100270860752455400093529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17400180573834970266729019 26100270860752455400093529)
            ·
              refine ⟨19575203145564341550070147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26100270860752455400093529 19575203145564341550070147)
              ·
                refine ⟨29362804718346512325105221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19575203145564341550070147 29362804718346512325105221)
                ·
                  refine ⟨5505525884689971060957229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29362804718346512325105221 5505525884689971060957229)
                  ·
                    refine ⟨2064572206758739147858961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5505525884689971060957229 2064572206758739147858961)
                    ·
                      refine ⟨1548429155069054360894221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064572206758739147858961 1548429155069054360894221)
                      ·
                        rfl

theorem cell23_3015555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_3015555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015555 prefixEnd_3015555 := by exact prefixLift 3015555
  have htrace : WordTrace (prefixWord ++ tailWord_3015555) baseStart_3015555 baseEnd_3015555 := by
    simpa [prefixWord, tailWord_3015555, baseEnd_3015555] using wordTrace_append hprefix tailTrace_3015555
  have hstable : (prefixWord ++ tailWord_3015555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015555).length < 2 ^ (prefixWord ++ tailWord_3015555).sum := by decide
  have hdescent : baseEnd_3015555 < baseStart_3015555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015562 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3015562 : Nat := 118140960795 + 3015562 * 2 ^ 59
def prefixEnd_3015562 : Nat := 4983230072969 + 3 ^ 40 * 3015562 * 2
def baseEnd_3015562 : Nat := 1548432749433635833506689

theorem tailTrace_3015562 : CollatzResearch.WordTrace tailWord_3015562 prefixEnd_3015562 1548432749433635833506689 := by
  unfold tailWord_3015562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496645475285341458028235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73324387934094243888075293 27496645475285341458028235)
  ·
    refine ⟨41244968212928012187042353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27496645475285341458028235 41244968212928012187042353)
    ·
      refine ⟨30933726159696009140281765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41244968212928012187042353 30933726159696009140281765)
      ·
        refine ⟨5800073654943001713802831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30933726159696009140281765 5800073654943001713802831)
        ·
          refine ⟨8700110482414502570704247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800073654943001713802831 8700110482414502570704247)
          ·
            refine ⟨13050165723621753856056371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700110482414502570704247 13050165723621753856056371)
            ·
              refine ⟨19575248585432630784084557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13050165723621753856056371 19575248585432630784084557)
              ·
                refine ⟨7340718219537236544031709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19575248585432630784084557 7340718219537236544031709)
                ·
                  refine ⟨2752769332326463704011891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7340718219537236544031709 2752769332326463704011891)
                  ·
                    refine ⟨4129153998489695556017837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2752769332326463704011891 4129153998489695556017837)
                    ·
                      refine ⟨1548432749433635833506689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4129153998489695556017837 1548432749433635833506689)
                      ·
                        rfl

theorem cell23_3015562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3015562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015562 prefixEnd_3015562 := by exact prefixLift 3015562
  have htrace : WordTrace (prefixWord ++ tailWord_3015562) baseStart_3015562 baseEnd_3015562 := by
    simpa [prefixWord, tailWord_3015562, baseEnd_3015562] using wordTrace_append hprefix tailTrace_3015562
  have hstable : (prefixWord ++ tailWord_3015562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015562).length < 2 ^ (prefixWord ++ tailWord_3015562).sum := by decide
  have hdescent : baseEnd_3015562 < baseStart_3015562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015588 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3015588 : Nat := 118140960795 + 3015588 * 2 ^ 59
def prefixEnd_3015588 : Nat := 4983230072969 + 3 ^ 40 * 3015588 * 2
def baseEnd_3015588 : Nat := 1548446099930652731781569

theorem tailTrace_3015588 : CollatzResearch.WordTrace tailWord_3015588 prefixEnd_3015588 1548446099930652731781569 := by
  unfold tailWord_3015588
  simp only [CollatzResearch.WordTrace]
  refine ⟨54993765099523586136279709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73325020132698114848372945 54993765099523586136279709)
  ·
    refine ⟨20622661912321344801104891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54993765099523586136279709 20622661912321344801104891)
    ·
      refine ⟨30933992868482017201657337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20622661912321344801104891 30933992868482017201657337)
      ·
        refine ⟨23200494651361512901243003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30933992868482017201657337 23200494651361512901243003)
        ·
          refine ⟨34800741977042269351864505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23200494651361512901243003 34800741977042269351864505)
          ·
            refine ⟨26100556482781702013898379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34800741977042269351864505 26100556482781702013898379)
            ·
              refine ⟨39150834724172553020847569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26100556482781702013898379 39150834724172553020847569)
              ·
                refine ⟨29363126043129414765635677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39150834724172553020847569 29363126043129414765635677)
                ·
                  refine ⟨11011172266173530537113379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29363126043129414765635677 11011172266173530537113379)
                  ·
                    refine ⟨16516758399260295805670069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11011172266173530537113379 16516758399260295805670069)
                    ·
                      refine ⟨1548446099930652731781569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16516758399260295805670069 1548446099930652731781569)
                      ·
                        rfl

theorem cell23_3015588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3015588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015588 prefixEnd_3015588 := by exact prefixLift 3015588
  have htrace : WordTrace (prefixWord ++ tailWord_3015588) baseStart_3015588 baseEnd_3015588 := by
    simpa [prefixWord, tailWord_3015588, baseEnd_3015588] using wordTrace_append hprefix tailTrace_3015588
  have hstable : (prefixWord ++ tailWord_3015588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015588).length < 2 ^ (prefixWord ++ tailWord_3015588).sum := by decide
  have hdescent : baseEnd_3015588 < baseStart_3015588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015605 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3015605 : Nat := 118140960795 + 3015605 * 2 ^ 59
def prefixEnd_3015605 : Nat := 4983230072969 + 3 ^ 40 * 3015605 * 2
def baseEnd_3015605 : Nat := 1548454829101779165268991

theorem tailTrace_3015605 : CollatzResearch.WordTrace tailWord_3015605 prefixEnd_3015605 1548454829101779165268991 := by
  unfold tailWord_3015605
  simp only [CollatzResearch.WordTrace]
  refine ⟨109988150239985584175928269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73325433493323722783952179 109988150239985584175928269)
  ·
    refine ⟨41245556339994594065973101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109988150239985584175928269 41245556339994594065973101)
    ·
      refine ⟨15467083627497972774739913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41245556339994594065973101 15467083627497972774739913)
      ·
        refine ⟨11600312720623479581054935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15467083627497972774739913 11600312720623479581054935)
        ·
          refine ⟨17400469080935219371582403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11600312720623479581054935 17400469080935219371582403)
          ·
            refine ⟨26100703621402829057373605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17400469080935219371582403 26100703621402829057373605)
            ·
              refine ⟨4893881929013030448257551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26100703621402829057373605 4893881929013030448257551)
              ·
                refine ⟨7340822893519545672386327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893881929013030448257551 7340822893519545672386327)
                ·
                  refine ⟨11011234340279318508579491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340822893519545672386327 11011234340279318508579491)
                  ·
                    refine ⟨16516851510418977762869237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11011234340279318508579491 16516851510418977762869237)
                    ·
                      refine ⟨1548454829101779165268991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16516851510418977762869237 1548454829101779165268991)
                      ·
                        rfl

theorem cell23_3015605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3015605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015605 prefixEnd_3015605 := by exact prefixLift 3015605
  have htrace : WordTrace (prefixWord ++ tailWord_3015605) baseStart_3015605 baseEnd_3015605 := by
    simpa [prefixWord, tailWord_3015605, baseEnd_3015605] using wordTrace_append hprefix tailTrace_3015605
  have hstable : (prefixWord ++ tailWord_3015605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015605).length < 2 ^ (prefixWord ++ tailWord_3015605).sum := by decide
  have hdescent : baseEnd_3015605 < baseStart_3015605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015608 : List Nat := [2, 1, 2, 1, 2, 6, 9]
def baseStart_3015608 : Nat := 118140960795 + 3015608 * 2 ^ 59
def prefixEnd_3015608 : Nat := 4983230072969 + 3 ^ 40 * 3015608 * 2
def baseEnd_3015608 : Nat := 19116745303009168562117

theorem tailTrace_3015608 : CollatzResearch.WordTrace tailWord_3015608 prefixEnd_3015608 19116745303009168562117 := by
  unfold tailWord_3015608
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994129829487357844143739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73325506439316477125524985 54994129829487357844143739)
  ·
    refine ⟨82491194744231036766215609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54994129829487357844143739 82491194744231036766215609)
    ·
      refine ⟨61868396058173277574661707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82491194744231036766215609 61868396058173277574661707)
      ·
        refine ⟨92802594087259916361992561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61868396058173277574661707 92802594087259916361992561)
        ·
          refine ⟨69601945565444937271494421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92802594087259916361992561 69601945565444937271494421)
          ·
            refine ⟨3262591198380231434601301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69601945565444937271494421 3262591198380231434601301)
            ·
              refine ⟨19116745303009168562117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3262591198380231434601301 19116745303009168562117)
              ·
                rfl

theorem cell23_3015608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 9].length) (baseStart_3015608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015608 prefixEnd_3015608 := by exact prefixLift 3015608
  have htrace : WordTrace (prefixWord ++ tailWord_3015608) baseStart_3015608 baseEnd_3015608 := by
    simpa [prefixWord, tailWord_3015608, baseEnd_3015608] using wordTrace_append hprefix tailTrace_3015608
  have hstable : (prefixWord ++ tailWord_3015608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015608).length < 2 ^ (prefixWord ++ tailWord_3015608).sum := by decide
  have hdescent : baseEnd_3015608 < baseStart_3015608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015628 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3015628 : Nat := 118140960795 + 3015628 * 2 ^ 59
def prefixEnd_3015628 : Nat := 4983230072969 + 3 ^ 40 * 3015628 * 2
def baseEnd_3015628 : Nat := 1548466639156832575281385

theorem tailTrace_3015628 : CollatzResearch.WordTrace tailWord_3015628 prefixEnd_3015628 1548466639156832575281385 := by
  unfold tailWord_3015628
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994494559451129552007769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73325992745934839402677025 54994494559451129552007769)
  ·
    refine ⟨41245870919588347164005827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54994494559451129552007769 41245870919588347164005827)
    ·
      refine ⟨61868806379382520746008741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41245870919588347164005827 61868806379382520746008741)
      ·
        refine ⟨11600401196134222639876639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61868806379382520746008741 11600401196134222639876639)
        ·
          refine ⟨17400601794201333959814959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11600401196134222639876639 17400601794201333959814959)
          ·
            refine ⟨26100902691302000939722439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17400601794201333959814959 26100902691302000939722439)
            ·
              refine ⟨39151354036953001409583659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26100902691302000939722439 39151354036953001409583659)
              ·
                refine ⟨58727031055429502114375489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39151354036953001409583659 58727031055429502114375489)
                ·
                  refine ⟨44045273291572126585781617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58727031055429502114375489 44045273291572126585781617)
                  ·
                    refine ⟨33033954968679094939336213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44045273291572126585781617 33033954968679094939336213)
                    ·
                      refine ⟨1548466639156832575281385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33033954968679094939336213 1548466639156832575281385)
                      ·
                        rfl

theorem cell23_3015628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3015628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015628 prefixEnd_3015628 := by exact prefixLift 3015628
  have htrace : WordTrace (prefixWord ++ tailWord_3015628) baseStart_3015628 baseEnd_3015628 := by
    simpa [prefixWord, tailWord_3015628, baseEnd_3015628] using wordTrace_append hprefix tailTrace_3015628
  have hstable : (prefixWord ++ tailWord_3015628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015628).length < 2 ^ (prefixWord ++ tailWord_3015628).sum := by decide
  have hdescent : baseEnd_3015628 < baseStart_3015628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015670 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_3015670 : Nat := 118140960795 + 3015670 * 2 ^ 59
def prefixEnd_3015670 : Nat := 4983230072969 + 3 ^ 40 * 3015670 * 2
def baseEnd_3015670 : Nat := 1548488205344321410956193

theorem tailTrace_3015670 : CollatzResearch.WordTrace tailWord_3015670 prefixEnd_3015670 1548488205344321410956193 := by
  unfold tailWord_3015670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6874407561546881267315279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73327013989833400184696309 6874407561546881267315279)
  ·
    refine ⟨10311611342320321900972919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6874407561546881267315279 10311611342320321900972919)
    ·
      refine ⟨15467417013480482851459379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10311611342320321900972919 15467417013480482851459379)
      ·
        refine ⟨23201125520220724277189069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15467417013480482851459379 23201125520220724277189069)
        ·
          refine ⟨8700422070082771603945901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23201125520220724277189069 8700422070082771603945901)
          ·
            refine ⟨3262658276281039351479713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8700422070082771603945901 3262658276281039351479713)
            ·
              refine ⟨2446993707210779513609785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262658276281039351479713 2446993707210779513609785)
              ·
                refine ⟨1835245280408084635207339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446993707210779513609785 1835245280408084635207339)
                ·
                  refine ⟨2752867920612126952811009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835245280408084635207339 2752867920612126952811009)
                  ·
                    refine ⟨2064650940459095214608257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2752867920612126952811009 2064650940459095214608257)
                    ·
                      refine ⟨1548488205344321410956193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064650940459095214608257 1548488205344321410956193)
                      ·
                        rfl

theorem cell23_3015670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_3015670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015670 prefixEnd_3015670 := by exact prefixLift 3015670
  have htrace : WordTrace (prefixWord ++ tailWord_3015670) baseStart_3015670 baseEnd_3015670 := by
    simpa [prefixWord, tailWord_3015670, baseEnd_3015670] using wordTrace_append hprefix tailTrace_3015670
  have hstable : (prefixWord ++ tailWord_3015670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015670).length < 2 ^ (prefixWord ++ tailWord_3015670).sum := by decide
  have hdescent : baseEnd_3015670 < baseStart_3015670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015675 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 5, 4, 2]
def baseStart_3015675 : Nat := 118140960795 + 3015675 * 2 ^ 59
def prefixEnd_3015675 : Nat := 4983230072969 + 3 ^ 40 * 3015675 * 2
def baseEnd_3015675 : Nat := 1548490772747593891393669

theorem tailTrace_3015675 : CollatzResearch.WordTrace tailWord_3015675 prefixEnd_3015675 1548490772747593891393669 := by
  unfold tailWord_3015675
  simp only [CollatzResearch.WordTrace]
  refine ⟨109990703349731986130976479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73327135566487990753984319 109990703349731986130976479)
  ·
    refine ⟨164986055024597979196464719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109990703349731986130976479 164986055024597979196464719)
    ·
      refine ⟨247479082536896968794697079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164986055024597979196464719 247479082536896968794697079)
      ·
        refine ⟨371218623805345453192045619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247479082536896968794697079 371218623805345453192045619)
        ·
          refine ⟨556827935708018179788068429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371218623805345453192045619 556827935708018179788068429)
          ·
            refine ⟨208810475890506817420525661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556827935708018179788068429 208810475890506817420525661)
            ·
              refine ⟨78303928458940056532697123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208810475890506817420525661 78303928458940056532697123)
              ·
                refine ⟨117455892688410084799045685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78303928458940056532697123 117455892688410084799045685)
                ·
                  refine ⟨11011489939538445449910533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117455892688410084799045685 11011489939538445449910533)
                  ·
                    refine ⟨2064654363663458521858225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11011489939538445449910533 2064654363663458521858225)
                    ·
                      refine ⟨1548490772747593891393669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064654363663458521858225 1548490772747593891393669)
                      ·
                        rfl

theorem cell23_3015675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4, 2].length) (baseStart_3015675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015675 prefixEnd_3015675 := by exact prefixLift 3015675
  have htrace : WordTrace (prefixWord ++ tailWord_3015675) baseStart_3015675 baseEnd_3015675 := by
    simpa [prefixWord, tailWord_3015675, baseEnd_3015675] using wordTrace_append hprefix tailTrace_3015675
  have hstable : (prefixWord ++ tailWord_3015675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015675).length < 2 ^ (prefixWord ++ tailWord_3015675).sum := by decide
  have hdescent : baseEnd_3015675 < baseStart_3015675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015692 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 1, 4, 2]
def baseStart_3015692 : Nat := 118140960795 + 3015692 * 2 ^ 59
def prefixEnd_3015692 : Nat := 4983230072969 + 3 ^ 40 * 3015692 * 2
def baseEnd_3015692 : Nat := 1548499501918720324881091

theorem tailTrace_3015692 : CollatzResearch.WordTrace tailWord_3015692 prefixEnd_3015692 1548499501918720324881091 := by
  unfold tailWord_3015692
  simp only [CollatzResearch.WordTrace]
  refine ⟨54995661695335199017172665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73327548927113598689563553 54995661695335199017172665)
  ·
    refine ⟨41246746271501399262879499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54995661695335199017172665 41246746271501399262879499)
    ·
      refine ⟨61870119407252098894319249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41246746271501399262879499 61870119407252098894319249)
      ·
        refine ⟨46402589555439074170739437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61870119407252098894319249 46402589555439074170739437)
        ·
          refine ⟨17400971083289652814027289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46402589555439074170739437 17400971083289652814027289)
          ·
            refine ⟨13050728312467239610520467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17400971083289652814027289 13050728312467239610520467)
            ·
              refine ⟨19576092468700859415780701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13050728312467239610520467 19576092468700859415780701)
              ·
                refine ⟨7341034675762822280917763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19576092468700859415780701 7341034675762822280917763)
                ·
                  refine ⟨11011552013644233421376645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341034675762822280917763 11011552013644233421376645)
                  ·
                    refine ⟨2064666002558293766508121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11011552013644233421376645 2064666002558293766508121)
                    ·
                      refine ⟨1548499501918720324881091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064666002558293766508121 1548499501918720324881091)
                      ·
                        rfl

theorem cell23_3015692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_3015692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015692 prefixEnd_3015692 := by exact prefixLift 3015692
  have htrace : WordTrace (prefixWord ++ tailWord_3015692) baseStart_3015692 baseEnd_3015692 := by
    simpa [prefixWord, tailWord_3015692, baseEnd_3015692] using wordTrace_append hprefix tailTrace_3015692
  have hstable : (prefixWord ++ tailWord_3015692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015692).length < 2 ^ (prefixWord ++ tailWord_3015692).sum := by decide
  have hdescent : baseEnd_3015692 < baseStart_3015692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015732 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3015732 : Nat := 118140960795 + 3015732 * 2 ^ 59
def prefixEnd_3015732 : Nat := 4983230072969 + 3 ^ 40 * 3015732 * 2
def baseEnd_3015732 : Nat := 172057782349433352042323

theorem tailTrace_3015732 : CollatzResearch.WordTrace tailWord_3015732 prefixEnd_3015732 172057782349433352042323 := by
  unfold tailWord_3015732
  simp only [CollatzResearch.WordTrace]
  refine ⟨54996391155262742432900725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73328521540350323243867633 54996391155262742432900725)
  ·
    refine ⟨5155911670805882103084443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54996391155262742432900725 5155911670805882103084443)
    ·
      refine ⟨7733867506208823154626665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155911670805882103084443 7733867506208823154626665)
      ·
        refine ⟨5800400629656617365969999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7733867506208823154626665 5800400629656617365969999)
        ·
          refine ⟨8700600944484926048954999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800400629656617365969999 8700600944484926048954999)
          ·
            refine ⟨13050901416727389073432499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700600944484926048954999 13050901416727389073432499)
            ·
              refine ⟨19576352125091083610148749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13050901416727389073432499 19576352125091083610148749)
              ·
                refine ⟨7341132046909156353805781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19576352125091083610148749 7341132046909156353805781)
                ·
                  refine ⟨172057782349433352042323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7341132046909156353805781 172057782349433352042323)
                  ·
                    rfl

theorem cell23_3015732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3015732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015732 prefixEnd_3015732 := by exact prefixLift 3015732
  have htrace : WordTrace (prefixWord ++ tailWord_3015732) baseStart_3015732 baseEnd_3015732 := by
    simpa [prefixWord, tailWord_3015732, baseEnd_3015732] using wordTrace_append hprefix tailTrace_3015732
  have hstable : (prefixWord ++ tailWord_3015732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015732).length < 2 ^ (prefixWord ++ tailWord_3015732).sum := by decide
  have hdescent : baseEnd_3015732 < baseStart_3015732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015765 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3015765 : Nat := 118140960795 + 3015765 * 2 ^ 59
def prefixEnd_3015765 : Nat := 4983230072969 + 3 ^ 40 * 3015765 * 2
def baseEnd_3015765 : Nat := 1548536986006498539268255

theorem tailTrace_3015765 : CollatzResearch.WordTrace tailWord_3015765 prefixEnd_3015765 1548536986006498539268255 := by
  unfold tailWord_3015765
  simp only [CollatzResearch.WordTrace]
  refine ⟨109993985919405931501752749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73329323946270621001168499 109993985919405931501752749)
  ·
    refine ⟨41247744719777224313157281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109993985919405931501752749 41247744719777224313157281)
    ·
      refine ⟨30935808539832918234867961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41247744719777224313157281 30935808539832918234867961)
      ·
        refine ⟨23201856404874688676150971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30935808539832918234867961 23201856404874688676150971)
        ·
          refine ⟨34802784607312033014226457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23201856404874688676150971 34802784607312033014226457)
          ·
            refine ⟨26102088455484024760669843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34802784607312033014226457 26102088455484024760669843)
            ·
              refine ⟨39153132683226037141004765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26102088455484024760669843 39153132683226037141004765)
              ·
                refine ⟨14682424756209763927876787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39153132683226037141004765 14682424756209763927876787)
                ·
                  refine ⟨22023637134314645891815181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14682424756209763927876787 22023637134314645891815181)
                  ·
                    refine ⟨8258863925367992209430693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22023637134314645891815181 8258863925367992209430693)
                    ·
                      refine ⟨1548536986006498539268255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8258863925367992209430693 1548536986006498539268255)
                      ·
                        rfl

theorem cell23_3015765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3015765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015765 prefixEnd_3015765 := by exact prefixLift 3015765
  have htrace : WordTrace (prefixWord ++ tailWord_3015765) baseStart_3015765 baseEnd_3015765 := by
    simpa [prefixWord, tailWord_3015765, baseEnd_3015765] using wordTrace_append hprefix tailTrace_3015765
  have hstable : (prefixWord ++ tailWord_3015765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015765).length < 2 ^ (prefixWord ++ tailWord_3015765).sum := by decide
  have hdescent : baseEnd_3015765 < baseStart_3015765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015839 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 6]
def baseStart_3015839 : Nat := 118140960795 + 3015839 * 2 ^ 59
def prefixEnd_3015839 : Nat := 4983230072969 + 3 ^ 40 * 3015839 * 2
def baseEnd_3015839 : Nat := 172063887063881249971435

theorem tailTrace_3015839 : CollatzResearch.WordTrace tailWord_3015839 prefixEnd_3015839 172063887063881249971435 := by
  unfold tailWord_3015839
  simp only [CollatzResearch.WordTrace]
  refine ⟨109996684921137842139946571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73331123280758561426631047 109996684921137842139946571)
  ·
    refine ⟨164995027381706763209919857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109996684921137842139946571 164995027381706763209919857)
    ·
      refine ⟨123746270536280072407439893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164995027381706763209919857 123746270536280072407439893)
      ·
        refine ⟨5800606431388128394098745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123746270536280072407439893 5800606431388128394098745)
        ·
          refine ⟨4350454823541096295574059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5800606431388128394098745 4350454823541096295574059)
          ·
            refine ⟨6525682235311644443361089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350454823541096295574059 6525682235311644443361089)
            ·
              refine ⟨4894261676483733332520817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6525682235311644443361089 4894261676483733332520817)
              ·
                refine ⟨3670696257362799999390613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4894261676483733332520817 3670696257362799999390613)
                ·
                  refine ⟨172063887063881249971435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3670696257362799999390613 172063887063881249971435)
                  ·
                    rfl

theorem cell23_3015839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 6].length) (baseStart_3015839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015839 prefixEnd_3015839 := by exact prefixLift 3015839
  have htrace : WordTrace (prefixWord ++ tailWord_3015839) baseStart_3015839 baseEnd_3015839 := by
    simpa [prefixWord, tailWord_3015839, baseEnd_3015839] using wordTrace_append hprefix tailTrace_3015839
  have hstable : (prefixWord ++ tailWord_3015839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015839).length < 2 ^ (prefixWord ++ tailWord_3015839).sum := by decide
  have hdescent : baseEnd_3015839 < baseStart_3015839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015875 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5]
def baseStart_3015875 : Nat := 118140960795 + 3015875 * 2 ^ 59
def prefixEnd_3015875 : Nat := 4983230072969 + 3 ^ 40 * 3015875 * 2
def baseEnd_3015875 : Nat := 1548593468878493108892749

theorem tailTrace_3015875 : CollatzResearch.WordTrace tailWord_3015875 prefixEnd_3015875 1548593468878493108892749 := by
  unfold tailWord_3015875
  simp only [CollatzResearch.WordTrace]
  refine ⟨109997997949007420288257079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73331998632671613525504719 109997997949007420288257079)
  ·
    refine ⟨164996996923511130432385619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109997997949007420288257079 164996996923511130432385619)
    ·
      refine ⟨247495495385266695648578429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164996996923511130432385619 247495495385266695648578429)
      ·
        refine ⟨92810810769475010868216911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247495495385266695648578429 92810810769475010868216911)
        ·
          refine ⟨139216216154212516302325367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92810810769475010868216911 139216216154212516302325367)
          ·
            refine ⟨208824324231318774453488051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139216216154212516302325367 208824324231318774453488051)
            ·
              refine ⟨313236486346978161680232077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208824324231318774453488051 313236486346978161680232077)
              ·
                refine ⟨117463682380116810630087029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313236486346978161680232077 117463682380116810630087029)
                ·
                  refine ⟨11012220223135950996570659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117463682380116810630087029 11012220223135950996570659)
                  ·
                    refine ⟨16518330334703926494855989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11012220223135950996570659 16518330334703926494855989)
                    ·
                      refine ⟨1548593468878493108892749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16518330334703926494855989 1548593468878493108892749)
                      ·
                        rfl

theorem cell23_3015875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_3015875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015875 prefixEnd_3015875 := by exact prefixLift 3015875
  have htrace : WordTrace (prefixWord ++ tailWord_3015875) baseStart_3015875 baseEnd_3015875 := by
    simpa [prefixWord, tailWord_3015875, baseEnd_3015875] using wordTrace_append hprefix tailTrace_3015875
  have hstable : (prefixWord ++ tailWord_3015875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015875).length < 2 ^ (prefixWord ++ tailWord_3015875).sum := by decide
  have hdescent : baseEnd_3015875 < baseStart_3015875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015876 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3015876 : Nat := 118140960795 + 3015876 * 2 ^ 59
def prefixEnd_3015876 : Nat := 4983230072969 + 3 ^ 40 * 3015876 * 2
def baseEnd_3015876 : Nat := 1548593982359147604980245

theorem tailTrace_3015876 : CollatzResearch.WordTrace tailWord_3015876 prefixEnd_3015876 1548593982359147604980245 := by
  unfold tailWord_3015876
  simp only [CollatzResearch.WordTrace]
  refine ⟨54999017211001898729521741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73332022948002531639362321 54999017211001898729521741)
  ·
    refine ⟨20624631454125712023570653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54999017211001898729521741 20624631454125712023570653)
    ·
      refine ⟨7734236795297142008838995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20624631454125712023570653 7734236795297142008838995)
      ·
        refine ⟨11601355192945713013258493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7734236795297142008838995 11601355192945713013258493)
        ·
          refine ⟨4350508197354642379971935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11601355192945713013258493 4350508197354642379971935)
          ·
            refine ⟨6525762296031963569957903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350508197354642379971935 6525762296031963569957903)
            ·
              refine ⟨9788643444047945354936855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6525762296031963569957903 9788643444047945354936855)
              ·
                refine ⟨14682965166071918032405283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788643444047945354936855 14682965166071918032405283)
                ·
                  refine ⟨22024447749107877048607925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14682965166071918032405283 22024447749107877048607925)
                  ·
                    refine ⟨2064791976478863473306993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22024447749107877048607925 2064791976478863473306993)
                    ·
                      refine ⟨1548593982359147604980245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064791976478863473306993 1548593982359147604980245)
                      ·
                        rfl

theorem cell23_3015876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3015876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015876 prefixEnd_3015876 := by exact prefixLift 3015876
  have htrace : WordTrace (prefixWord ++ tailWord_3015876) baseStart_3015876 baseEnd_3015876 := by
    simpa [prefixWord, tailWord_3015876, baseEnd_3015876] using wordTrace_append hprefix tailTrace_3015876
  have hstable : (prefixWord ++ tailWord_3015876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015876).length < 2 ^ (prefixWord ++ tailWord_3015876).sum := by decide
  have hdescent : baseEnd_3015876 < baseStart_3015876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015882 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_3015882 : Nat := 118140960795 + 3015882 * 2 ^ 59
def prefixEnd_3015882 : Nat := 4983230072969 + 3 ^ 40 * 3015882 * 2
def baseEnd_3015882 : Nat := 516199021081024860501739

theorem tailTrace_3015882 : CollatzResearch.WordTrace tailWord_3015882 prefixEnd_3015882 516199021081024860501739 := by
  unfold tailWord_3015882
  simp only [CollatzResearch.WordTrace]
  refine ⟨27499563314995515120940475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73332168839988040322507933 27499563314995515120940475)
  ·
    refine ⟨41249344972493272681410713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27499563314995515120940475 41249344972493272681410713)
    ·
      refine ⟨30937008729369954511058035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41249344972493272681410713 30937008729369954511058035)
      ·
        refine ⟨46405513094054931766587053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30937008729369954511058035 46405513094054931766587053)
        ·
          refine ⟨17402067410270599412470145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46405513094054931766587053 17402067410270599412470145)
          ·
            refine ⟨13051550557702949559352609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17402067410270599412470145 13051550557702949559352609)
            ·
              refine ⟨9788662918277212169514457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13051550557702949559352609 9788662918277212169514457)
              ·
                refine ⟨7341497188707909127135843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9788662918277212169514457 7341497188707909127135843)
                ·
                  refine ⟨11012245783061863690703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341497188707909127135843 11012245783061863690703765)
                  ·
                    refine ⟨516199021081024860501739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11012245783061863690703765 516199021081024860501739)
                    ·
                      rfl

theorem cell23_3015882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_3015882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015882 prefixEnd_3015882 := by exact prefixLift 3015882
  have htrace : WordTrace (prefixWord ++ tailWord_3015882) baseStart_3015882 baseEnd_3015882 := by
    simpa [prefixWord, tailWord_3015882, baseEnd_3015882] using wordTrace_append hprefix tailTrace_3015882
  have hstable : (prefixWord ++ tailWord_3015882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015882).length < 2 ^ (prefixWord ++ tailWord_3015882).sum := by decide
  have hdescent : baseEnd_3015882 < baseStart_3015882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015889 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 7, 2, 2]
def baseStart_3015889 : Nat := 118140960795 + 3015889 * 2 ^ 59
def prefixEnd_3015889 : Nat := 4983230072969 + 3 ^ 40 * 3015889 * 2
def baseEnd_3015889 : Nat := 1548600657607656054117685

theorem tailTrace_3015889 : CollatzResearch.WordTrace tailWord_3015889 prefixEnd_3015889 1548600657607656054117685 := by
  unfold tailWord_3015889
  simp only [CollatzResearch.WordTrace]
  refine ⟨109998508570956700679266721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73332339047304467119511147 109998508570956700679266721)
  ·
    refine ⟨82498881428217525509450041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109998508570956700679266721 82498881428217525509450041)
    ·
      refine ⟨61874161071163144132087531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82498881428217525509450041 61874161071163144132087531)
      ·
        refine ⟨92811241606744716198131297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61874161071163144132087531 92811241606744716198131297)
        ·
          refine ⟨69608431205058537148598473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92811241606744716198131297 69608431205058537148598473)
          ·
            refine ⟨52206323403793902861448855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69608431205058537148598473 52206323403793902861448855)
            ·
              refine ⟨78309485105690854292173283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52206323403793902861448855 78309485105690854292173283)
              ·
                refine ⟨117464227658536281438259925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78309485105690854292173283 117464227658536281438259925)
                ·
                  refine ⟨2753067835746944096209217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117464227658536281438259925 2753067835746944096209217)
                  ·
                    refine ⟨2064800876810208072156913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2753067835746944096209217 2064800876810208072156913)
                    ·
                      refine ⟨1548600657607656054117685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064800876810208072156913 1548600657607656054117685)
                      ·
                        rfl

theorem cell23_3015889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_3015889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015889 prefixEnd_3015889 := by exact prefixLift 3015889
  have htrace : WordTrace (prefixWord ++ tailWord_3015889) baseStart_3015889 baseEnd_3015889 := by
    simpa [prefixWord, tailWord_3015889, baseEnd_3015889] using wordTrace_append hprefix tailTrace_3015889
  have hstable : (prefixWord ++ tailWord_3015889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015889).length < 2 ^ (prefixWord ++ tailWord_3015889).sum := by decide
  have hdescent : baseEnd_3015889 < baseStart_3015889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015909 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3015909 : Nat := 118140960795 + 3015909 * 2 ^ 59
def prefixEnd_3015909 : Nat := 4983230072969 + 3 ^ 40 * 3015909 * 2
def baseEnd_3015909 : Nat := 1548610927220745975867593

theorem tailTrace_3015909 : CollatzResearch.WordTrace tailWord_3015909 prefixEnd_3015909 1548610927220745975867593 := by
  unfold tailWord_3015909
  simp only [CollatzResearch.WordTrace]
  refine ⟨109999238030884244094994781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73332825353922829396663187 109999238030884244094994781)
  ·
    refine ⟨41249714261581591535623043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109999238030884244094994781 41249714261581591535623043)
    ·
      refine ⟨61874571392372387303434565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41249714261581591535623043 61874571392372387303434565)
      ·
        refine ⟨11601482136069822619393981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61874571392372387303434565 11601482136069822619393981)
        ·
          refine ⟨4350555801026183482272743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11601482136069822619393981 4350555801026183482272743)
          ·
            refine ⟨6525833701539275223409115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350555801026183482272743 6525833701539275223409115)
            ·
              refine ⟨9788750552308912835113673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6525833701539275223409115 9788750552308912835113673)
              ·
                refine ⟨7341562914231684626335255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9788750552308912835113673 7341562914231684626335255)
                ·
                  refine ⟨11012344371347526939502883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341562914231684626335255 11012344371347526939502883)
                  ·
                    refine ⟨16518516557021290409254325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11012344371347526939502883 16518516557021290409254325)
                    ·
                      refine ⟨1548610927220745975867593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16518516557021290409254325 1548610927220745975867593)
                      ·
                        rfl

theorem cell23_3015909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3015909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015909 prefixEnd_3015909 := by exact prefixLift 3015909
  have htrace : WordTrace (prefixWord ++ tailWord_3015909) baseStart_3015909 baseEnd_3015909 := by
    simpa [prefixWord, tailWord_3015909, baseEnd_3015909] using wordTrace_append hprefix tailTrace_3015909
  have hstable : (prefixWord ++ tailWord_3015909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015909).length < 2 ^ (prefixWord ++ tailWord_3015909).sum := by decide
  have hdescent : baseEnd_3015909 < baseStart_3015909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015916 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_3015916 : Nat := 118140960795 + 3015916 * 2 ^ 59
def prefixEnd_3015916 : Nat := 4983230072969 + 3 ^ 40 * 3015916 * 2
def baseEnd_3015916 : Nat := 516204840528442482826687

theorem tailTrace_3015916 : CollatzResearch.WordTrace tailWord_3015916 prefixEnd_3015916 516204840528442482826687 := by
  unfold tailWord_3015916
  simp only [CollatzResearch.WordTrace]
  refine ⟨54999746670929442145249801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73332995561239256193666401 54999746670929442145249801)
  ·
    refine ⟨41249810003197081608937351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54999746670929442145249801 41249810003197081608937351)
    ·
      refine ⟨61874715004795622413406027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41249810003197081608937351 61874715004795622413406027)
      ·
        refine ⟨92812072507193433620109041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61874715004795622413406027 92812072507193433620109041)
        ·
          refine ⟨69609054380395075215081781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92812072507193433620109041 69609054380395075215081781)
          ·
            refine ⟨6525848848162038301413917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69609054380395075215081781 6525848848162038301413917)
            ·
              refine ⟨2447193318060764363030219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6525848848162038301413917 2447193318060764363030219)
              ·
                refine ⟨3670789977091146544545329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447193318060764363030219 3670789977091146544545329)
                ·
                  refine ⟨2753092482818359908408997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3670789977091146544545329 2753092482818359908408997)
                  ·
                    refine ⟨516204840528442482826687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2753092482818359908408997 516204840528442482826687)
                    ·
                      rfl

theorem cell23_3015916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_3015916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015916 prefixEnd_3015916 := by exact prefixLift 3015916
  have htrace : WordTrace (prefixWord ++ tailWord_3015916) baseStart_3015916 baseEnd_3015916 := by
    simpa [prefixWord, tailWord_3015916, baseEnd_3015916] using wordTrace_append hprefix tailTrace_3015916
  have hstable : (prefixWord ++ tailWord_3015916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015916).length < 2 ^ (prefixWord ++ tailWord_3015916).sum := by decide
  have hdescent : baseEnd_3015916 < baseStart_3015916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015939 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 3]
def baseStart_3015939 : Nat := 118140960795 + 3015939 * 2 ^ 59
def prefixEnd_3015939 : Nat := 4983230072969 + 3 ^ 40 * 3015939 * 2
def baseEnd_3015939 : Nat := 1548626331640380858492455

theorem tailTrace_3015939 : CollatzResearch.WordTrace tailWord_3015939 prefixEnd_3015939 1548626331640380858492455 := by
  unfold tailWord_3015939
  simp only [CollatzResearch.WordTrace]
  refine ⟨110000332220775559218586871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73333554813850372812391247 110000332220775559218586871)
  ·
    refine ⟨165000498331163338827880307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110000332220775559218586871 165000498331163338827880307)
    ·
      refine ⟨247500747496745008241820461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165000498331163338827880307 247500747496745008241820461)
      ·
        refine ⟨92812780311279378090682673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247500747496745008241820461 92812780311279378090682673)
        ·
          refine ⟨69609585233459533568012005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92812780311279378090682673 69609585233459533568012005)
          ·
            refine ⟨13051797231273662544002251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69609585233459533568012005 13051797231273662544002251)
            ·
              refine ⟨19577695846910493816003377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13051797231273662544002251 19577695846910493816003377)
              ·
                refine ⟨14683271885182870362002533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19577695846910493816003377 14683271885182870362002533)
                ·
                  refine ⟨2753113478471788192875475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14683271885182870362002533 2753113478471788192875475)
                  ·
                    refine ⟨4129670217707682289313213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753113478471788192875475 4129670217707682289313213)
                    ·
                      refine ⟨1548626331640380858492455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4129670217707682289313213 1548626331640380858492455)
                      ·
                        rfl

theorem cell23_3015939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_3015939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015939 prefixEnd_3015939 := by exact prefixLift 3015939
  have htrace : WordTrace (prefixWord ++ tailWord_3015939) baseStart_3015939 baseEnd_3015939 := by
    simpa [prefixWord, tailWord_3015939, baseEnd_3015939] using wordTrace_append hprefix tailTrace_3015939
  have hstable : (prefixWord ++ tailWord_3015939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015939).length < 2 ^ (prefixWord ++ tailWord_3015939).sum := by decide
  have hdescent : baseEnd_3015939 < baseStart_3015939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015940 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_3015940 : Nat := 118140960795 + 3015940 * 2 ^ 59
def prefixEnd_3015940 : Nat := 4983230072969 + 3 ^ 40 * 3015940 * 2
def baseEnd_3015940 : Nat := 1548626845121035354579951

theorem tailTrace_3015940 : CollatzResearch.WordTrace tailWord_3015940 prefixEnd_3015940 1548626845121035354579951 := by
  unfold tailWord_3015940
  simp only [CollatzResearch.WordTrace]
  refine ⟨55000184346885968194686637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73333579129181290926248849 55000184346885968194686637)
  ·
    refine ⟨20625069130082238073007489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55000184346885968194686637 20625069130082238073007489)
    ·
      refine ⟨15468801847561678554755617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20625069130082238073007489 15468801847561678554755617)
      ·
        refine ⟨11601601385671258916066713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15468801847561678554755617 11601601385671258916066713)
        ·
          refine ⟨8701201039253444187050035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11601601385671258916066713 8701201039253444187050035)
          ·
            refine ⟨13051801558880166280575053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8701201039253444187050035 13051801558880166280575053)
            ·
              refine ⟨4894425584580062355215645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13051801558880166280575053 4894425584580062355215645)
              ·
                refine ⟨1835409594217523383205867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4894425584580062355215645 1835409594217523383205867)
                ·
                  refine ⟨2753114391326285074808801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835409594217523383205867 2753114391326285074808801)
                  ·
                    refine ⟨2064835793494713806106601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2753114391326285074808801 2064835793494713806106601)
                    ·
                      refine ⟨1548626845121035354579951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064835793494713806106601 1548626845121035354579951)
                      ·
                        rfl

theorem cell23_3015940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_3015940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015940 prefixEnd_3015940 := by exact prefixLift 3015940
  have htrace : WordTrace (prefixWord ++ tailWord_3015940) baseStart_3015940 baseEnd_3015940 := by
    simpa [prefixWord, tailWord_3015940, baseEnd_3015940] using wordTrace_append hprefix tailTrace_3015940
  have hstable : (prefixWord ++ tailWord_3015940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015940).length < 2 ^ (prefixWord ++ tailWord_3015940).sum := by decide
  have hdescent : baseEnd_3015940 < baseStart_3015940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015972 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_3015972 : Nat := 118140960795 + 3015972 * 2 ^ 59
def prefixEnd_3015972 : Nat := 4983230072969 + 3 ^ 40 * 3015972 * 2
def baseEnd_3015972 : Nat := 516214425500659743126601

theorem tailTrace_3015972 : CollatzResearch.WordTrace tailWord_3015972 prefixEnd_3015972 516214425500659743126601 := by
  unfold tailWord_3015972
  simp only [CollatzResearch.WordTrace]
  refine ⟨55000767914828002927269085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73334357219770670569692113 55000767914828002927269085)
  ·
    refine ⟨20625287968060501097725907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55000767914828002927269085 20625287968060501097725907)
    ·
      refine ⟨30937931952090751646588861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20625287968060501097725907 30937931952090751646588861)
      ·
        refine ⟨11601724482034031867470823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30937931952090751646588861 11601724482034031867470823)
        ·
          refine ⟨17402586723051047801206235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11601724482034031867470823 17402586723051047801206235)
          ·
            refine ⟨26103880084576571701809353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17402586723051047801206235 26103880084576571701809353)
            ·
              refine ⟨19577910063432428776357015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26103880084576571701809353 19577910063432428776357015)
              ·
                refine ⟨29366865095148643164535523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19577910063432428776357015 29366865095148643164535523)
                ·
                  refine ⟨44050297642722964746803285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29366865095148643164535523 44050297642722964746803285)
                  ·
                    refine ⟨516214425500659743126601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44050297642722964746803285 516214425500659743126601)
                    ·
                      rfl

theorem cell23_3015972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_3015972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015972 prefixEnd_3015972 := by exact prefixLift 3015972
  have htrace : WordTrace (prefixWord ++ tailWord_3015972) baseStart_3015972 baseEnd_3015972 := by
    simpa [prefixWord, tailWord_3015972, baseEnd_3015972] using wordTrace_append hprefix tailTrace_3015972
  have hstable : (prefixWord ++ tailWord_3015972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015972).length < 2 ^ (prefixWord ++ tailWord_3015972).sum := by decide
  have hdescent : baseEnd_3015972 < baseStart_3015972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015973 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 2, 1, 3]
def baseStart_3015973 : Nat := 118140960795 + 3015973 * 2 ^ 59
def prefixEnd_3015973 : Nat := 4983230072969 + 3 ^ 40 * 3015973 * 2
def baseEnd_3015973 : Nat := 1548643789982633725467299

theorem tailTrace_3015973 : CollatzResearch.WordTrace tailWord_3015973 prefixEnd_3015973 1548643789982633725467299 := by
  unfold tailWord_3015973
  simp only [CollatzResearch.WordTrace]
  refine ⟨110001572302652383025324573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73334381535101588683549715 110001572302652383025324573)
  ·
    refine ⟨41250589613494643634496715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110001572302652383025324573 41250589613494643634496715)
    ·
      refine ⟨61875884420241965451745073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41250589613494643634496715 61875884420241965451745073)
      ·
        refine ⟨46406913315181474088808805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61875884420241965451745073 46406913315181474088808805)
        ·
          refine ⟨8701296246596526391651651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46406913315181474088808805 8701296246596526391651651)
          ·
            refine ⟨13051944369894789587477477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8701296246596526391651651 13051944369894789587477477)
            ·
              refine ⟨2447239569355273047652027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13051944369894789587477477 2447239569355273047652027)
              ·
                refine ⟨3670859354032909571478041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447239569355273047652027 3670859354032909571478041)
                ·
                  refine ⟨2753144515524682178608531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3670859354032909571478041 2753144515524682178608531)
                  ·
                    refine ⟨4129716773287023267912797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753144515524682178608531 4129716773287023267912797)
                    ·
                      refine ⟨1548643789982633725467299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4129716773287023267912797 1548643789982633725467299)
                      ·
                        rfl

theorem cell23_3015973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_3015973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015973 prefixEnd_3015973 := by exact prefixLift 3015973
  have htrace : WordTrace (prefixWord ++ tailWord_3015973) baseStart_3015973 baseEnd_3015973 := by
    simpa [prefixWord, tailWord_3015973, baseEnd_3015973] using wordTrace_append hprefix tailTrace_3015973
  have hstable : (prefixWord ++ tailWord_3015973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015973).length < 2 ^ (prefixWord ++ tailWord_3015973).sum := by decide
  have hdescent : baseEnd_3015973 < baseStart_3015973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015992 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3015992 : Nat := 118140960795 + 3015992 * 2 ^ 59
def prefixEnd_3015992 : Nat := 4983230072969 + 3 ^ 40 * 3015992 * 2
def baseEnd_3015992 : Nat := 1548653546115069151129711

theorem tailTrace_3015992 : CollatzResearch.WordTrace tailWord_3015992 prefixEnd_3015992 1548653546115069151129711 := by
  unfold tailWord_3015992
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001132644791774635133115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73334843526389032846844153 55001132644791774635133115)
  ·
    refine ⟨82501698967187661952699673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55001132644791774635133115 82501698967187661952699673)
    ·
      refine ⟨61876274225390746464524755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82501698967187661952699673 61876274225390746464524755)
      ·
        refine ⟨92814411338086119696787133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61876274225390746464524755 92814411338086119696787133)
        ·
          refine ⟨34805404251782294886295175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92814411338086119696787133 34805404251782294886295175)
          ·
            refine ⟨52208106377673442329442763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34805404251782294886295175 52208106377673442329442763)
            ·
              refine ⟨78312159566510163494164145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52208106377673442329442763 78312159566510163494164145)
              ·
                refine ⟨58734119674882622620623109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78312159566510163494164145 58734119674882622620623109)
                ·
                  refine ⟨11012647439040491741366833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58734119674882622620623109 11012647439040491741366833)
                  ·
                    refine ⟨8259485579280368806025125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11012647439040491741366833 8259485579280368806025125)
                    ·
                      refine ⟨1548653546115069151129711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8259485579280368806025125 1548653546115069151129711)
                      ·
                        rfl

theorem cell23_3015992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3015992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015992 prefixEnd_3015992 := by exact prefixLift 3015992
  have htrace : WordTrace (prefixWord ++ tailWord_3015992) baseStart_3015992 baseEnd_3015992 := by
    simpa [prefixWord, tailWord_3015992, baseEnd_3015992] using wordTrace_append hprefix tailTrace_3015992
  have hstable : (prefixWord ++ tailWord_3015992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015992).length < 2 ^ (prefixWord ++ tailWord_3015992).sum := by decide
  have hdescent : baseEnd_3015992 < baseStart_3015992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3015996 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_3015996 : Nat := 118140960795 + 3015996 * 2 ^ 59
def prefixEnd_3015996 : Nat := 4983230072969 + 3 ^ 40 * 3015996 * 2
def baseEnd_3015996 : Nat := 1548655600037687135479693

theorem tailTrace_3015996 : CollatzResearch.WordTrace tailWord_3015996 prefixEnd_3015996 1548655600037687135479693 := by
  unfold tailWord_3015996
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001205590784528976705921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73334940787712705302274561 55001205590784528976705921)
  ·
    refine ⟨41250904193088396732529441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55001205590784528976705921 41250904193088396732529441)
    ·
      refine ⟨30938178144816297549397081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41250904193088396732529441 30938178144816297549397081)
      ·
        refine ⟨23203633608612223162047811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30938178144816297549397081 23203633608612223162047811)
        ·
          refine ⟨34805450412918334743071717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23203633608612223162047811 34805450412918334743071717)
          ·
            refine ⟨6526021952422187764325947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34805450412918334743071717 6526021952422187764325947)
            ·
              refine ⟨9789032928633281646488921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526021952422187764325947 9789032928633281646488921)
              ·
                refine ⟨7341774696474961234866691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9789032928633281646488921 7341774696474961234866691)
                ·
                  refine ⟨11012662044712441852300037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341774696474961234866691 11012662044712441852300037)
                  ·
                    refine ⟨2064874133383582847306257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11012662044712441852300037 2064874133383582847306257)
                    ·
                      refine ⟨1548655600037687135479693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064874133383582847306257 1548655600037687135479693)
                      ·
                        rfl

theorem cell23_3015996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_3015996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3015996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3015996 prefixEnd_3015996 := by exact prefixLift 3015996
  have htrace : WordTrace (prefixWord ++ tailWord_3015996) baseStart_3015996 baseEnd_3015996 := by
    simpa [prefixWord, tailWord_3015996, baseEnd_3015996] using wordTrace_append hprefix tailTrace_3015996
  have hstable : (prefixWord ++ tailWord_3015996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3015996).length < 2 ^ (prefixWord ++ tailWord_3015996).sum := by decide
  have hdescent : baseEnd_3015996 < baseStart_3015996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3015996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016019 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 5]
def baseStart_3016019 : Nat := 118140960795 + 3016019 * 2 ^ 59
def prefixEnd_3016019 : Nat := 4983230072969 + 3 ^ 40 * 3016019 * 2
def baseEnd_3016019 : Nat := 172074156676971171721343

theorem tailTrace_3016019 : CollatzResearch.WordTrace tailWord_3016019 prefixEnd_3016019 172074156676971171721343 := by
  unfold tailWord_3016019
  simp only [CollatzResearch.WordTrace]
  refine ⟨110003250060485732881499111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73335500040323821920999407 110003250060485732881499111)
  ·
    refine ⟨165004875090728599322248667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110003250060485732881499111 165004875090728599322248667)
    ·
      refine ⟨247507312636092898983373001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165004875090728599322248667 247507312636092898983373001)
      ·
        refine ⟨185630484477069674237529751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247507312636092898983373001 185630484477069674237529751)
        ·
          refine ⟨278445726715604511356294627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185630484477069674237529751 278445726715604511356294627)
          ·
            refine ⟨417668590073406767034441941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278445726715604511356294627 417668590073406767034441941)
            ·
              refine ⟨9789107579845471102369733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 417668590073406767034441941 9789107579845471102369733)
              ·
                refine ⟨1835457671221025831694325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9789107579845471102369733 1835457671221025831694325)
                ·
                  refine ⟨172074156676971171721343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1835457671221025831694325 172074156676971171721343)
                  ·
                    rfl

theorem cell23_3016019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 5].length) (baseStart_3016019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016019 prefixEnd_3016019 := by exact prefixLift 3016019
  have htrace : WordTrace (prefixWord ++ tailWord_3016019) baseStart_3016019 baseEnd_3016019 := by
    simpa [prefixWord, tailWord_3016019, baseEnd_3016019] using wordTrace_append hprefix tailTrace_3016019
  have hstable : (prefixWord ++ tailWord_3016019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016019).length < 2 ^ (prefixWord ++ tailWord_3016019).sum := by decide
  have hdescent : baseEnd_3016019 < baseStart_3016019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016049 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 2, 5]
def baseStart_3016049 : Nat := 118140960795 + 3016049 * 2 ^ 59
def prefixEnd_3016049 : Nat := 4983230072969 + 3 ^ 40 * 3016049 * 2
def baseEnd_3016049 : Nat := 516227604837458476038983

theorem tailTrace_3016049 : CollatzResearch.WordTrace tailWord_3016049 prefixEnd_3016049 516227604837458476038983 := by
  unfold tailWord_3016049
  simp only [CollatzResearch.WordTrace]
  refine ⟨110004344250377048005091201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73336229500251365336727467 110004344250377048005091201)
  ·
    refine ⟨82503258187782786003818401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110004344250377048005091201 82503258187782786003818401)
    ·
      refine ⟨61877443640837089502863801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82503258187782786003818401 61877443640837089502863801)
      ·
        refine ⟨46408082730627817127147851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61877443640837089502863801 46408082730627817127147851)
        ·
          refine ⟨69612124095941725690721777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46408082730627817127147851 69612124095941725690721777)
          ·
            refine ⟨52209093071956294268041333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69612124095941725690721777 52209093071956294268041333)
            ·
              refine ⟨4894602475495902587628875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52209093071956294268041333 4894602475495902587628875)
              ·
                refine ⟨7341903713243853881443313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894602475495902587628875 7341903713243853881443313)
                ·
                  refine ⟨5506427784932890411082485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341903713243853881443313 5506427784932890411082485)
                  ·
                    refine ⟨516227604837458476038983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5506427784932890411082485 516227604837458476038983)
                    ·
                      rfl

theorem cell23_3016049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_3016049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016049 prefixEnd_3016049 := by exact prefixLift 3016049
  have htrace : WordTrace (prefixWord ++ tailWord_3016049) baseStart_3016049 baseEnd_3016049 := by
    simpa [prefixWord, tailWord_3016049, baseEnd_3016049] using wordTrace_append hprefix tailTrace_3016049
  have hstable : (prefixWord ++ tailWord_3016049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016049).length < 2 ^ (prefixWord ++ tailWord_3016049).sum := by decide
  have hdescent : baseEnd_3016049 < baseStart_3016049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016053 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 5]
def baseStart_3016053 : Nat := 118140960795 + 3016053 * 2 ^ 59
def prefixEnd_3016053 : Nat := 4983230072969 + 3 ^ 40 * 3016053 * 2
def baseEnd_3016053 : Nat := 172076096492777045829659

theorem tailTrace_3016053 : CollatzResearch.WordTrace tailWord_3016053 prefixEnd_3016053 172076096492777045829659 := by
  unfold tailWord_3016053
  simp only [CollatzResearch.WordTrace]
  refine ⟨110004490142362556688236813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73336326761575037792157875 110004490142362556688236813)
  ·
    refine ⟨41251683803385958758088805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110004490142362556688236813 41251683803385958758088805)
    ·
      refine ⟨7734690713134867267141651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41251683803385958758088805 7734690713134867267141651)
      ·
        refine ⟨11602036069702300900712477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7734690713134867267141651 11602036069702300900712477)
        ·
          refine ⟨4350763526138362837767179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11602036069702300900712477 4350763526138362837767179)
          ·
            refine ⟨6526145289207544256650769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350763526138362837767179 6526145289207544256650769)
            ·
              refine ⟨4894608966905658192488077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6526145289207544256650769 4894608966905658192488077)
              ·
                refine ⟨1835478362589621822183029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4894608966905658192488077 1835478362589621822183029)
                ·
                  refine ⟨172076096492777045829659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1835478362589621822183029 172076096492777045829659)
                  ·
                    rfl

theorem cell23_3016053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_3016053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016053 prefixEnd_3016053 := by exact prefixLift 3016053
  have htrace : WordTrace (prefixWord ++ tailWord_3016053) baseStart_3016053 baseEnd_3016053 := by
    simpa [prefixWord, tailWord_3016053, baseEnd_3016053] using wordTrace_append hprefix tailTrace_3016053
  have hstable : (prefixWord ++ tailWord_3016053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016053).length < 2 ^ (prefixWord ++ tailWord_3016053).sum := by decide
  have hdescent : baseEnd_3016053 < baseStart_3016053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016069 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_3016069 : Nat := 118140960795 + 3016069 * 2 ^ 59
def prefixEnd_3016069 : Nat := 4983230072969 + 3 ^ 40 * 3016069 * 2
def baseEnd_3016069 : Nat := 1548693084125465349866857

theorem tailTrace_3016069 : CollatzResearch.WordTrace tailWord_3016069 prefixEnd_3016069 1548693084125465349866857 := by
  unfold tailWord_3016069
  simp only [CollatzResearch.WordTrace]
  refine ⟨110005073710304591420819261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73336715806869727613879507 110005073710304591420819261)
  ·
    refine ⟨41251902641364221782807223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110005073710304591420819261 41251902641364221782807223)
    ·
      refine ⟨61877853962046332674210835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41251902641364221782807223 61877853962046332674210835)
      ·
        refine ⟨92816780943069499011316253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61877853962046332674210835 92816780943069499011316253)
        ·
          refine ⟨34806292853651062129243595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92816780943069499011316253 34806292853651062129243595)
          ·
            refine ⟨52209439280476593193865393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34806292853651062129243595 52209439280476593193865393)
            ·
              refine ⟨39157079460357444895399045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52209439280476593193865393 39157079460357444895399045)
              ·
                refine ⟨7341952398817020917887321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39157079460357444895399045 7341952398817020917887321)
                ·
                  refine ⟨5506464299112765688415491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341952398817020917887321 5506464299112765688415491)
                  ·
                    refine ⟨8259696448669148532623237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5506464299112765688415491 8259696448669148532623237)
                    ·
                      refine ⟨1548693084125465349866857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8259696448669148532623237 1548693084125465349866857)
                      ·
                        rfl

theorem cell23_3016069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_3016069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016069 prefixEnd_3016069 := by exact prefixLift 3016069
  have htrace : WordTrace (prefixWord ++ tailWord_3016069) baseStart_3016069 baseEnd_3016069 := by
    simpa [prefixWord, tailWord_3016069, baseEnd_3016069] using wordTrace_append hprefix tailTrace_3016069
  have hstable : (prefixWord ++ tailWord_3016069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016069).length < 2 ^ (prefixWord ++ tailWord_3016069).sum := by decide
  have hdescent : baseEnd_3016069 < baseStart_3016069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016089 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_3016089 : Nat := 118140960795 + 3016089 * 2 ^ 59
def prefixEnd_3016089 : Nat := 4983230072969 + 3 ^ 40 * 3016089 * 2
def baseEnd_3016089 : Nat := 1548703353738555271616765

theorem tailTrace_3016089 : CollatzResearch.WordTrace tailWord_3016089 prefixEnd_3016089 1548703353738555271616765 := by
  unfold tailWord_3016089
  simp only [CollatzResearch.WordTrace]
  refine ⟨110005803170232134836547321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73337202113488089891031547 110005803170232134836547321)
  ·
    refine ⟨82504352377674101127410491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110005803170232134836547321 82504352377674101127410491)
    ·
      refine ⟨123756528566511151691115737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82504352377674101127410491 123756528566511151691115737)
      ·
        refine ⟨92817396424883363768336803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123756528566511151691115737 92817396424883363768336803)
        ·
          refine ⟨139226094637325045652505205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92817396424883363768336803 139226094637325045652505205)
          ·
            refine ⟨13052446372249223029922363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139226094637325045652505205 13052446372249223029922363)
            ·
              refine ⟨19578669558373834544883545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13052446372249223029922363 19578669558373834544883545)
              ·
                refine ⟨14684002168780375908662659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19578669558373834544883545 14684002168780375908662659)
                ·
                  refine ⟨22026003253170563862993989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14684002168780375908662659 22026003253170563862993989)
                  ·
                    refine ⟨4129875609969480724311373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22026003253170563862993989 4129875609969480724311373)
                    ·
                      refine ⟨1548703353738555271616765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4129875609969480724311373 1548703353738555271616765)
                      ·
                        rfl

theorem cell23_3016089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_3016089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016089 prefixEnd_3016089 := by exact prefixLift 3016089
  have htrace : WordTrace (prefixWord ++ tailWord_3016089) baseStart_3016089 baseEnd_3016089 := by
    simpa [prefixWord, tailWord_3016089, baseEnd_3016089] using wordTrace_append hprefix tailTrace_3016089
  have hstable : (prefixWord ++ tailWord_3016089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016089).length < 2 ^ (prefixWord ++ tailWord_3016089).sum := by decide
  have hdescent : baseEnd_3016089 < baseStart_3016089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016112 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_3016112 : Nat := 118140960795 + 3016112 * 2 ^ 59
def prefixEnd_3016112 : Nat := 4983230072969 + 3 ^ 40 * 3016112 * 2
def baseEnd_3016112 : Nat := 1548715163793608681629159

theorem tailTrace_3016112 : CollatzResearch.WordTrace tailWord_3016112 prefixEnd_3016112 1548715163793608681629159 := by
  unfold tailWord_3016112
  simp only [CollatzResearch.WordTrace]
  refine ⟨55003321024574404882317295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73337761366099206509756393 55003321024574404882317295)
  ·
    refine ⟨82504981536861607323475943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55003321024574404882317295 82504981536861607323475943)
    ·
      refine ⟨123757472305292410985213915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82504981536861607323475943 123757472305292410985213915)
      ·
        refine ⟨185636208457938616477820873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123757472305292410985213915 185636208457938616477820873)
        ·
          refine ⟨139227156343453962358365655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185636208457938616477820873 139227156343453962358365655)
          ·
            refine ⟨208840734515180943537548483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139227156343453962358365655 208840734515180943537548483)
            ·
              refine ⟨313261101772771415306322725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208840734515180943537548483 313261101772771415306322725)
              ·
                refine ⟨58736456582394640369935511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313261101772771415306322725 58736456582394640369935511)
                ·
                  refine ⟨88104684873591960554903267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58736456582394640369935511 88104684873591960554903267)
                  ·
                    refine ⟨132157027310387940832354901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88104684873591960554903267 132157027310387940832354901)
                    ·
                      refine ⟨1548715163793608681629159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 132157027310387940832354901 1548715163793608681629159)
                      ·
                        rfl

theorem cell23_3016112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_3016112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016112 prefixEnd_3016112 := by exact prefixLift 3016112
  have htrace : WordTrace (prefixWord ++ tailWord_3016112) baseStart_3016112 baseEnd_3016112 := by
    simpa [prefixWord, tailWord_3016112, baseEnd_3016112] using wordTrace_append hprefix tailTrace_3016112
  have hstable : (prefixWord ++ tailWord_3016112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016112).length < 2 ^ (prefixWord ++ tailWord_3016112).sum := by decide
  have hdescent : baseEnd_3016112 < baseStart_3016112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016163 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 2, 3, 2]
def baseStart_3016163 : Nat := 118140960795 + 3016163 * 2 ^ 59
def prefixEnd_3016163 : Nat := 4983230072969 + 3 ^ 40 * 3016163 * 2
def baseEnd_3016163 : Nat := 1548741351306987982091425

theorem tailTrace_3016163 : CollatzResearch.WordTrace tailWord_3016163 prefixEnd_3016163 1548741351306987982091425 := by
  unfold tailWord_3016163
  simp only [CollatzResearch.WordTrace]
  refine ⟨110008502171964045474741143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73339001447976030316494095 110008502171964045474741143)
  ·
    refine ⟨165012753257946068212111715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110008502171964045474741143 165012753257946068212111715)
    ·
      refine ⟨247519129886919102318167573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165012753257946068212111715 247519129886919102318167573)
      ·
        refine ⟨11602459213449332921164105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 247519129886919102318167573 11602459213449332921164105)
        ·
          refine ⟨8701844410086999690873079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11602459213449332921164105 8701844410086999690873079)
          ·
            refine ⟨13052766615130499536309619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8701844410086999690873079 13052766615130499536309619)
            ·
              refine ⟨19579149922695749304464429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13052766615130499536309619 19579149922695749304464429)
              ·
                refine ⟨7342181221010905989174161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19579149922695749304464429 7342181221010905989174161)
                ·
                  refine ⟨5506635915758179491880621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7342181221010905989174161 5506635915758179491880621)
                  ·
                    refine ⟨2064988468409317309455233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5506635915758179491880621 2064988468409317309455233)
                    ·
                      refine ⟨1548741351306987982091425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2064988468409317309455233 1548741351306987982091425)
                      ·
                        rfl

theorem cell23_3016163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_3016163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016163 prefixEnd_3016163 := by exact prefixLift 3016163
  have htrace : WordTrace (prefixWord ++ tailWord_3016163) baseStart_3016163 baseEnd_3016163 := by
    simpa [prefixWord, tailWord_3016163, baseEnd_3016163] using wordTrace_append hprefix tailTrace_3016163
  have hstable : (prefixWord ++ tailWord_3016163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016163).length < 2 ^ (prefixWord ++ tailWord_3016163).sum := by decide
  have hdescent : baseEnd_3016163 < baseStart_3016163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016179 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5]
def baseStart_3016179 : Nat := 118140960795 + 3016179 * 2 ^ 59
def prefixEnd_3016179 : Nat := 4983230072969 + 3 ^ 40 * 3016179 * 2
def baseEnd_3016179 : Nat := 1548749566997459919491351

theorem tailTrace_3016179 : CollatzResearch.WordTrace tailWord_3016179 prefixEnd_3016179 1548749566997459919491351 := by
  unfold tailWord_3016179
  simp only [CollatzResearch.WordTrace]
  refine ⟨110009085739906080207323591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73339390493270720138215727 110009085739906080207323591)
  ·
    refine ⟨165013628609859120310985387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110009085739906080207323591 165013628609859120310985387)
    ·
      refine ⟨247520442914788680466478081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165013628609859120310985387 247520442914788680466478081)
      ·
        refine ⟨185640332186091510349858561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247520442914788680466478081 185640332186091510349858561)
        ·
          refine ⟨139230249139568632762393921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185640332186091510349858561 139230249139568632762393921)
          ·
            refine ⟨104422686854676474571795441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139230249139568632762393921 104422686854676474571795441)
            ·
              refine ⟨78317015141007355928846581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104422686854676474571795441 78317015141007355928846581)
              ·
                refine ⟨7342220169469439618329367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78317015141007355928846581 7342220169469439618329367)
                ·
                  refine ⟨11013330254204159427494051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7342220169469439618329367 11013330254204159427494051)
                  ·
                    refine ⟨16519995381306239141241077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11013330254204159427494051 16519995381306239141241077)
                    ·
                      refine ⟨1548749566997459919491351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16519995381306239141241077 1548749566997459919491351)
                      ·
                        rfl

theorem cell23_3016179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_3016179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016179 prefixEnd_3016179 := by exact prefixLift 3016179
  have htrace : WordTrace (prefixWord ++ tailWord_3016179) baseStart_3016179 baseEnd_3016179 := by
    simpa [prefixWord, tailWord_3016179, baseEnd_3016179] using wordTrace_append hprefix tailTrace_3016179
  have hstable : (prefixWord ++ tailWord_3016179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016179).length < 2 ^ (prefixWord ++ tailWord_3016179).sum := by decide
  have hdescent : baseEnd_3016179 < baseStart_3016179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016227 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 1, 1, 4]
def baseStart_3016227 : Nat := 118140960795 + 3016227 * 2 ^ 59
def prefixEnd_3016227 : Nat := 4983230072969 + 3 ^ 40 * 3016227 * 2
def baseEnd_3016227 : Nat := 1548774214068875731691131

theorem tailTrace_3016227 : CollatzResearch.WordTrace tailWord_3016227 prefixEnd_3016227 1548774214068875731691131 := by
  unfold tailWord_3016227
  simp only [CollatzResearch.WordTrace]
  refine ⟨110010836443732184405070935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73340557629154789603380623 110010836443732184405070935)
  ·
    refine ⟨165016254665598276607606403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110010836443732184405070935 165016254665598276607606403)
    ·
      refine ⟨247524381998397414911409605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165016254665598276607606403 247524381998397414911409605)
      ·
        refine ⟨46410821624699515295889301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247524381998397414911409605 46410821624699515295889301)
        ·
          refine ⟨2175507263657789779494811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46410821624699515295889301 2175507263657789779494811)
          ·
            refine ⟨3263260895486684669242217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175507263657789779494811 3263260895486684669242217)
            ·
              refine ⟨2447445671615013501931663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3263260895486684669242217 2447445671615013501931663)
              ·
                refine ⟨3671168507422520252897495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447445671615013501931663 3671168507422520252897495)
                ·
                  refine ⟨5506752761133780379346243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671168507422520252897495 5506752761133780379346243)
                  ·
                    refine ⟨8260129141700670569019365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5506752761133780379346243 8260129141700670569019365)
                    ·
                      refine ⟨1548774214068875731691131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8260129141700670569019365 1548774214068875731691131)
                      ·
                        rfl

theorem cell23_3016227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_3016227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016227 prefixEnd_3016227 := by exact prefixLift 3016227
  have htrace : WordTrace (prefixWord ++ tailWord_3016227) baseStart_3016227 baseEnd_3016227 := by
    simpa [prefixWord, tailWord_3016227, baseEnd_3016227] using wordTrace_append hprefix tailTrace_3016227
  have hstable : (prefixWord ++ tailWord_3016227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016227).length < 2 ^ (prefixWord ++ tailWord_3016227).sum := by decide
  have hdescent : baseEnd_3016227 < baseStart_3016227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016243 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 3]
def baseStart_3016243 : Nat := 118140960795 + 3016243 * 2 ^ 59
def prefixEnd_3016243 : Nat := 4983230072969 + 3 ^ 40 * 3016243 * 2
def baseEnd_3016243 : Nat := 1548782429759347669091057

theorem tailTrace_3016243 : CollatzResearch.WordTrace tailWord_3016243 prefixEnd_3016243 1548782429759347669091057 := by
  unfold tailWord_3016243
  simp only [CollatzResearch.WordTrace]
  refine ⟨110011420011674219137653383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73340946674449479425102255 110011420011674219137653383)
  ·
    refine ⟨165017130017511328706480075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110011420011674219137653383 165017130017511328706480075)
    ·
      refine ⟨247525695026266993059720113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165017130017511328706480075 247525695026266993059720113)
      ·
        refine ⟨185644271269700244794790085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247525695026266993059720113 185644271269700244794790085)
        ·
          refine ⟨34808300863068795899023141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185644271269700244794790085 34808300863068795899023141)
          ·
            refine ⟨6526556411825399231066839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34808300863068795899023141 6526556411825399231066839)
            ·
              refine ⟨9789834617738098846600259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526556411825399231066839 9789834617738098846600259)
              ·
                refine ⟨14684751926607148269900389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9789834617738098846600259 14684751926607148269900389)
                ·
                  refine ⟨2753390986238840300606323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14684751926607148269900389 2753390986238840300606323)
                  ·
                    refine ⟨4130086479358260450909485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753390986238840300606323 4130086479358260450909485)
                    ·
                      refine ⟨1548782429759347669091057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130086479358260450909485 1548782429759347669091057)
                      ·
                        rfl

theorem cell23_3016243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_3016243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016243 prefixEnd_3016243 := by exact prefixLift 3016243
  have htrace : WordTrace (prefixWord ++ tailWord_3016243) baseStart_3016243 baseEnd_3016243 := by
    simpa [prefixWord, tailWord_3016243, baseEnd_3016243] using wordTrace_append hprefix tailTrace_3016243
  have hstable : (prefixWord ++ tailWord_3016243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016243).length < 2 ^ (prefixWord ++ tailWord_3016243).sum := by decide
  have hdescent : baseEnd_3016243 < baseStart_3016243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016300 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 2, 2, 2]
def baseStart_3016300 : Nat := 118140960795 + 3016300 * 2 ^ 59
def prefixEnd_3016300 : Nat := 4983230072969 + 3 ^ 40 * 3016300 * 2
def baseEnd_3016300 : Nat := 1548811698156653946078295

theorem tailTrace_3016300 : CollatzResearch.WordTrace tailWord_3016300 prefixEnd_3016300 1548811698156653946078295 := by
  unfold tailWord_3016300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55006749486233858936239177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73342332648311811914985569 55006749486233858936239177)
  ·
    refine ⟨41255062114675394202179383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55006749486233858936239177 41255062114675394202179383)
    ·
      refine ⟨61882593172013091303269075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41255062114675394202179383 61882593172013091303269075)
      ·
        refine ⟨92823889758019636954903613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61882593172013091303269075 92823889758019636954903613)
        ·
          refine ⟨34808958659257363858088855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92823889758019636954903613 34808958659257363858088855)
          ·
            refine ⟨52213437988886045787133283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34808958659257363858088855 52213437988886045787133283)
            ·
              refine ⟨78320156983329068680699925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52213437988886045787133283 78320156983329068680699925)
              ·
                refine ⟨3671257358593550094407809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78320156983329068680699925 3671257358593550094407809)
                ·
                  refine ⟨2753443018945162570805857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671257358593550094407809 2753443018945162570805857)
                  ·
                    refine ⟨2065082264208871928104393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2753443018945162570805857 2065082264208871928104393)
                    ·
                      refine ⟨1548811698156653946078295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065082264208871928104393 1548811698156653946078295)
                      ·
                        rfl

theorem cell23_3016300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_3016300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016300 prefixEnd_3016300 := by exact prefixLift 3016300
  have htrace : WordTrace (prefixWord ++ tailWord_3016300) baseStart_3016300 baseEnd_3016300 := by
    simpa [prefixWord, tailWord_3016300, baseEnd_3016300] using wordTrace_append hprefix tailTrace_3016300
  have hstable : (prefixWord ++ tailWord_3016300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016300).length < 2 ^ (prefixWord ++ tailWord_3016300).sum := by decide
  have hdescent : baseEnd_3016300 < baseStart_3016300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016316 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_3016316 : Nat := 118140960795 + 3016316 * 2 ^ 59
def prefixEnd_3016316 : Nat := 4983230072969 + 3 ^ 40 * 3016316 * 2
def baseEnd_3016316 : Nat := 1548819913847125883478221

theorem tailTrace_3016316 : CollatzResearch.WordTrace tailWord_3016316 prefixEnd_3016316 1548819913847125883478221 := by
  unfold tailWord_3016316
  simp only [CollatzResearch.WordTrace]
  refine ⟨55007041270204876302530401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73342721693606501736707201 55007041270204876302530401)
  ·
    refine ⟨41255280952653657226897801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55007041270204876302530401 41255280952653657226897801)
    ·
      refine ⟨30941460714490242920173351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41255280952653657226897801 30941460714490242920173351)
      ·
        refine ⟨46412191071735364380260027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30941460714490242920173351 46412191071735364380260027)
        ·
          refine ⟨69618286607603046570390041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46412191071735364380260027 69618286607603046570390041)
          ·
            refine ⟨52213714955702284927792531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69618286607603046570390041 52213714955702284927792531)
            ·
              refine ⟨78320572433553427391688797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52213714955702284927792531 78320572433553427391688797)
              ·
                refine ⟨29370214662582535271883299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78320572433553427391688797 29370214662582535271883299)
                ·
                  refine ⟨44055321993873802907824949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29370214662582535271883299 44055321993873802907824949)
                  ·
                    refine ⟨4130186436925669022608589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44055321993873802907824949 4130186436925669022608589)
                    ·
                      refine ⟨1548819913847125883478221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130186436925669022608589 1548819913847125883478221)
                      ·
                        rfl

theorem cell23_3016316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_3016316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016316 prefixEnd_3016316 := by exact prefixLift 3016316
  have htrace : WordTrace (prefixWord ++ tailWord_3016316) baseStart_3016316 baseEnd_3016316 := by
    simpa [prefixWord, tailWord_3016316, baseEnd_3016316] using wordTrace_append hprefix tailTrace_3016316
  have hstable : (prefixWord ++ tailWord_3016316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016316).length < 2 ^ (prefixWord ++ tailWord_3016316).sum := by decide
  have hdescent : baseEnd_3016316 < baseStart_3016316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016317 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_3016317 : Nat := 118140960795 + 3016317 * 2 ^ 59
def prefixEnd_3016317 : Nat := 4983230072969 + 3 ^ 40 * 3016317 * 2
def baseEnd_3016317 : Nat := 1548820427327780379565717

theorem tailTrace_3016317 : CollatzResearch.WordTrace tailWord_3016317 prefixEnd_3016317 1548820427327780379565717 := by
  unfold tailWord_3016317
  simp only [CollatzResearch.WordTrace]
  refine ⟨110014119013406129775847205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73342746008937419850564803 110014119013406129775847205)
  ·
    refine ⟨20627647315013649332971351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110014119013406129775847205 20627647315013649332971351)
    ·
      refine ⟨30941470972520473999457027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20627647315013649332971351 30941470972520473999457027)
      ·
        refine ⟨46412206458780710999185541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30941470972520473999457027 46412206458780710999185541)
        ·
          refine ⟨8702288711021383312347289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46412206458780710999185541 8702288711021383312347289)
          ·
            refine ⟨6526716533266037484260467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8702288711021383312347289 6526716533266037484260467)
            ·
              refine ⟨9790074799899056226390701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526716533266037484260467 9790074799899056226390701)
              ·
                refine ⟨3671278049962146084896513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9790074799899056226390701 3671278049962146084896513)
                ·
                  refine ⟨2753458537471609563672385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671278049962146084896513 2753458537471609563672385)
                  ·
                    refine ⟨2065093903103707172754289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2753458537471609563672385 2065093903103707172754289)
                    ·
                      refine ⟨1548820427327780379565717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065093903103707172754289 1548820427327780379565717)
                      ·
                        rfl

theorem cell23_3016317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_3016317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016317 prefixEnd_3016317 := by exact prefixLift 3016317
  have htrace : WordTrace (prefixWord ++ tailWord_3016317) baseStart_3016317 baseEnd_3016317 := by
    simpa [prefixWord, tailWord_3016317, baseEnd_3016317] using wordTrace_append hprefix tailTrace_3016317
  have hstable : (prefixWord ++ tailWord_3016317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016317).length < 2 ^ (prefixWord ++ tailWord_3016317).sum := by decide
  have hdescent : baseEnd_3016317 < baseStart_3016317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016353 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3016353 : Nat := 118140960795 + 3016353 * 2 ^ 59
def prefixEnd_3016353 : Nat := 4983230072969 + 3 ^ 40 * 3016353 * 2
def baseEnd_3016353 : Nat := 516279637543780746238517

theorem tailTrace_3016353 : CollatzResearch.WordTrace tailWord_3016353 prefixEnd_3016353 516279637543780746238517 := by
  unfold tailWord_3016353
  simp only [CollatzResearch.WordTrace]
  refine ⟨110015432041275707924157713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73343621360850471949438475 110015432041275707924157713)
  ·
    refine ⟨82511574030956780943118285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110015432041275707924157713 82511574030956780943118285)
    ·
      refine ⟨30941840261608792853669357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82511574030956780943118285 30941840261608792853669357)
      ·
        refine ⟨11603190098103297320126009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30941840261608792853669357 11603190098103297320126009)
        ·
          refine ⟨8702392573577472990094507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11603190098103297320126009 8702392573577472990094507)
          ·
            refine ⟨13053588860366209485141761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8702392573577472990094507 13053588860366209485141761)
            ·
              refine ⟨9790191645274657113856321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13053588860366209485141761 9790191645274657113856321)
              ·
                refine ⟨7342643733955992835392241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9790191645274657113856321 7342643733955992835392241)
                ·
                  refine ⟨5506982800466994626544181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7342643733955992835392241 5506982800466994626544181)
                  ·
                    refine ⟨516279637543780746238517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5506982800466994626544181 516279637543780746238517)
                    ·
                      rfl

theorem cell23_3016353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3016353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016353 prefixEnd_3016353 := by exact prefixLift 3016353
  have htrace : WordTrace (prefixWord ++ tailWord_3016353) baseStart_3016353 baseEnd_3016353 := by
    simpa [prefixWord, tailWord_3016353, baseEnd_3016353] using wordTrace_append hprefix tailTrace_3016353
  have hstable : (prefixWord ++ tailWord_3016353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016353).length < 2 ^ (prefixWord ++ tailWord_3016353).sum := by decide
  have hdescent : baseEnd_3016353 < baseStart_3016353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016383 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 3, 4]
def baseStart_3016383 : Nat := 118140960795 + 3016383 * 2 ^ 59
def prefixEnd_3016383 : Nat := 4983230072969 + 3 ^ 40 * 3016383 * 2
def baseEnd_3016383 : Nat := 516284772350325707113471

theorem tailTrace_3016383 : CollatzResearch.WordTrace tailWord_3016383 prefixEnd_3016383 516284772350325707113471 := by
  unfold tailWord_3016383
  simp only [CollatzResearch.WordTrace]
  refine ⟨110016526231167023047749803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73344350820778015365166535 110016526231167023047749803)
  ·
    refine ⟨165024789346750534571624705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110016526231167023047749803 165024789346750534571624705)
    ·
      refine ⟨123768592010062900928718529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165024789346750534571624705 123768592010062900928718529)
      ·
        refine ⟨92826444007547175696538897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123768592010062900928718529 92826444007547175696538897)
        ·
          refine ⟨69619833005660381772404173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92826444007547175696538897 69619833005660381772404173)
          ·
            refine ⟨26107437377122643164651565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69619833005660381772404173 26107437377122643164651565)
            ·
              refine ⟨9790289016420991186744337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26107437377122643164651565 9790289016420991186744337)
              ·
                refine ⟨7342716762315743390058253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9790289016420991186744337 7342716762315743390058253)
                ·
                  refine ⟨2753518785868403771271845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7342716762315743390058253 2753518785868403771271845)
                  ·
                    refine ⟨516284772350325707113471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2753518785868403771271845 516284772350325707113471)
                    ·
                      rfl

theorem cell23_3016383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_3016383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016383 prefixEnd_3016383 := by exact prefixLift 3016383
  have htrace : WordTrace (prefixWord ++ tailWord_3016383) baseStart_3016383 baseEnd_3016383 := by
    simpa [prefixWord, tailWord_3016383, baseEnd_3016383] using wordTrace_append hprefix tailTrace_3016383
  have hstable : (prefixWord ++ tailWord_3016383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016383).length < 2 ^ (prefixWord ++ tailWord_3016383).sum := by decide
  have hdescent : baseEnd_3016383 < baseStart_3016383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016416 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3016416 : Nat := 118140960795 + 3016416 * 2 ^ 59
def prefixEnd_3016416 : Nat := 4983230072969 + 3 ^ 40 * 3016416 * 2
def baseEnd_3016416 : Nat := 1548871261912575492227761

theorem tailTrace_3016416 : CollatzResearch.WordTrace tailWord_3016416 prefixEnd_3016416 1548871261912575492227761 := by
  unfold tailWord_3016416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55008864920023734841850551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73345153226698313122467401 55008864920023734841850551)
  ·
    refine ⟨82513297380035602262775827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55008864920023734841850551 82513297380035602262775827)
    ·
      refine ⟨123769946070053403394163741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82513297380035602262775827 123769946070053403394163741)
      ·
        refine ⟨46413729776270026272811403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123769946070053403394163741 46413729776270026272811403)
        ·
          refine ⟨69620594664405039409217105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46413729776270026272811403 69620594664405039409217105)
          ·
            refine ⟨52215445998303779556912829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69620594664405039409217105 52215445998303779556912829)
            ·
              refine ⟨19580792249363917333842311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52215445998303779556912829 19580792249363917333842311)
              ·
                refine ⟨29371188374045876000763467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19580792249363917333842311 29371188374045876000763467)
                ·
                  refine ⟨44056782561068814001145201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29371188374045876000763467 44056782561068814001145201)
                  ·
                    refine ⟨33042586920801610500858901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44056782561068814001145201 33042586920801610500858901)
                    ·
                      refine ⟨1548871261912575492227761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33042586920801610500858901 1548871261912575492227761)
                      ·
                        rfl

theorem cell23_3016416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3016416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016416 prefixEnd_3016416 := by exact prefixLift 3016416
  have htrace : WordTrace (prefixWord ++ tailWord_3016416) baseStart_3016416 baseEnd_3016416 := by
    simpa [prefixWord, tailWord_3016416, baseEnd_3016416] using wordTrace_append hprefix tailTrace_3016416
  have hstable : (prefixWord ++ tailWord_3016416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016416).length < 2 ^ (prefixWord ++ tailWord_3016416).sum := by decide
  have hdescent : baseEnd_3016416 < baseStart_3016416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016430 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_3016430 : Nat := 118140960795 + 3016430 * 2 ^ 59
def prefixEnd_3016430 : Nat := 4983230072969 + 3 ^ 40 * 3016430 * 2
def baseEnd_3016430 : Nat := 172097605626859826383633

theorem tailTrace_3016430 : CollatzResearch.WordTrace tailWord_3016430 prefixEnd_3016430 172097605626859826383633 := by
  unfold tailWord_3016430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752280057749593759338843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73345493641331166716473829 13752280057749593759338843)
  ·
    refine ⟨20628420086624390639008265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13752280057749593759338843 20628420086624390639008265)
    ·
      refine ⟨15471315064968292979256199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20628420086624390639008265 15471315064968292979256199)
      ·
        refine ⟨23206972597452439468884299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15471315064968292979256199 23206972597452439468884299)
        ·
          refine ⟨34810458896178659203326449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23206972597452439468884299 34810458896178659203326449)
          ·
            refine ⟨26107844172133994402494837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34810458896178659203326449 26107844172133994402494837)
            ·
              refine ⟨2447610391137561975233891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26107844172133994402494837 2447610391137561975233891)
              ·
                refine ⟨3671415586706342962850837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447610391137561975233891 3671415586706342962850837)
                ·
                  refine ⟨172097605626859826383633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3671415586706342962850837 172097605626859826383633)
                  ·
                    rfl

theorem cell23_3016430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_3016430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016430 prefixEnd_3016430 := by exact prefixLift 3016430
  have htrace : WordTrace (prefixWord ++ tailWord_3016430) baseStart_3016430 baseEnd_3016430 := by
    simpa [prefixWord, tailWord_3016430, baseEnd_3016430] using wordTrace_append hprefix tailTrace_3016430
  have hstable : (prefixWord ++ tailWord_3016430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016430).length < 2 ^ (prefixWord ++ tailWord_3016430).sum := by decide
  have hdescent : baseEnd_3016430 < baseStart_3016430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016468 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3016468 : Nat := 118140960795 + 3016468 * 2 ^ 59
def prefixEnd_3016468 : Nat := 4983230072969 + 3 ^ 40 * 3016468 * 2
def baseEnd_3016468 : Nat := 516299320968869762925841

theorem tailTrace_3016468 : CollatzResearch.WordTrace tailWord_3016468 prefixEnd_3016468 516299320968869762925841 := by
  unfold tailWord_3016468
  simp only [CollatzResearch.WordTrace]
  refine ⟨55009813217929541282297029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73346417623906055043062705 55009813217929541282297029)
  ·
    refine ⟨10314339978361788990430693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55009813217929541282297029 10314339978361788990430693)
    ·
      refine ⟨1933938745942835435705755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10314339978361788990430693 1933938745942835435705755)
      ·
        refine ⟨2900908118914253153558633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933938745942835435705755 2900908118914253153558633)
        ·
          refine ⟨2175681089185689865168975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900908118914253153558633 2175681089185689865168975)
          ·
            refine ⟨3263521633778534797753463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175681089185689865168975 3263521633778534797753463)
            ·
              refine ⟨4895282450667802196630195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263521633778534797753463 4895282450667802196630195)
              ·
                refine ⟨7342923676001703294945293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895282450667802196630195 7342923676001703294945293)
                ·
                  refine ⟨2753596378500638735604485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7342923676001703294945293 2753596378500638735604485)
                  ·
                    refine ⟨516299320968869762925841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2753596378500638735604485 516299320968869762925841)
                    ·
                      rfl

theorem cell23_3016468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3016468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016468 prefixEnd_3016468 := by exact prefixLift 3016468
  have htrace : WordTrace (prefixWord ++ tailWord_3016468) baseStart_3016468 baseEnd_3016468 := by
    simpa [prefixWord, tailWord_3016468, baseEnd_3016468] using wordTrace_append hprefix tailTrace_3016468
  have hstable : (prefixWord ++ tailWord_3016468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016468).length < 2 ^ (prefixWord ++ tailWord_3016468).sum := by decide
  have hdescent : baseEnd_3016468 < baseStart_3016468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016483 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3016483 : Nat := 118140960795 + 3016483 * 2 ^ 59
def prefixEnd_3016483 : Nat := 4983230072969 + 3 ^ 40 * 3016483 * 2
def baseEnd_3016483 : Nat := 1548905665116426730089953

theorem tailTrace_3016483 : CollatzResearch.WordTrace tailWord_3016483 prefixEnd_3016483 1548905665116426730089953 := by
  unfold tailWord_3016483
  simp only [CollatzResearch.WordTrace]
  refine ⟨110020173530804740126390103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73346782353869826750926735 110020173530804740126390103)
  ·
    refine ⟨165030260296207110189585155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110020173530804740126390103 165030260296207110189585155)
    ·
      refine ⟨247545390444310665284377733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165030260296207110189585155 247545390444310665284377733)
      ·
        refine ⟨46414760708308249740820825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247545390444310665284377733 46414760708308249740820825)
        ·
          refine ⟨34811070531231187305615619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46414760708308249740820825 34811070531231187305615619)
          ·
            refine ⟨52216605796846780958423429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34811070531231187305615619 52216605796846780958423429)
            ·
              refine ⟨9790613586908771429704393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52216605796846780958423429 9790613586908771429704393)
              ·
                refine ⟨7342960190181578572278295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9790613586908771429704393 7342960190181578572278295)
                ·
                  refine ⟨11014440285272367858417443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7342960190181578572278295 11014440285272367858417443)
                  ·
                    refine ⟨16521660427908551787626165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11014440285272367858417443 16521660427908551787626165)
                    ·
                      refine ⟨1548905665116426730089953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16521660427908551787626165 1548905665116426730089953)
                      ·
                        rfl

theorem cell23_3016483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3016483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016483 prefixEnd_3016483 := by exact prefixLift 3016483
  have htrace : WordTrace (prefixWord ++ tailWord_3016483) baseStart_3016483 baseEnd_3016483 := by
    simpa [prefixWord, tailWord_3016483, baseEnd_3016483] using wordTrace_append hprefix tailTrace_3016483
  have hstable : (prefixWord ++ tailWord_3016483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016483).length < 2 ^ (prefixWord ++ tailWord_3016483).sum := by decide
  have hdescent : baseEnd_3016483 < baseStart_3016483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016494 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3016494 : Nat := 118140960795 + 3016494 * 2 ^ 59
def prefixEnd_3016494 : Nat := 4983230072969 + 3 ^ 40 * 3016494 * 2
def baseEnd_3016494 : Nat := 516303771134542062350801

theorem tailTrace_3016494 : CollatzResearch.WordTrace tailWord_3016494 prefixEnd_3016494 516303771134542062350801 := by
  unfold tailWord_3016494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752571841720611125630067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73347049822509926003360357 13752571841720611125630067)
  ·
    refine ⟨20628857762580916688445101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13752571841720611125630067 20628857762580916688445101)
    ·
      refine ⟨7735821660967843758166913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20628857762580916688445101 7735821660967843758166913)
      ·
        refine ⟨5801866245725882818625185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7735821660967843758166913 5801866245725882818625185)
        ·
          refine ⟨4351399684294412113968889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5801866245725882818625185 4351399684294412113968889)
          ·
            refine ⟨3263549763220809085476667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351399684294412113968889 3263549763220809085476667)
            ·
              refine ⟨4895324644831213628215001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263549763220809085476667 4895324644831213628215001)
              ·
                refine ⟨3671493483623410221161251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895324644831213628215001 3671493483623410221161251)
                ·
                  refine ⟨5507240225435115331741877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671493483623410221161251 5507240225435115331741877)
                  ·
                    refine ⟨516303771134542062350801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5507240225435115331741877 516303771134542062350801)
                    ·
                      rfl

theorem cell23_3016494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3016494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016494 prefixEnd_3016494 := by exact prefixLift 3016494
  have htrace : WordTrace (prefixWord ++ tailWord_3016494) baseStart_3016494 baseEnd_3016494 := by
    simpa [prefixWord, tailWord_3016494, baseEnd_3016494] using wordTrace_append hprefix tailTrace_3016494
  have hstable : (prefixWord ++ tailWord_3016494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016494).length < 2 ^ (prefixWord ++ tailWord_3016494).sum := by decide
  have hdescent : baseEnd_3016494 < baseStart_3016494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016497 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_3016497 : Nat := 118140960795 + 3016497 * 2 ^ 59
def prefixEnd_3016497 : Nat := 4983230072969 + 3 ^ 40 * 3016497 * 2
def baseEnd_3016497 : Nat := 1548912853845589675314889

theorem tailTrace_3016497 : CollatzResearch.WordTrace tailWord_3016497 prefixEnd_3016497 1548912853845589675314889 := by
  unfold tailWord_3016497
  simp only [CollatzResearch.WordTrace]
  refine ⟨110020684152754020517399745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73347122768502680344933163 110020684152754020517399745)
  ·
    refine ⟨82515513114565515388049809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110020684152754020517399745 82515513114565515388049809)
    ·
      refine ⟨61886634835924136541037357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82515513114565515388049809 61886634835924136541037357)
      ·
        refine ⟨23207488063471551202889009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61886634835924136541037357 23207488063471551202889009)
        ·
          refine ⟨17405616047603663402166757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23207488063471551202889009 17405616047603663402166757)
          ·
            refine ⟨3263553008925686887906267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17405616047603663402166757 3263553008925686887906267)
            ·
              refine ⟨4895329513388530331859401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263553008925686887906267 4895329513388530331859401)
              ·
                refine ⟨3671497135041397748894551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895329513388530331859401 3671497135041397748894551)
                ·
                  refine ⟨5507245702562096623341827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671497135041397748894551 5507245702562096623341827)
                  ·
                    refine ⟨8260868553843144935012741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5507245702562096623341827 8260868553843144935012741)
                    ·
                      refine ⟨1548912853845589675314889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8260868553843144935012741 1548912853845589675314889)
                      ·
                        rfl

theorem cell23_3016497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_3016497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016497 prefixEnd_3016497 := by exact prefixLift 3016497
  have htrace : WordTrace (prefixWord ++ tailWord_3016497) baseStart_3016497 baseEnd_3016497 := by
    simpa [prefixWord, tailWord_3016497, baseEnd_3016497] using wordTrace_append hprefix tailTrace_3016497
  have hstable : (prefixWord ++ tailWord_3016497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016497).length < 2 ^ (prefixWord ++ tailWord_3016497).sum := by decide
  have hdescent : baseEnd_3016497 < baseStart_3016497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016510 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3016510 : Nat := 118140960795 + 3016510 * 2 ^ 59
def prefixEnd_3016510 : Nat := 4983230072969 + 3 ^ 40 * 3016510 * 2
def baseEnd_3016510 : Nat := 1548919529094098124452329

theorem tailTrace_3016510 : CollatzResearch.WordTrace tailWord_3016510 prefixEnd_3016510 1548919529094098124452329 := by
  unfold tailWord_3016510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752644787713365467202873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73347438867804615825081989 13752644787713365467202873)
  ·
    refine ⟨10314483590785024100402155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13752644787713365467202873 10314483590785024100402155)
    ·
      refine ⟨15471725386177536150603233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10314483590785024100402155 15471725386177536150603233)
      ·
        refine ⟨11603794039633152112952425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15471725386177536150603233 11603794039633152112952425)
        ·
          refine ⟨8702845529724864084714319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11603794039633152112952425 8702845529724864084714319)
          ·
            refine ⟨13054268294587296127071479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8702845529724864084714319 13054268294587296127071479)
            ·
              refine ⟨19581402441880944190607219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13054268294587296127071479 19581402441880944190607219)
              ·
                refine ⟨29372103662821416285910829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19581402441880944190607219 29372103662821416285910829)
                ·
                  refine ⟨11014538873558031107216561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29372103662821416285910829 11014538873558031107216561)
                  ·
                    refine ⟨8260904155168523330412421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11014538873558031107216561 8260904155168523330412421)
                    ·
                      refine ⟨1548919529094098124452329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8260904155168523330412421 1548919529094098124452329)
                      ·
                        rfl

theorem cell23_3016510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3016510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016510 prefixEnd_3016510 := by exact prefixLift 3016510
  have htrace : WordTrace (prefixWord ++ tailWord_3016510) baseStart_3016510 baseEnd_3016510 := by
    simpa [prefixWord, tailWord_3016510, baseEnd_3016510] using wordTrace_append hprefix tailTrace_3016510
  have hstable : (prefixWord ++ tailWord_3016510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016510).length < 2 ^ (prefixWord ++ tailWord_3016510).sum := by decide
  have hdescent : baseEnd_3016510 < baseStart_3016510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016517 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 1, 2, 3]
def baseStart_3016517 : Nat := 118140960795 + 3016517 * 2 ^ 59
def prefixEnd_3016517 : Nat := 4983230072969 + 3 ^ 40 * 3016517 * 2
def baseEnd_3016517 : Nat := 1548923123458679597064797

theorem tailTrace_3016517 : CollatzResearch.WordTrace tailWord_3016517 prefixEnd_3016517 1548923123458679597064797 := by
  unfold tailWord_3016517
  simp only [CollatzResearch.WordTrace]
  refine ⟨110021413612681563933127805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73347609075121042622085203 110021413612681563933127805)
  ·
    refine ⟨41258030104755586474922927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110021413612681563933127805 41258030104755586474922927)
    ·
      refine ⟨61887045157133379712384391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41258030104755586474922927 61887045157133379712384391)
      ·
        refine ⟨92830567735700069568576587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61887045157133379712384391 92830567735700069568576587)
        ·
          refine ⟨139245851603550104352864881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92830567735700069568576587 139245851603550104352864881)
          ·
            refine ⟨104434388702662578264648661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139245851603550104352864881 104434388702662578264648661)
            ·
              refine ⟨2447680985218654178077703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 104434388702662578264648661 2447680985218654178077703)
              ·
                refine ⟨3671521477827981267116555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447680985218654178077703 3671521477827981267116555)
                ·
                  refine ⟨5507282216741971900674833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671521477827981267116555 5507282216741971900674833)
                  ·
                    refine ⟨4130461662556478925506125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5507282216741971900674833 4130461662556478925506125)
                    ·
                      refine ⟨1548923123458679597064797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130461662556478925506125 1548923123458679597064797)
                      ·
                        rfl

theorem cell23_3016517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_3016517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016517 prefixEnd_3016517 := by exact prefixLift 3016517
  have htrace : WordTrace (prefixWord ++ tailWord_3016517) baseStart_3016517 baseEnd_3016517 := by
    simpa [prefixWord, tailWord_3016517, baseEnd_3016517] using wordTrace_append hprefix tailTrace_3016517
  have hstable : (prefixWord ++ tailWord_3016517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016517).length < 2 ^ (prefixWord ++ tailWord_3016517).sum := by decide
  have hdescent : baseEnd_3016517 < baseStart_3016517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016533 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_3016533 : Nat := 118140960795 + 3016533 * 2 ^ 59
def prefixEnd_3016533 : Nat := 4983230072969 + 3 ^ 40 * 3016533 * 2
def baseEnd_3016533 : Nat := 516310446383050511488241

theorem tailTrace_3016533 : CollatzResearch.WordTrace tailWord_3016533 prefixEnd_3016533 516310446383050511488241 := by
  unfold tailWord_3016533
  simp only [CollatzResearch.WordTrace]
  refine ⟨110021997180623598665710253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73347998120415732443806835 110021997180623598665710253)
  ·
    refine ⟨41258248942733849499641345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110021997180623598665710253 41258248942733849499641345)
    ·
      refine ⟨30943686707050387124731009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41258248942733849499641345 30943686707050387124731009)
      ·
        refine ⟨23207765030287790343548257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30943686707050387124731009 23207765030287790343548257)
        ·
          refine ⟨17405823772715842757661193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23207765030287790343548257 17405823772715842757661193)
          ·
            refine ⟨13054367829536882068245895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17405823772715842757661193 13054367829536882068245895)
            ·
              refine ⟨19581551744305323102368843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13054367829536882068245895 19581551744305323102368843)
              ·
                refine ⟨29372327616457984653553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19581551744305323102368843 29372327616457984653553265)
                ·
                  refine ⟨22029245712343488490164949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29372327616457984653553265 22029245712343488490164949)
                  ·
                    refine ⟨516310446383050511488241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22029245712343488490164949 516310446383050511488241)
                    ·
                      rfl

theorem cell23_3016533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_3016533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016533 prefixEnd_3016533 := by exact prefixLift 3016533
  have htrace : WordTrace (prefixWord ++ tailWord_3016533) baseStart_3016533 baseEnd_3016533 := by
    simpa [prefixWord, tailWord_3016533, baseEnd_3016533] using wordTrace_append hprefix tailTrace_3016533
  have hstable : (prefixWord ++ tailWord_3016533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016533).length < 2 ^ (prefixWord ++ tailWord_3016533).sum := by decide
  have hdescent : baseEnd_3016533 < baseStart_3016533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016547 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 3]
def baseStart_3016547 : Nat := 118140960795 + 3016547 * 2 ^ 59
def prefixEnd_3016547 : Nat := 4983230072969 + 3 ^ 40 * 3016547 * 2
def baseEnd_3016547 : Nat := 1548938527878314479689659

theorem tailTrace_3016547 : CollatzResearch.WordTrace tailWord_3016547 prefixEnd_3016547 1548938527878314479689659 := by
  unfold tailWord_3016547
  simp only [CollatzResearch.WordTrace]
  refine ⟨110022507802572879056719895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73348338535048586037813263 110022507802572879056719895)
  ·
    refine ⟨165033761703859318585079843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110022507802572879056719895 165033761703859318585079843)
    ·
      refine ⟨247550642555788977877619765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165033761703859318585079843 247550642555788977877619765)
      ·
        refine ⟨23207872739605216676026853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247550642555788977877619765 23207872739605216676026853)
        ·
          refine ⟨4351476138675978126755035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23207872739605216676026853 4351476138675978126755035)
          ·
            refine ⟨6527214208013967190132553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351476138675978126755035 6527214208013967190132553)
            ·
              refine ⟨4895410656010475392599415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6527214208013967190132553 4895410656010475392599415)
              ·
                refine ⟨7343115984015713088899123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895410656010475392599415 7343115984015713088899123)
                ·
                  refine ⟨11014673976023569633348685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343115984015713088899123 11014673976023569633348685)
                  ·
                    refine ⟨4130502741008838612505757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11014673976023569633348685 4130502741008838612505757)
                    ·
                      refine ⟨1548938527878314479689659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130502741008838612505757 1548938527878314479689659)
                      ·
                        rfl

theorem cell23_3016547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_3016547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016547 prefixEnd_3016547 := by exact prefixLift 3016547
  have htrace : WordTrace (prefixWord ++ tailWord_3016547) baseStart_3016547 baseEnd_3016547 := by
    simpa [prefixWord, tailWord_3016547, baseEnd_3016547] using wordTrace_append hprefix tailTrace_3016547
  have hstable : (prefixWord ++ tailWord_3016547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016547).length < 2 ^ (prefixWord ++ tailWord_3016547).sum := by decide
  have hdescent : baseEnd_3016547 < baseStart_3016547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016557 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3016557 : Nat := 118140960795 + 3016557 * 2 ^ 59
def prefixEnd_3016557 : Nat := 4983230072969 + 3 ^ 40 * 3016557 * 2
def baseEnd_3016557 : Nat := 1548943662684859440564613

theorem tailTrace_3016557 : CollatzResearch.WordTrace tailWord_3016557 prefixEnd_3016557 1548943662684859440564613 := by
  unfold tailWord_3016557
  simp only [CollatzResearch.WordTrace]
  refine ⟨110022872532536650764583925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73348581688357767176389283 110022872532536650764583925)
  ·
    refine ⟨10314644299925311009179743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110022872532536650764583925 10314644299925311009179743)
    ·
      refine ⟨15471966449887966513769615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10314644299925311009179743 15471966449887966513769615)
      ·
        refine ⟨23207949674831949770654423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15471966449887966513769615 23207949674831949770654423)
        ·
          refine ⟨34811924512247924655981635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23207949674831949770654423 34811924512247924655981635)
          ·
            refine ⟨52217886768371886983972453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34811924512247924655981635 52217886768371886983972453)
            ·
              refine ⟨9790853769069728809494835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52217886768371886983972453 9790853769069728809494835)
              ·
                refine ⟨14686280653604593214242253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9790853769069728809494835 14686280653604593214242253)
                ·
                  refine ⟨5507355245101722455340845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14686280653604593214242253 5507355245101722455340845)
                  ·
                    refine ⟨2065258216913145920752817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5507355245101722455340845 2065258216913145920752817)
                    ·
                      refine ⟨1548943662684859440564613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065258216913145920752817 1548943662684859440564613)
                      ·
                        rfl

theorem cell23_3016557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3016557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016557 prefixEnd_3016557 := by exact prefixLift 3016557
  have htrace : WordTrace (prefixWord ++ tailWord_3016557) baseStart_3016557 baseEnd_3016557 := by
    simpa [prefixWord, tailWord_3016557, baseEnd_3016557] using wordTrace_append hprefix tailTrace_3016557
  have hstable : (prefixWord ++ tailWord_3016557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016557).length < 2 ^ (prefixWord ++ tailWord_3016557).sum := by decide
  have hdescent : baseEnd_3016557 < baseStart_3016557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016573 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3016573 : Nat := 118140960795 + 3016573 * 2 ^ 59
def prefixEnd_3016573 : Nat := 4983230072969 + 3 ^ 40 * 3016573 * 2
def baseEnd_3016573 : Nat := 1548951878375331377964539

theorem tailTrace_3016573 : CollatzResearch.WordTrace tailWord_3016573 prefixEnd_3016573 1548951878375331377964539 := by
  unfold tailWord_3016573
  simp only [CollatzResearch.WordTrace]
  refine ⟨110023456100478685497166373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73348970733652456998110915 110023456100478685497166373)
  ·
    refine ⟨20629398018839753530718695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110023456100478685497166373 20629398018839753530718695)
    ·
      refine ⟨30944097028259630296078043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20629398018839753530718695 30944097028259630296078043)
      ·
        refine ⟨46416145542389445444117065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30944097028259630296078043 46416145542389445444117065)
        ·
          refine ⟨34812109156792084083087799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46416145542389445444117065 34812109156792084083087799)
          ·
            refine ⟨52218163735188126124631699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34812109156792084083087799 52218163735188126124631699)
            ·
              refine ⟨78327245602782189186947549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52218163735188126124631699 78327245602782189186947549)
              ·
                refine ⟨29372717101043320945105331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78327245602782189186947549 29372717101043320945105331)
                ·
                  refine ⟨44059075651564981417657997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29372717101043320945105331 44059075651564981417657997)
                  ·
                    refine ⟨16522153369336868031621749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44059075651564981417657997 16522153369336868031621749)
                    ·
                      refine ⟨1548951878375331377964539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16522153369336868031621749 1548951878375331377964539)
                      ·
                        rfl

theorem cell23_3016573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3016573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016573 prefixEnd_3016573 := by exact prefixLift 3016573
  have htrace : WordTrace (prefixWord ++ tailWord_3016573) baseStart_3016573 baseEnd_3016573 := by
    simpa [prefixWord, tailWord_3016573, baseEnd_3016573] using wordTrace_append hprefix tailTrace_3016573
  have hstable : (prefixWord ++ tailWord_3016573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016573).length < 2 ^ (prefixWord ++ tailWord_3016573).sum := by decide
  have hdescent : baseEnd_3016573 < baseStart_3016573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
